// trust-binary-parse: DWARF line number programs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::cursor::Cursor;
use crate::dwarf::constants::{
    DW_FORM_DATA1, DW_FORM_DATA2, DW_FORM_DATA4, DW_FORM_DATA8, DW_FORM_LINE_STRP, DW_FORM_STRING,
    DW_FORM_STRP, DW_FORM_UDATA,
};
use crate::error::DwarfError;

const DW_LNS_COPY: u8 = 1;
const DW_LNS_ADVANCE_PC: u8 = 2;
const DW_LNS_ADVANCE_LINE: u8 = 3;
const DW_LNS_SET_FILE: u8 = 4;
const DW_LNS_SET_COLUMN: u8 = 5;
const DW_LNS_NEGATE_STMT: u8 = 6;
const DW_LNS_SET_BASIC_BLOCK: u8 = 7;
const DW_LNS_CONST_ADD_PC: u8 = 8;
const DW_LNS_FIXED_ADVANCE_PC: u8 = 9;
const DW_LNS_SET_PROLOGUE_END: u8 = 10;
const DW_LNS_SET_EPILOGUE_BEGIN: u8 = 11;

const DW_LNE_END_SEQUENCE: u8 = 1;
const DW_LNE_SET_ADDRESS: u8 = 2;
const DW_LNE_DEFINE_FILE: u8 = 3;

const DW_LNCT_PATH: u64 = 0x01;
const DW_LNCT_DIRECTORY_INDEX: u64 = 0x02;
const DW_LNCT_TIMESTAMP: u64 = 0x03;
const DW_LNCT_SIZE: u64 = 0x04;
const DW_LNCT_MD5: u64 = 0x05;
const DW_FORM_DATA16: u64 = 0x1e;

/// The decoded line program header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineProgramHeader {
    pub(crate) minimum_instruction_length: u8,
    pub(crate) maximum_operations_per_instruction: u8,
    pub(crate) default_is_stmt: bool,
    pub(crate) line_base: i8,
    pub(crate) line_range: u8,
    pub(crate) opcode_base: u8,
    pub(crate) standard_opcode_lengths: Vec<u8>,
    pub(crate) include_directories: Vec<String>,
    pub(crate) file_names: Vec<FileEntry>,
}

/// A file table entry from the line program header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileEntry {
    pub(crate) name: String,
    pub(crate) directory_index: u64,
    pub(crate) last_modified: u64,
    pub(crate) size: u64,
}

/// A single emitted row from the line table state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineRow {
    pub(crate) address: u64,
    pub(crate) file: usize,
    pub(crate) line: u64,
    pub(crate) column: u64,
    pub(crate) is_stmt: bool,
    pub(crate) basic_block: bool,
    pub(crate) end_sequence: bool,
    pub(crate) prologue_end: bool,
    pub(crate) epilogue_begin: bool,
}

struct ParsedHeader {
    header: LineProgramHeader,
    version: u16,
    offset_size: usize,
    address_size: usize,
    segment_selector_size: usize,
    file_entry_formats: Vec<(u64, u64)>,
    program_end: usize,
}

#[derive(Debug, Clone)]
struct LineState {
    address: u64,
    op_index: u64,
    file: usize,
    line: u64,
    column: u64,
    is_stmt: bool,
    basic_block: bool,
    end_sequence: bool,
    prologue_end: bool,
    epilogue_begin: bool,
}

/// Parse a line number program contribution from `.debug_line`.
#[cfg(test)]
pub fn parse_line_program(data: &[u8]) -> Result<(LineProgramHeader, Vec<LineRow>), DwarfError> {
    parse_line_program_with_size(data).map(|(program, _)| program)
}

pub fn parse_line_program_with_size(
    data: &[u8],
) -> Result<((LineProgramHeader, Vec<LineRow>), usize), DwarfError> {
    let mut cursor = Cursor::new(data);
    let mut parsed = parse_header(&mut cursor)?;
    let mut rows = Vec::new();
    let mut state = LineState::new(parsed.header.default_is_stmt);

    while cursor.position() < parsed.program_end {
        let opcode = cursor.read_u8()?;
        if opcode == 0 {
            let extended_length = usize::try_from(cursor.read_uleb128()?)
                .map_err(|_| DwarfError::InvalidLineProgram)?;
            if extended_length == 0 {
                return Err(DwarfError::InvalidLineProgram);
            }
            let payload = cursor.read_bytes(extended_length)?;
            execute_extended_opcode(payload, &mut parsed, &mut state, &mut rows)?;
            continue;
        }

        if opcode < parsed.header.opcode_base {
            execute_standard_opcode(opcode, &mut cursor, &parsed, &mut state, &mut rows)?;
            continue;
        }

        execute_special_opcode(opcode, &parsed, &mut state, &mut rows)?;
    }

    Ok(((parsed.header, rows), parsed.program_end))
}

fn parse_header(cursor: &mut Cursor<'_>) -> Result<ParsedHeader, DwarfError> {
    let initial_length = cursor.read_u32_le()?;
    let (unit_length, offset_size) = if initial_length == u32::MAX {
        (cursor.read_u64_le()?, 8)
    } else {
        (u64::from(initial_length), 4)
    };
    let unit_length = usize::try_from(unit_length).map_err(|_| DwarfError::InvalidLineProgram)?;
    let program_end =
        cursor.position().checked_add(unit_length).ok_or(DwarfError::InvalidLineProgram)?;
    if program_end > cursor.len() {
        return Err(DwarfError::UnexpectedEof { offset: cursor.position() });
    }

    let version = cursor.read_u16_le()?;
    if !(2..=5).contains(&version) {
        return Err(DwarfError::UnsupportedDwarfVersion(version));
    }

    let (address_size, segment_selector_size, header_length) = if version == 5 {
        let address_size = usize::from(cursor.read_u8()?);
        let segment_selector_size = usize::from(cursor.read_u8()?);
        let header_length = read_offset(cursor, offset_size)?;
        (address_size, segment_selector_size, header_length)
    } else {
        let header_length = read_offset(cursor, offset_size)?;
        (0, 0, header_length)
    };

    let header_length =
        usize::try_from(header_length).map_err(|_| DwarfError::InvalidLineProgram)?;
    let header_end =
        cursor.position().checked_add(header_length).ok_or(DwarfError::InvalidLineProgram)?;
    if header_end > program_end {
        return Err(DwarfError::InvalidLineProgram);
    }

    let minimum_instruction_length = cursor.read_u8()?;
    let maximum_operations_per_instruction = if version >= 4 { cursor.read_u8()? } else { 1 };
    let default_is_stmt = cursor.read_u8()? != 0;
    let line_base = cursor.read_u8()? as i8;
    let line_range = cursor.read_u8()?;
    let opcode_base = cursor.read_u8()?;
    if opcode_base == 0 || line_range == 0 {
        return Err(DwarfError::InvalidLineProgram);
    }

    let standard_opcode_lengths = (0..usize::from(opcode_base.saturating_sub(1)))
        .map(|_| cursor.read_u8())
        .collect::<Result<Vec<_>, _>>()?;

    let (include_directories, file_names, file_entry_formats) = if version == 5 {
        let directory_formats = parse_entry_formats(cursor)?;
        let include_directories = parse_directories_v5(cursor, &directory_formats, offset_size)?;
        let file_entry_formats = parse_entry_formats(cursor)?;
        let file_names = parse_files_v5(cursor, &file_entry_formats, offset_size)?;
        (include_directories, file_names, file_entry_formats)
    } else {
        let include_directories = parse_directories_legacy(cursor)?;
        let file_names = parse_files_legacy(cursor)?;
        (include_directories, file_names, Vec::new())
    };

    if cursor.position() != header_end {
        if cursor.position() > header_end {
            return Err(DwarfError::InvalidLineProgram);
        }
        if !cursor.read_bytes(header_end - cursor.position())?.iter().all(|byte| *byte == 0) {
            return Err(DwarfError::InvalidLineProgram);
        }
    }

    Ok(ParsedHeader {
        header: LineProgramHeader {
            minimum_instruction_length,
            maximum_operations_per_instruction,
            default_is_stmt,
            line_base,
            line_range,
            opcode_base,
            standard_opcode_lengths,
            include_directories,
            file_names,
        },
        version,
        offset_size,
        address_size,
        segment_selector_size,
        file_entry_formats,
        program_end,
    })
}

fn parse_directories_legacy(cursor: &mut Cursor<'_>) -> Result<Vec<String>, DwarfError> {
    let mut directories = Vec::new();
    loop {
        let directory = cursor.read_null_terminated_string()?;
        if directory.is_empty() {
            break;
        }
        directories.push(directory.to_string());
    }
    Ok(directories)
}

fn parse_files_legacy(cursor: &mut Cursor<'_>) -> Result<Vec<FileEntry>, DwarfError> {
    let mut files = Vec::new();
    loop {
        let name = cursor.read_null_terminated_string()?;
        if name.is_empty() {
            break;
        }
        files.push(FileEntry {
            name: name.to_string(),
            directory_index: cursor.read_uleb128()?,
            last_modified: cursor.read_uleb128()?,
            size: cursor.read_uleb128()?,
        });
    }
    Ok(files)
}

fn parse_entry_formats(cursor: &mut Cursor<'_>) -> Result<Vec<(u64, u64)>, DwarfError> {
    let count = usize::from(cursor.read_u8()?);
    (0..count).map(|_| Ok((cursor.read_uleb128()?, cursor.read_uleb128()?))).collect()
}

fn parse_directories_v5(
    cursor: &mut Cursor<'_>,
    formats: &[(u64, u64)],
    offset_size: usize,
) -> Result<Vec<String>, DwarfError> {
    let count =
        usize::try_from(cursor.read_uleb128()?).map_err(|_| DwarfError::InvalidLineProgram)?;
    let mut directories = Vec::with_capacity(count);

    for _ in 0..count {
        let mut path = String::new();
        for (content_type, form) in formats {
            match *content_type {
                DW_LNCT_PATH => path = read_header_path(cursor, *form, offset_size)?,
                _ => skip_header_field(cursor, *form, offset_size)?,
            }
        }
        directories.push(path);
    }

    Ok(directories)
}

fn parse_files_v5(
    cursor: &mut Cursor<'_>,
    formats: &[(u64, u64)],
    offset_size: usize,
) -> Result<Vec<FileEntry>, DwarfError> {
    let count =
        usize::try_from(cursor.read_uleb128()?).map_err(|_| DwarfError::InvalidLineProgram)?;
    let mut files = Vec::with_capacity(count);

    for _ in 0..count {
        files.push(parse_file_entry_v5(cursor, formats, offset_size)?);
    }

    Ok(files)
}

fn parse_file_entry_v5(
    cursor: &mut Cursor<'_>,
    formats: &[(u64, u64)],
    offset_size: usize,
) -> Result<FileEntry, DwarfError> {
    let mut entry =
        FileEntry { name: String::new(), directory_index: 0, last_modified: 0, size: 0 };

    for (content_type, form) in formats {
        match *content_type {
            DW_LNCT_PATH => entry.name = read_header_path(cursor, *form, offset_size)?,
            DW_LNCT_DIRECTORY_INDEX => {
                entry.directory_index = read_header_number(cursor, *form, offset_size)?
            }
            DW_LNCT_TIMESTAMP => {
                entry.last_modified = read_header_number(cursor, *form, offset_size)?
            }
            DW_LNCT_SIZE => entry.size = read_header_number(cursor, *form, offset_size)?,
            DW_LNCT_MD5 => skip_header_field(cursor, *form, offset_size)?,
            _ => skip_header_field(cursor, *form, offset_size)?,
        }
    }

    Ok(entry)
}

fn read_header_path(
    cursor: &mut Cursor<'_>,
    form: u64,
    offset_size: usize,
) -> Result<String, DwarfError> {
    match form {
        DW_FORM_STRING => Ok(cursor.read_null_terminated_string()?.to_string()),
        DW_FORM_LINE_STRP | DW_FORM_STRP => {
            let offset = read_offset(cursor, offset_size)?;
            Ok(format!("<strp:{offset}>"))
        }
        DW_FORM_DATA1 | DW_FORM_DATA2 | DW_FORM_DATA4 | DW_FORM_DATA8 | DW_FORM_UDATA => {
            let value = read_header_number(cursor, form, offset_size)?;
            Ok(format!("<path:{value}>"))
        }
        _ => Err(DwarfError::InvalidLineProgram),
    }
}

fn read_header_number(
    cursor: &mut Cursor<'_>,
    form: u64,
    offset_size: usize,
) -> Result<u64, DwarfError> {
    match form {
        DW_FORM_DATA1 => Ok(u64::from(cursor.read_u8()?)),
        DW_FORM_DATA2 => Ok(u64::from(cursor.read_u16_le()?)),
        DW_FORM_DATA4 => Ok(u64::from(cursor.read_u32_le()?)),
        DW_FORM_DATA8 => cursor.read_u64_le(),
        DW_FORM_UDATA => cursor.read_uleb128(),
        DW_FORM_LINE_STRP | DW_FORM_STRP => read_offset(cursor, offset_size),
        _ => Err(DwarfError::InvalidLineProgram),
    }
}

fn skip_header_field(
    cursor: &mut Cursor<'_>,
    form: u64,
    offset_size: usize,
) -> Result<(), DwarfError> {
    match form {
        DW_FORM_STRING => {
            let _ = cursor.read_null_terminated_string()?;
        }
        DW_FORM_DATA1 => {
            let _ = cursor.read_u8()?;
        }
        DW_FORM_DATA2 => {
            let _ = cursor.read_u16_le()?;
        }
        DW_FORM_DATA4 => {
            let _ = cursor.read_u32_le()?;
        }
        DW_FORM_DATA8 => {
            let _ = cursor.read_u64_le()?;
        }
        DW_FORM_UDATA => {
            let _ = cursor.read_uleb128()?;
        }
        DW_FORM_LINE_STRP | DW_FORM_STRP => {
            let _ = read_offset(cursor, offset_size)?;
        }
        DW_FORM_DATA16 => {
            let _ = cursor.read_bytes(16)?;
        }
        _ => return Err(DwarfError::InvalidLineProgram),
    }
    Ok(())
}

fn execute_standard_opcode(
    opcode: u8,
    cursor: &mut Cursor<'_>,
    parsed: &ParsedHeader,
    state: &mut LineState,
    rows: &mut Vec<LineRow>,
) -> Result<(), DwarfError> {
    match opcode {
        DW_LNS_COPY => {
            rows.push(state.to_row());
            state.clear_transient_flags();
        }
        DW_LNS_ADVANCE_PC => {
            let advance = cursor.read_uleb128()?;
            advance_address(state, &parsed.header, advance)?;
        }
        DW_LNS_ADVANCE_LINE => {
            let delta = cursor.read_sleb128()?;
            advance_line(state, delta)?;
        }
        DW_LNS_SET_FILE => {
            state.file = usize::try_from(cursor.read_uleb128()?)
                .map_err(|_| DwarfError::InvalidLineProgram)?;
        }
        DW_LNS_SET_COLUMN => {
            state.column = cursor.read_uleb128()?;
        }
        DW_LNS_NEGATE_STMT => {
            state.is_stmt = !state.is_stmt;
        }
        DW_LNS_SET_BASIC_BLOCK => {
            state.basic_block = true;
        }
        DW_LNS_CONST_ADD_PC => {
            let adjusted = u64::from(u8::MAX - parsed.header.opcode_base);
            let advance = adjusted / u64::from(parsed.header.line_range);
            advance_address(state, &parsed.header, advance)?;
        }
        DW_LNS_FIXED_ADVANCE_PC => {
            state.address = state
                .address
                .checked_add(u64::from(cursor.read_u16_le()?))
                .ok_or(DwarfError::InvalidLineProgram)?;
            state.op_index = 0;
        }
        DW_LNS_SET_PROLOGUE_END => {
            state.prologue_end = true;
        }
        DW_LNS_SET_EPILOGUE_BEGIN => {
            state.epilogue_begin = true;
        }
        _ => {
            let operand_count = parsed
                .header
                .standard_opcode_lengths
                .get(usize::from(opcode.saturating_sub(1)))
                .copied()
                .ok_or(DwarfError::InvalidLineProgram)?;
            for _ in 0..operand_count {
                let _ = cursor.read_uleb128()?;
            }
        }
    }

    Ok(())
}

fn execute_special_opcode(
    opcode: u8,
    parsed: &ParsedHeader,
    state: &mut LineState,
    rows: &mut Vec<LineRow>,
) -> Result<(), DwarfError> {
    let adjusted = u64::from(opcode - parsed.header.opcode_base);
    let operation_advance = adjusted / u64::from(parsed.header.line_range);
    let line_increment = i64::from(parsed.header.line_base)
        + i64::try_from(adjusted % u64::from(parsed.header.line_range))
            .expect("invariant: modulo of u8 range always fits in i64");

    advance_address(state, &parsed.header, operation_advance)?;
    advance_line(state, line_increment)?;
    rows.push(state.to_row());
    state.clear_transient_flags();
    Ok(())
}

fn execute_extended_opcode(
    payload: &[u8],
    parsed: &mut ParsedHeader,
    state: &mut LineState,
    rows: &mut Vec<LineRow>,
) -> Result<(), DwarfError> {
    let mut cursor = Cursor::new(payload);
    let opcode = cursor.read_u8()?;

    match opcode {
        DW_LNE_END_SEQUENCE => {
            state.end_sequence = true;
            rows.push(state.to_row());
            *state = LineState::new(parsed.header.default_is_stmt);
        }
        DW_LNE_SET_ADDRESS => {
            let remaining = cursor.remaining();
            if parsed.version == 5
                && parsed.segment_selector_size > 0
                && remaining == parsed.segment_selector_size + parsed.address_size
            {
                let _ = cursor.read_bytes(parsed.segment_selector_size)?;
                state.address = cursor.read_uint(parsed.address_size)?;
            } else {
                state.address = cursor.read_uint(remaining)?;
            }
            state.op_index = 0;
        }
        DW_LNE_DEFINE_FILE => {
            let file = if parsed.version == 5 && !parsed.file_entry_formats.is_empty() {
                parse_file_entry_v5(&mut cursor, &parsed.file_entry_formats, parsed.offset_size)?
            } else {
                FileEntry {
                    name: cursor.read_null_terminated_string()?.to_string(),
                    directory_index: cursor.read_uleb128()?,
                    last_modified: cursor.read_uleb128()?,
                    size: cursor.read_uleb128()?,
                }
            };
            parsed.header.file_names.push(file);
        }
        _ => return Err(DwarfError::InvalidLineProgram),
    }

    if !cursor.is_empty() {
        return Err(DwarfError::InvalidLineProgram);
    }

    Ok(())
}

fn advance_address(
    state: &mut LineState,
    header: &LineProgramHeader,
    operation_advance: u64,
) -> Result<(), DwarfError> {
    let max_ops = u64::from(header.maximum_operations_per_instruction.max(1));
    let min_instruction_length = u64::from(header.minimum_instruction_length);
    let total_operations =
        state.op_index.checked_add(operation_advance).ok_or(DwarfError::InvalidLineProgram)?;
    let address_advance = min_instruction_length
        .checked_mul(total_operations / max_ops)
        .ok_or(DwarfError::InvalidLineProgram)?;

    state.address =
        state.address.checked_add(address_advance).ok_or(DwarfError::InvalidLineProgram)?;
    state.op_index = total_operations % max_ops;
    Ok(())
}

fn advance_line(state: &mut LineState, delta: i64) -> Result<(), DwarfError> {
    let next_line = i128::from(state.line) + i128::from(delta);
    if !(0..=i128::from(u64::MAX)).contains(&next_line) {
        return Err(DwarfError::InvalidLineProgram);
    }
    state.line = next_line as u64;
    Ok(())
}

fn read_offset(cursor: &mut Cursor<'_>, width: usize) -> Result<u64, DwarfError> {
    cursor.read_uint(width)
}

impl LineState {
    fn new(default_is_stmt: bool) -> Self {
        Self {
            address: 0,
            op_index: 0,
            file: 1,
            line: 1,
            column: 0,
            is_stmt: default_is_stmt,
            basic_block: false,
            end_sequence: false,
            prologue_end: false,
            epilogue_begin: false,
        }
    }

    fn to_row(&self) -> LineRow {
        LineRow {
            address: self.address,
            file: self.file,
            line: self.line,
            column: self.column,
            is_stmt: self.is_stmt,
            basic_block: self.basic_block,
            end_sequence: self.end_sequence,
            prologue_end: self.prologue_end,
            epilogue_begin: self.epilogue_begin,
        }
    }

    fn clear_transient_flags(&mut self) {
        self.basic_block = false;
        self.end_sequence = false;
        self.prologue_end = false;
        self.epilogue_begin = false;
    }
}

#[cfg(test)]
mod tests {
    use super::{FileEntry, parse_line_program};

    fn encode_uleb128(mut value: u64) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            bytes.push(byte);
            if value == 0 {
                break;
            }
        }
        bytes
    }

    fn encode_sleb128(mut value: i64) -> Vec<u8> {
        let mut bytes = Vec::new();
        loop {
            let byte = (value & 0x7f) as u8;
            let sign_bit_set = byte & 0x40 != 0;
            value >>= 7;
            let done = (value == 0 && !sign_bit_set) || (value == -1 && sign_bit_set);
            bytes.push(if done { byte } else { byte | 0x80 });
            if done {
                break;
            }
        }
        bytes
    }

    fn patch_u32_le(bytes: &mut [u8], offset: usize, value: u32) {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }

    #[test]
    fn test_line_program_special_standard_extended_opcodes_parse_expected() {
        let mut bytes = vec![0; 4];
        bytes.extend(4_u16.to_le_bytes());
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes());

        let header_start = bytes.len();
        bytes.push(1);
        bytes.push(1);
        bytes.push(1);
        bytes.push((-5_i8) as u8);
        bytes.push(14);
        bytes.push(12);
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0]);
        bytes.extend(b"src\0");
        bytes.push(0);
        bytes.extend(b"main.rs\0");
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(0));
        bytes.extend(encode_uleb128(0));
        bytes.push(0);

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        bytes.push(0);
        bytes.extend(encode_uleb128(9));
        bytes.push(2);
        bytes.extend(0x1000_u64.to_le_bytes());

        bytes.push(5);
        bytes.extend(encode_uleb128(2));
        bytes.push(1);
        bytes.push(3);
        bytes.extend(encode_sleb128(2));
        bytes.push(74);
        bytes.push(10);
        bytes.push(2);
        bytes.extend(encode_uleb128(3));
        bytes.push(1);

        bytes.push(0);
        bytes.extend(encode_uleb128(17));
        bytes.push(3);
        bytes.extend(b"generated.rs\0");
        bytes.extend(encode_uleb128(1));
        bytes.extend(encode_uleb128(0));
        bytes.extend(encode_uleb128(0));

        bytes.push(3);
        bytes.extend(encode_sleb128(-1));
        bytes.push(4);
        bytes.extend(encode_uleb128(2));
        bytes.push(1);

        bytes.push(0);
        bytes.extend(encode_uleb128(1));
        bytes.push(1);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let (header, rows) = parse_line_program(&bytes).unwrap();
        assert_eq!(header.include_directories, vec!["src".to_string()]);
        assert_eq!(
            header.file_names[0],
            FileEntry {
                name: "main.rs".to_string(),
                directory_index: 1,
                last_modified: 0,
                size: 0,
            }
        );
        assert_eq!(header.file_names[1].name, "generated.rs");

        assert_eq!(rows.len(), 5);
        assert_eq!(rows[0].address, 0x1000);
        assert_eq!(rows[0].line, 1);
        assert_eq!(rows[0].column, 2);
        assert_eq!(rows[1].address, 0x1004);
        assert_eq!(rows[1].line, 4);
        assert_eq!(rows[2].address, 0x1007);
        assert!(rows[2].prologue_end);
        assert_eq!(rows[3].file, 2);
        assert_eq!(rows[3].line, 3);
        assert!(!rows[3].end_sequence);
        assert!(rows[4].end_sequence);
    }

    /// Build a minimal DWARF v4 line program with just an end_sequence.
    fn build_minimal_line_program() -> Vec<u8> {
        let mut bytes = vec![0; 4]; // unit_length placeholder
        bytes.extend(4_u16.to_le_bytes()); // version
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes()); // header_length placeholder

        let header_start = bytes.len();
        bytes.push(1); // minimum_instruction_length
        bytes.push(1); // maximum_operations_per_instruction
        bytes.push(1); // default_is_stmt
        bytes.push((-5_i8) as u8); // line_base
        bytes.push(14); // line_range
        bytes.push(13); // opcode_base
        // standard_opcode_lengths for opcodes 1..12
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
        bytes.push(0); // end of include directories
        bytes.push(0); // end of file names

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        // Program body: just DW_LNE_end_sequence
        bytes.push(0); // extended opcode marker
        bytes.extend(encode_uleb128(1)); // length of payload
        bytes.push(1); // DW_LNE_end_sequence

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        bytes
    }

    #[test]
    fn test_line_program_minimal_only_end_sequence() {
        let bytes = build_minimal_line_program();
        let (header, rows) = parse_line_program(&bytes).unwrap();
        assert!(header.include_directories.is_empty());
        assert!(header.file_names.is_empty());
        assert_eq!(rows.len(), 1);
        assert!(rows[0].end_sequence);
        assert_eq!(rows[0].address, 0);
        assert_eq!(rows[0].line, 1); // default initial line
    }

    #[test]
    fn test_line_program_empty_data_returns_error() {
        let err = parse_line_program(&[]);
        assert!(err.is_err());
    }

    #[test]
    fn test_line_program_truncated_header_returns_error() {
        // Just 4 bytes is not enough for a valid header
        let err = parse_line_program(&[10, 0, 0, 0]);
        assert!(err.is_err());
    }

    #[test]
    fn test_line_program_invalid_version_returns_error() {
        let mut bytes = vec![0; 4]; // unit_length placeholder
        bytes.extend(1_u16.to_le_bytes()); // version 1 (unsupported, needs 2-5)
        bytes.extend(0_u32.to_le_bytes()); // header_length
        bytes.push(1); // minimum_instruction_length

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let err = parse_line_program(&bytes);
        assert!(err.is_err());
    }

    #[test]
    fn test_line_program_zero_opcode_base_returns_error() {
        let mut bytes = vec![0; 4]; // unit_length placeholder
        bytes.extend(4_u16.to_le_bytes()); // version
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes()); // header_length

        let header_start = bytes.len();
        bytes.push(1); // minimum_instruction_length
        bytes.push(1); // maximum_operations_per_instruction
        bytes.push(1); // default_is_stmt
        bytes.push((-5_i8) as u8); // line_base
        bytes.push(14); // line_range
        bytes.push(0); // opcode_base = 0 (INVALID)

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let err = parse_line_program(&bytes);
        assert!(err.is_err());
    }

    #[test]
    fn test_line_program_zero_line_range_returns_error() {
        let mut bytes = vec![0; 4]; // unit_length placeholder
        bytes.extend(4_u16.to_le_bytes()); // version
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes()); // header_length

        let header_start = bytes.len();
        bytes.push(1); // minimum_instruction_length
        bytes.push(1); // maximum_operations_per_instruction
        bytes.push(1); // default_is_stmt
        bytes.push((-5_i8) as u8); // line_base
        bytes.push(0); // line_range = 0 (INVALID)
        bytes.push(13); // opcode_base

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let err = parse_line_program(&bytes);
        assert!(err.is_err());
    }

    #[test]
    fn test_line_program_negate_stmt_opcode() {
        let mut bytes = vec![0; 4];
        bytes.extend(4_u16.to_le_bytes());
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes());

        let header_start = bytes.len();
        bytes.push(1); // min instruction length
        bytes.push(1); // max ops per instruction
        bytes.push(1); // default_is_stmt = true
        bytes.push((-5_i8) as u8); // line_base
        bytes.push(14); // line_range
        bytes.push(13); // opcode_base
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
        bytes.push(0); // end include dirs
        bytes.push(0); // end file names

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        // DW_LNS_NEGATE_STMT (opcode 6)
        bytes.push(6);
        // DW_LNS_COPY (opcode 1) to emit a row
        bytes.push(1);
        // end sequence
        bytes.push(0);
        bytes.extend(encode_uleb128(1));
        bytes.push(1);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let (_header, rows) = parse_line_program(&bytes).unwrap();
        assert_eq!(rows.len(), 2);
        // First row should have is_stmt negated (was true, now false)
        assert!(!rows[0].is_stmt);
        assert!(rows[1].end_sequence);
    }

    #[test]
    fn test_line_program_set_basic_block_opcode() {
        let mut bytes = vec![0; 4];
        bytes.extend(4_u16.to_le_bytes());
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes());

        let header_start = bytes.len();
        bytes.push(1);
        bytes.push(1);
        bytes.push(1);
        bytes.push((-5_i8) as u8);
        bytes.push(14);
        bytes.push(13);
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
        bytes.push(0);
        bytes.push(0);

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        // DW_LNS_SET_BASIC_BLOCK (opcode 7)
        bytes.push(7);
        // DW_LNS_COPY
        bytes.push(1);
        // end sequence
        bytes.push(0);
        bytes.extend(encode_uleb128(1));
        bytes.push(1);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let (_header, rows) = parse_line_program(&bytes).unwrap();
        assert_eq!(rows.len(), 2);
        assert!(rows[0].basic_block);
        // basic_block should be reset after copy
    }

    #[test]
    fn test_line_program_epilogue_begin_opcode() {
        let mut bytes = vec![0; 4];
        bytes.extend(4_u16.to_le_bytes());
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes());

        let header_start = bytes.len();
        bytes.push(1);
        bytes.push(1);
        bytes.push(1);
        bytes.push((-5_i8) as u8);
        bytes.push(14);
        bytes.push(13);
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
        bytes.push(0);
        bytes.push(0);

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        // DW_LNS_SET_EPILOGUE_BEGIN (opcode 11)
        bytes.push(11);
        // DW_LNS_COPY
        bytes.push(1);
        // end sequence
        bytes.push(0);
        bytes.extend(encode_uleb128(1));
        bytes.push(1);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let (_header, rows) = parse_line_program(&bytes).unwrap();
        assert_eq!(rows.len(), 2);
        assert!(rows[0].epilogue_begin);
    }

    #[test]
    fn test_line_program_const_add_pc_opcode() {
        let mut bytes = vec![0; 4];
        bytes.extend(4_u16.to_le_bytes());
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes());

        let header_start = bytes.len();
        bytes.push(1); // minimum_instruction_length
        bytes.push(1); // maximum_operations_per_instruction
        bytes.push(1); // default_is_stmt
        bytes.push((-5_i8) as u8); // line_base
        bytes.push(14); // line_range
        bytes.push(13); // opcode_base
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
        bytes.push(0);
        bytes.push(0);

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        // Set address first
        bytes.push(0); // extended
        bytes.extend(encode_uleb128(9));
        bytes.push(2); // DW_LNE_SET_ADDRESS
        bytes.extend(0x1000_u64.to_le_bytes());

        // DW_LNS_CONST_ADD_PC (opcode 8)
        bytes.push(8);
        // DW_LNS_COPY to emit row
        bytes.push(1);
        // end sequence
        bytes.push(0);
        bytes.extend(encode_uleb128(1));
        bytes.push(1);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let (_header, rows) = parse_line_program(&bytes).unwrap();
        assert_eq!(rows.len(), 2);
        // const_add_pc advances by (255 - opcode_base) / line_range
        // = (255 - 13) / 14 = 17 instructions = 17 bytes (min_inst_len=1)
        assert_eq!(rows[0].address, 0x1000 + 17);
    }

    #[test]
    fn test_line_program_fixed_advance_pc_opcode() {
        let mut bytes = vec![0; 4];
        bytes.extend(4_u16.to_le_bytes());
        let header_length_offset = bytes.len();
        bytes.extend(0_u32.to_le_bytes());

        let header_start = bytes.len();
        bytes.push(1);
        bytes.push(1);
        bytes.push(1);
        bytes.push((-5_i8) as u8);
        bytes.push(14);
        bytes.push(13);
        bytes.extend([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
        bytes.push(0);
        bytes.push(0);

        let header_length = (bytes.len() - header_start) as u32;
        patch_u32_le(&mut bytes, header_length_offset, header_length);

        // Set address
        bytes.push(0);
        bytes.extend(encode_uleb128(9));
        bytes.push(2);
        bytes.extend(0x2000_u64.to_le_bytes());

        // DW_LNS_FIXED_ADVANCE_PC (opcode 9): takes u16 operand
        bytes.push(9);
        bytes.extend(0x0100_u16.to_le_bytes()); // advance by 256

        // DW_LNS_COPY
        bytes.push(1);

        // end sequence
        bytes.push(0);
        bytes.extend(encode_uleb128(1));
        bytes.push(1);

        let unit_length = (bytes.len() - 4) as u32;
        patch_u32_le(&mut bytes, 0, unit_length);

        let (_header, rows) = parse_line_program(&bytes).unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].address, 0x2000 + 0x100);
    }

    #[test]
    fn test_line_state_clear_transient_flags() {
        use super::LineState;
        let mut state = LineState::new(true);
        state.basic_block = true;
        state.prologue_end = true;
        state.epilogue_begin = true;
        state.end_sequence = true;

        state.clear_transient_flags();
        assert!(!state.basic_block);
        assert!(!state.prologue_end);
        assert!(!state.epilogue_begin);
        assert!(!state.end_sequence);
        // Non-transient fields unchanged
        assert_eq!(state.address, 0);
        assert_eq!(state.line, 1);
        assert!(state.is_stmt);
    }

    #[test]
    fn test_line_state_initial_values() {
        use super::LineState;
        let state = LineState::new(false);
        assert_eq!(state.address, 0);
        assert_eq!(state.op_index, 0);
        assert_eq!(state.file, 1);
        assert_eq!(state.line, 1);
        assert_eq!(state.column, 0);
        assert!(!state.is_stmt);
        assert!(!state.basic_block);
        assert!(!state.end_sequence);
        assert!(!state.prologue_end);
        assert!(!state.epilogue_begin);
    }

    #[test]
    fn test_line_state_to_row_preserves_fields() {
        use super::LineState;
        let mut state = LineState::new(true);
        state.address = 0x42;
        state.file = 3;
        state.line = 99;
        state.column = 7;
        state.basic_block = true;
        state.prologue_end = true;

        let row = state.to_row();
        assert_eq!(row.address, 0x42);
        assert_eq!(row.file, 3);
        assert_eq!(row.line, 99);
        assert_eq!(row.column, 7);
        assert!(row.is_stmt);
        assert!(row.basic_block);
        assert!(row.prologue_end);
        assert!(!row.epilogue_begin);
        assert!(!row.end_sequence);
    }
}
