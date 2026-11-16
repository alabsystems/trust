//! Trust (EW-18; ruling EW18-DROPIN-1): opt-in object cleanup keeps Darwin
//! debug maps and line information correct. The sibling upstream fixture keeps
//! its default object-retention assertion. These controls exercise
//! `-Ztrust-drop-rlib-objects`, including its dylib, mixed-crate and explicit
//! object-emission exceptions and the deleted-object backtrace negative.
//! Subject verification is explicitly off, as in the inherited fixture's
//! default isolated lane: these are native object/debug checks, not proof claims.

//@ only-apple
//@ ignore-cross-compile (the binaries run on the host)

use std::path::Path;

use run_make_support::object::Endianness;
use run_make_support::object::macho::{MachHeader64, N_OSO};
use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::read::macho::{MachHeader as _, Nlist as _};
use run_make_support::{
    bin_name, dynamic_lib_name, has_extension, rfs, run, rustc, shallow_find_files,
};

/// The loose object files in `dir`, sorted.
fn objects_in(dir: &str) -> Vec<String> {
    let mut objects: Vec<String> = shallow_find_files(dir, |path| has_extension(path, "o"))
        .iter()
        .map(|path| path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    objects.sort();
    objects
}

/// The object members of the archive at `path`.
fn archive_objects(path: &str) -> Vec<String> {
    let data = rfs::read(path);
    let archive = ArchiveFile::parse(&*data).unwrap();
    archive
        .members()
        .map(|member| String::from_utf8_lossy(member.unwrap().name()).into_owned())
        .filter(|name| name.ends_with(".o"))
        .collect()
}

/// The debug-map (`N_OSO`) entries of the Mach-O image at `path`.
fn debug_map(path: &str) -> Vec<String> {
    let data = rfs::read(path);
    let data = &*data;
    let header = MachHeader64::<Endianness>::parse(data, 0).unwrap();
    let endian = header.endian().unwrap();
    let mut commands = header.load_commands(endian, data, 0).unwrap();
    while let Some(command) = commands.next().unwrap() {
        if let Some(symtab) = command.symtab().unwrap() {
            let symbols = symtab.symbols::<MachHeader64<Endianness>, _>(endian, data).unwrap();
            return symbols
                .iter()
                .filter(|nlist| nlist.n_type() == N_OSO)
                .map(|nlist| {
                    String::from_utf8_lossy(nlist.name(endian, symbols.strings()).unwrap())
                        .into_owned()
                })
                .collect();
        }
    }
    panic!("`{path}` has no symbol table");
}

const DEBUGINFO: [&str; 3] =
    ["-Cdebuginfo=line-tables-only", "-Csplit-debuginfo=unpacked", "-Ccodegen-units=2"];

/// The opt-in to EW-18's rule (ruling EW18-DROPIN-1).
const DROP: &str = "-Ztrust-drop-rlib-objects";

fn main() {
    rfs::write(
        "dep.rs",
        "#[inline(never)]\n\
         pub fn dep_backtrace() -> String {\n\
         \x20   std::backtrace::Backtrace::force_capture().to_string()\n\
         }\n",
    );
    rfs::write("main.rs", "fn main() {\n    println!(\"{}\", dep::dep_backtrace());\n}\n");
    rfs::write(
        "own.rs",
        "#[inline(never)]\n\
         fn own_backtrace() -> String {\n\
         \x20   std::backtrace::Backtrace::force_capture().to_string()\n\
         }\n\
         fn main() {\n    println!(\"{}\", own_backtrace());\n}\n",
    );

    // With the flag the rlib-only compilation leaves no loose objects; its rlib holds them.
    rfs::create_dir("deps");
    rustc().arg("-Ztrust-verify=off").input("dep.rs").crate_type("rlib").args(DEBUGINFO).arg(DROP).out_dir("deps").run();
    assert_eq!(objects_in("deps"), Vec::<String>::new(), "loose objects beside the rlib");
    let members = archive_objects("deps/libdep.rlib");
    assert!(!members.is_empty(), "the rlib holds no objects");

    // A binary linked against it names the rlib's members, and still has their lines.
    rustc().arg("-Ztrust-verify=off").input("main.rs").extern_("dep", "deps/libdep.rlib").args(DEBUGINFO).arg(DROP).run();
    let osos = debug_map(&bin_name("main"));
    let dep_entries: Vec<&String> =
        osos.iter().filter(|entry| entry.contains("libdep.rlib(")).collect();
    assert!(
        !dep_entries.is_empty()
            && dep_entries.iter().all(|entry| {
                members.iter().any(|member| entry.ends_with(&format!("libdep.rlib({member})")))
            }),
        "the debug map does not name libdep.rlib's members \
         (members: {members:?}; debug map: {osos:?})",
    );
    let backtrace = run(&bin_name("main")).stdout_utf8();
    assert!(
        backtrace.contains("dep_backtrace") && backtrace.contains("dep.rs:3:"),
        "the rlib crate's frame has no line information:\n{backtrace}",
    );

    // Control: an executable's own objects are what its debug map names. Deleting them
    // drops its line information, so the check above reads DWARF through the debug map.
    rfs::create_dir("own");
    rustc().arg("-Ztrust-verify=off").input("own.rs").args(DEBUGINFO).arg(DROP).out_dir("own").run();
    let own_objects = objects_in("own");
    assert!(!own_objects.is_empty(), "the executable's objects were not kept");
    let own_binary = format!("own/{}", bin_name("own"));
    let unstripped = run(&own_binary).stdout_utf8();
    assert!(unstripped.contains("own.rs:3:"), "no line information at all:\n{unstripped}");
    for object in &own_objects {
        rfs::remove_file(Path::new("own").join(object));
    }
    let stripped = run(&own_binary).stdout_utf8();
    assert!(
        stripped.contains("own_backtrace") && !stripped.contains("own.rs:"),
        "line information survived deleting the objects the debug map names:\n{stripped}",
    );

    // Unchanged by the flag: a dylib keeps its objects, and its own debug map names them.
    rfs::create_dir("dylib");
    rustc().arg("-Ztrust-verify=off").input("dep.rs").crate_type("dylib").args(DEBUGINFO).arg(DROP).out_dir("dylib").run();
    let dylib_objects = objects_in("dylib");
    assert!(!dylib_objects.is_empty(), "the dylib's objects were not kept");
    let dylib_map = debug_map(&format!("dylib/{}", dynamic_lib_name("dep")));
    for object in &dylib_objects {
        assert!(
            dylib_map.iter().any(|entry| entry.ends_with(&format!("/{object}"))),
            "the dylib's debug map does not name its object {object} (debug map: {dylib_map:?})",
        );
    }

    // Unchanged by the flag: one compilation of an rlib AND a dylib shares its objects,
    // and the dylib's debug map names the loose ones, so every crate type must be an
    // rlib before any object goes.
    rfs::create_dir("both");
    rustc().arg("-Ztrust-verify=off")
        .input("dep.rs")
        .crate_type("rlib,dylib")
        .args(DEBUGINFO)
        .arg(DROP)
        .out_dir("both")
        .run();
    let both_objects = objects_in("both");
    assert!(!both_objects.is_empty(), "`rlib,dylib` objects were deleted");
    let both_map = debug_map(&format!("both/{}", dynamic_lib_name("dep")));
    for object in &both_objects {
        assert!(
            both_map.iter().any(|entry| entry.ends_with(&format!("/{object}"))),
            "the `rlib,dylib` dylib's debug map does not name {object} (debug map: {both_map:?})",
        );
    }

    // Unchanged by the flag: objects the user asked for are kept.
    rfs::create_dir("emit");
    rustc().arg("-Ztrust-verify=off")
        .input("dep.rs")
        .crate_type("rlib")
        .emit("obj,link")
        .args(DEBUGINFO)
        .arg(DROP)
        .out_dir("emit")
        .run();
    assert!(!objects_in("emit").is_empty(), "`--emit=obj` objects were deleted");
}
