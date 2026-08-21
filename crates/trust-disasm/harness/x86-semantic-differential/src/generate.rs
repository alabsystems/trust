//! Candidates. Coverage is a statement about THIS FILE: x86-64 has no
//! fixed-width space to enumerate, so the population is generated — a
//! systematic sweep over the ModRM/SIB/REX matrix plus arithmetic/flag/branch
//! forms, a defect corpus, and seeded random bytes. Only candidates that BOTH
//! decode AND model enter the comparison; the rest are counted.

pub fn candidates(mode: &str, seed: u64, limit: usize) -> Vec<Vec<u8>> {
    let mut out = match mode {
        "corpus" => corpus(),
        "sweep" => sweep(),
        "random" => random(seed, limit),
        "all" => {
            let mut v = corpus();
            v.extend(sweep());
            v.extend(random(seed, limit));
            v
        }
        _ => Vec::new(),
    };
    out.truncate(limit.max(1).min(500_000));
    out
}

/// Encodings that exhibited real defects in the 2026-08-18 campaign, plus the
/// flag-heavy forms the decode differential structurally cannot judge.
fn corpus() -> Vec<Vec<u8>> {
    [
        "48c7c02a000000",   // mov rax, 42
        "4801d8",           // add rax, rbx      — flags
        "4829d8",           // sub rax, rbx      — flags
        "4839d8",           // cmp rax, rbx      — flags only
        "4885c0",           // test rax, rax
        "4821d8",           // and rax, rbx
        "4809d8",           // or  rax, rbx
        "4831d8",           // xor rax, rbx
        "48f7d8",           // neg rax           — CF quirk
        "48ffc0",           // inc rax           — preserves CF
        "48ffc8",           // dec rax
        "480fafc3",         // imul rax, rbx
        "48c1e004",         // shl rax, 4        — count masked; CF/OF unknown
        "48c1e040",         // shl rax, 64       — masked to 0
        "48d3e0",           // shl rax, cl
        "88e5",             // mov ch, ah        — high-byte class
        "6650",             // pushw %ax
        "50",               // push rax
        "58",               // pop rax
        "488916",           // mov [rsi], rdx
        "c60701",           // movb $1,(%rdi)
        "66c7000100",       // movw $1,(%rax)
        "488b0510000000",   // mov rax,[rip+0x10]
        "4a8b0423",         // mov rax,[rbx+r12]
        "488b0c8510000000", // mov rcx,[rax*4+0x10]
        "488b544b20",       // mov rdx,[rbx+rcx*2+0x20]
        "7405",             // je +5
        "7505",             // jne +5
        "7205",             // jb +5
        "7705",             // ja +5
        "7c05",             // jl +5
        "7f05",             // jg +5
        "eb10",             // jmp +0x10
        "e910000000",       // jmp rel32
        "e810000000",       // call rel32
        "ffd3",             // call *rbx
        "ffe7",             // jmp *rdi
        "c3",               // ret
        "0fb6c3",           // movzx eax, bl
        "0fbec3",           // movsx eax, bl
        "4863c3",           // movsxd rax, ebx
        "0f94c0",           // sete al
        "480f44c3",         // cmove rax, rbx
        "89d8",             // mov eax, ebx — 32-bit write zero-extends
        "01d8",             // add eax, ebx
        "31c0",             // xor eax, eax
    ]
    .iter()
    .filter_map(|h| hex(h))
    .collect()
}

/// The ModRM/SIB/REX matrix (as in the decode differential) plus an
/// arithmetic-opcode axis, because THIS harness judges values and flags.
fn sweep() -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    // Register-direct arithmetic across the REX axis: every opcode family the
    // model computes flags for, over distinct register pairings.
    for &opcode in &[0x01u8, 0x09, 0x11, 0x19, 0x21, 0x29, 0x31, 0x39, 0x85] {
        for rex in [0x00u8, 0x48, 0x4C, 0x49, 0x4D] {
            for modrm in [0xC0u8, 0xC3, 0xD8, 0xE1, 0xFF, 0xC8] {
                let mut b = Vec::new();
                if rex != 0 {
                    b.push(rex);
                }
                b.push(opcode);
                b.push(modrm);
                out.push(b);
            }
        }
    }
    // Memory forms over the SIB matrix with rsi/rbx/rax bases (in-window).
    for &opcode in &[0x8Bu8, 0x89, 0x03, 0x01] {
        for rex in [0x00u8, 0x48] {
            for modrm in [0x06u8, 0x03, 0x40, 0x43, 0x80, 0x04] {
                let mut b = Vec::new();
                if rex != 0 {
                    b.push(rex);
                }
                b.push(opcode);
                b.push(modrm);
                if modrm == 0x04 {
                    b.push(0x33); // SIB: rbx + rsi
                }
                match modrm >> 6 {
                    0b01 => b.push(0x10),
                    0b10 => b.extend_from_slice(&[0x10, 0, 0, 0]),
                    _ => {}
                }
                out.push(b);
            }
        }
    }
    // Shifts across counts, including the mask boundary.
    for &(op, modrm) in &[(0xC1u8, 0xE0u8), (0xC1, 0xE8), (0xC1, 0xF8)] {
        for imm in [1u8, 4, 31, 32, 63, 64, 65] {
            for rex in [0x00u8, 0x48] {
                let mut b = Vec::new();
                if rex != 0 {
                    b.push(rex);
                }
                b.extend_from_slice(&[op, modrm, imm]);
                out.push(b);
            }
        }
    }
    // Every Jcc over both taken and not-taken flag profiles (the profiles
    // handle the flag side; here just the encodings).
    for cc in 0x70u8..=0x7F {
        out.push(vec![cc, 0x08]);
    }
    out
}

fn random(seed: u64, limit: usize) -> Vec<Vec<u8>> {
    let mut state = seed | 1;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    (0..limit.min(100_000))
        .map(|_| {
            let len = 1 + (next() % 8) as usize;
            (0..len).map(|_| (next() >> 24) as u8).collect()
        })
        .collect()
}

fn hex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}
