// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

// Compile the actual maintained Targo entry for private whole-consumer
// qualification. No replacement scheduler, compiler path, result constructor
// or Host authentication is installed here. In particular, this declaration
// is absent from the shipped Targo image until its entire consumer is judged.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[repr(C, align(8))]
struct InitialQualificationDeclaration([u8; 64]);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[used]
#[unsafe(link_section = "__TEXT,__trust_pinit")]
static INITIAL_QUALIFICATION_DECLARATION: InitialQualificationDeclaration =
    InitialQualificationDeclaration(
        trust_resource_controller::workload::INITIAL_CPU_PROTOCOL_MARKER,
    );

include!("../src/bin/cargo/main.rs");
