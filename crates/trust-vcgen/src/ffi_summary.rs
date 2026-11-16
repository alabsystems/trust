// trust_vcgen/ffi_summary.rs: Extern/FFI function summary framework
//
// Provides a framework for summarizing extern/FFI function behavior for
// verification. Inspired by angr's SimProcedures and Ghidra's function
// signature database, this module models FFI function contracts (parameter
// constraints, return value contracts, side effects, safety level) and
// generates verification conditions at call sites.
//
// When verification encounters an extern "C" call (e.g., malloc, free,
// memcpy), the summary database provides a contract that constrains the
// call's behavior, enabling sound reasoning without the foreign function body.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{CalleeKey, Formula, Sort, SourceSpan, VcKind, VerificationCondition};

/// Safety classification for an FFI function.
///
/// Determines the level of trust we can place in the function's behavior
/// and what verification obligations are generated at call sites.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SafetyLevel {
    /// Function is safe to call with valid arguments (e.g., strlen on valid C string).
    Safe,
    /// Function is unsafe but has a known contract that, if satisfied, ensures
    /// defined behavior (e.g., memcpy with non-overlapping, valid-length buffers).
    UnsafeRequiresContract,
    /// Function is unsafe with unknown or unmodeled behavior. Verification must
    /// conservatively assume arbitrary side effects.
    UnsafeUnknown,
}

/// Side effects that an FFI function may produce.
///
/// Modeled after angr's SimProcedure effect annotations and Ghidra's
/// function effect metadata.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SideEffect {
    /// Allocates heap memory (e.g., malloc, calloc, realloc).
    AllocatesMemory,
    /// Frees heap memory (e.g., free, realloc).
    FreesMemory,
    /// Writes to a named global variable or memory-mapped region.
    WritesGlobal(String),
    /// Reads from a named global variable or memory-mapped region.
    ReadsGlobal(String),
    /// Invokes a callback function pointer passed as an argument.
    CallsCallback,
    /// No observable side effects (pure computation).
    None,
}

/// Contract for a single FFI function parameter.
///
/// Captures nullability, valid value ranges, and aliasing constraints
/// that must hold for the function call to be well-defined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamContract {
    /// Zero-based index of the parameter in the function signature.
    pub param_index: usize,
    /// Whether the parameter may be a null pointer.
    /// `false` means the caller must ensure non-null.
    pub is_nullable: bool,
    /// Optional inclusive value range [lo, hi] for integer parameters.
    /// `None` means no range constraint.
    pub valid_range: Option<(i128, i128)>,
    /// Aliasing class identifier. Parameters in the same aliasing class
    /// must not alias each other (e.g., memcpy src and dst).
    /// `None` means no aliasing constraint.
    pub aliasing_class: Option<String>,
}

/// A buffer argument must provide at least `count_param` BYTES. This is a
/// caller obligation, distinct from nullness and from the callee's return bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BufferContract {
    pub pointer_param: usize,
    pub count_param: usize,
}

/// What a call must be before a summary binds to it.
///
/// Trust: FFI-SCALAR-LIBC-1 (2026-11-01). The database is keyed on a NAME, and the
/// name a call reaches the lookup with is the declaration's Rust name (the extractor
/// keys the call on the decl path and drops `#[link_name]`). A summary that drops the
/// call-site row therefore vouches for whatever symbol a declaration of that name links
/// to: `#[link_name = "memset"] fn getpid(..)` would borrow `getpid`'s "no obligation".
/// The legacy rows keep [`SummaryBinding::DeclName`]; a row added from FFI-SCALAR-LIBC-1
/// on binds only through [`SummaryBinding::UpstreamLibcSymbol`], the identity
/// `ffi_pointer_contract::direct_call_contract` (G1) believes for a libc contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SummaryBinding {
    /// Binds any call the FFI lane routes (`is_foreign`, or the synthetic-MIR name
    /// fallback) whose declaration's Rust name is the summary's name.
    DeclName,
    /// Binds only a direct FOREIGN call (`is_foreign`) whose declaration an UPSTREAM
    /// crate named `libc` writes, whose Rust name (`CalleeKey::foreign_block_leaf`) and
    /// link symbol (`CalleeKey::upstream_foreign_link_symbol`, `tcx.symbol_name`) are
    /// both the summary's name, with exactly `arity` arguments. Any other call gets no
    /// summary, so it keeps the fail-closed `unmodeled FFI call` row.
    UpstreamLibcSymbol {
        /// The documented number of parameters of the C prototype.
        arity: usize,
    },
}

/// The crate whose `extern` declarations a [`SummaryBinding::UpstreamLibcSymbol`] row
/// believes (the same name `ffi_pointer_contract` believes, for the same reasons: the
/// name is defense in depth on top of the upstream link-symbol and arity checks).
pub(crate) const SUMMARY_DECLARING_CRATE: &str = "libc";

/// Summary of an extern/FFI function's behavior for verification.
///
/// Captures the full contract: parameter constraints, return value
/// guarantees, side effects, and safety classification. The verification
/// engine uses this to generate VCs at call sites without needing the
/// foreign function body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiSummary {
    /// The extern function's name (e.g., "malloc", "strlen", "memcpy").
    pub function_name: String,
    /// Per-parameter contracts.
    pub parameter_contracts: Vec<ParamContract>,
    /// Pointer/count relations measured in bytes independently of pointee type.
    pub buffer_contracts: Vec<BufferContract>,
    /// Formula constraining the return value. Uses `Var("__ffi_ret", Sort::Int)`
    /// as the return value placeholder.
    pub return_contract: Option<Formula>,
    /// Side effects produced by the function.
    pub side_effects: Vec<SideEffect>,
    /// Safety classification.
    pub safety_level: SafetyLevel,
    /// What a call must be before this summary binds to it.
    pub binding: SummaryBinding,
}

impl FfiSummary {
    /// Create a new FFI summary with the given name and no contracts.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            function_name: name.into(),
            parameter_contracts: Vec::new(),
            buffer_contracts: Vec::new(),
            return_contract: None,
            side_effects: vec![SideEffect::None],
            safety_level: SafetyLevel::UnsafeUnknown,
            binding: SummaryBinding::DeclName,
        }
    }

    /// Builder: bind only an upstream `libc` declaration of this symbol with `arity`
    /// arguments ([`SummaryBinding::UpstreamLibcSymbol`]).
    #[must_use]
    pub fn binding_upstream_libc_symbol(mut self, arity: usize) -> Self {
        self.binding = SummaryBinding::UpstreamLibcSymbol { arity };
        self
    }

    /// Whether this summary binds a call: `is_foreign` is the extractor's
    /// `tcx.is_foreign_item`, `key` the call's [`CalleeKey`], `arg_count` its argument
    /// count. A [`SummaryBinding::DeclName`] row binds every call it is looked up for;
    /// a [`SummaryBinding::UpstreamLibcSymbol`] row binds only the identity it names,
    /// and anything missing (no key, a local declaration, a renamed link symbol, another
    /// arity, another declaring crate) answers `false`.
    #[must_use]
    pub fn binds_call(&self, is_foreign: bool, key: Option<&CalleeKey>, arg_count: usize) -> bool {
        match self.binding {
            SummaryBinding::DeclName => true,
            SummaryBinding::UpstreamLibcSymbol { arity } => {
                let name = self.function_name.as_str();
                is_foreign
                    && arg_count == arity
                    && key.is_some_and(|key| {
                        key.krate_name == SUMMARY_DECLARING_CRATE
                            && key.foreign_block_leaf.as_deref() == Some(name)
                            && key.upstream_foreign_link_symbol.as_deref() == Some(name)
                    })
            }
        }
    }

    /// Builder: add a parameter contract.
    #[must_use]
    pub fn with_param(mut self, contract: ParamContract) -> Self {
        self.parameter_contracts.push(contract);
        self
    }

    #[must_use]
    pub fn with_buffer(mut self, contract: BufferContract) -> Self {
        self.buffer_contracts.push(contract);
        self
    }

    /// Builder: set the return contract formula.
    #[must_use]
    pub fn with_return_contract(mut self, formula: Formula) -> Self {
        self.return_contract = Some(formula);
        self
    }

    /// Builder: set side effects.
    #[must_use]
    pub fn with_side_effects(mut self, effects: Vec<SideEffect>) -> Self {
        self.side_effects = effects;
        self
    }

    /// Builder: set the safety level.
    #[must_use]
    pub fn with_safety(mut self, level: SafetyLevel) -> Self {
        self.safety_level = level;
        self
    }
}

/// In-memory database of known FFI function summaries.
///
/// Pre-populated with summaries for common libc functions (malloc, free,
/// memcpy, strlen, printf, read, write). Users can register additional
/// summaries for project-specific FFI functions.
#[derive(Debug, Clone)]
pub struct FfiSummaryDb {
    summaries: FxHashMap<String, FfiSummary>,
    min_name_len: usize,
    max_name_len: usize,
    has_path_separator: bool,
}

impl Default for FfiSummaryDb {
    fn default() -> Self {
        Self::new()
    }
}

impl FfiSummaryDb {
    /// Return a shared static reference to the built-in FFI summary database,
    /// initialized once on first access.
    #[must_use]
    pub fn builtin() -> &'static Self {
        static BUILTIN: std::sync::OnceLock<FfiSummaryDb> = std::sync::OnceLock::new();
        BUILTIN.get_or_init(Self::new)
    }

    /// Create a new database pre-populated with built-in libc summaries.
    #[must_use]
    pub fn new() -> Self {
        let mut db = Self {
            summaries: FxHashMap::with_capacity_and_hasher(48, Default::default()),
            min_name_len: usize::MAX,
            max_name_len: 0,
            has_path_separator: false,
        };
        db.register_builtins();
        db
    }

    /// Create an empty database with no built-in summaries.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            summaries: FxHashMap::default(),
            min_name_len: usize::MAX,
            max_name_len: 0,
            has_path_separator: false,
        }
    }

    /// Look up a summary by function name.
    #[inline]
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&FfiSummary> {
        let len = name.len();
        if len < self.min_name_len || len > self.max_name_len {
            return None;
        }
        if !self.has_path_separator && name.contains("::") {
            return None;
        }
        self.summaries.get(name)
    }

    #[inline]
    #[must_use]
    pub(crate) fn has_path_separator(&self) -> bool {
        self.has_path_separator
    }

    #[inline]
    #[must_use]
    pub(crate) fn lookup_prechecked_bare(&self, name: &str) -> Option<&FfiSummary> {
        let len = name.len();
        if len < self.min_name_len || len > self.max_name_len {
            return None;
        }
        self.summaries.get(name)
    }

    /// Register a custom FFI summary.
    pub fn register(&mut self, summary: FfiSummary) {
        let len = summary.function_name.len();
        self.min_name_len = self.min_name_len.min(len);
        self.max_name_len = self.max_name_len.max(len);
        self.has_path_separator |= summary.function_name.contains("::");
        self.summaries.insert(summary.function_name.clone(), summary);
    }

    /// Number of summaries in the database.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Whether the database is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty()
    }

    /// All registered function names.
    #[must_use]
    pub fn function_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.summaries.keys().map(String::as_str).collect();
        names.sort();
        names
    }

    /// Register built-in libc summaries.
    fn register_builtins(&mut self) {
        self.register(builtin_malloc());
        self.register(builtin_free());
        self.register(builtin_memcpy());
        self.register(builtin_strlen());
        self.register(builtin_printf());
        self.register(builtin_fprintf());
        self.register(builtin_sprintf());
        self.register(builtin_read());
        self.register(builtin_write());
        self.register(builtin_calloc());
        self.register(builtin_realloc());
        self.register(builtin_memmove());
        self.register(builtin_memset());
        self.register(builtin_strcmp());
        self.register(builtin_strncpy());
        self.register(builtin_strcpy());
        self.register(builtin_strcat());
        self.register(builtin_strncat());
        self.register(builtin_puts());
        self.register(builtin_fopen());
        self.register(builtin_fclose());
        self.register(builtin_fread());
        self.register(builtin_fwrite());
        self.register(builtin_snprintf());
        // T6: demand-free fd/process-seam summaries. NOTE the collision
        // surface these names would have under last-segment matching
        // (`Future::poll`, `Child::kill`, `File::access`…) — registering them
        // is sound ONLY because `is_extern_call` no longer matches a
        // qualified Rust path by its terminal segment (T1).
        self.register(builtin_close());
        self.register(builtin_dup());
        self.register(builtin_fcntl());
        self.register(builtin_kill());
        self.register(builtin_killpg());
        self.register(builtin_waitpid());
        self.register(builtin_getuid());
        // T9 (#[link_name] import alias): aterm-types dirs.rs imports getuid as
        // `#[link_name = "getuid"] fn libc_getuid();` — extraction keys the call
        // on the RUST DECL NAME (`dirs::libc_getuid`, short `libc_getuid`) and
        // DROPS the link_name attribute, so the `getuid` summary above never
        // binds and the call fails closed as "unmodeled FFI call: no summary"
        // (gate-logs-w3/aterm-types.log, hardened_ffi_boundary UNKNOWN at
        // dirs.rs:37). The general fix — carrying link_name on
        // `Terminator::Call` and using it as the lookup key — needs a new field
        // on a serialized variant constructed in ~350 places (including the
        // ir-bridge lowering), so until that lands, register the ONE
        // evidence-demanded alias explicitly. Binding by the Rust decl name is
        // exactly as name-trusting as every other entry in this db (the routing
        // gate is the authoritative extraction-side `is_foreign`, so only a
        // genuine foreign import reaches it); keeping the alias NARROW — not a
        // generic `libc_*` prefix-strip — keeps the mis-bind surface at this
        // single name.
        self.register(FfiSummary { function_name: "libc_getuid".to_string(), ..builtin_getuid() });
        self.register(builtin_access());
        self.register(builtin_getentropy());
        self.register(builtin_poll());
        self.register(builtin_pipe());
        self.register(builtin_ioctl());
        // FFI-SCALAR-LIBC-1 (2026-11-01): the integer-only process, session and
        // terminal queries the agy-alab and claude-code-alab strict gates call, and the
        // errno-slot accessors. Each binds only an upstream `libc` declaration of its
        // own symbol at its documented arity (`SummaryBinding::UpstreamLibcSymbol`);
        // docs/TCB.md "libc integer-argument call summaries" lists the same rows.
        for summary in scalar_libc_summaries() {
            self.register(summary);
        }
    }
}

/// FFI-SCALAR-LIBC-1: C functions whose every parameter is an integer and whose call
/// therefore reads and writes no memory through any argument the caller supplies. No
/// value of an integer argument is undefined behaviour for them: a bad pid, fd or
/// signal number is an error return (`ESRCH`, `EBADF`/`ENOTTY`, `EINVAL`). Each is
/// `Safe` with no parameter contract, so a bound call mints no call-site obligation;
/// its result is an unconstrained integer (or pointer) to every later use, which is
/// verified on its own. The return contracts are informational: this layer has no
/// assumption channel (see `generate_call_site_vcs_with_extents`, step 2).
pub(crate) fn scalar_libc_summaries() -> Vec<FfiSummary> {
    vec![
        // `pid_t getpid(void)`: "shall always be successful" (POSIX.1-2024 getpid).
        FfiSummary::new("getpid")
            .with_return_contract(ffi_ret_ge(0))
            .with_safety(SafetyLevel::Safe)
            .binding_upstream_libc_symbol(0),
        // `pid_t getpgrp(void)`: "shall always be successful" (POSIX getpgrp).
        FfiSummary::new("getpgrp")
            .with_return_contract(ffi_ret_ge(0))
            .with_safety(SafetyLevel::Safe)
            .binding_upstream_libc_symbol(0),
        // `uid_t geteuid(void)`: "shall always be successful" (POSIX geteuid).
        FfiSummary::new("geteuid")
            .with_return_contract(ffi_ret_ge(0))
            .with_safety(SafetyLevel::Safe)
            .binding_upstream_libc_symbol(0),
        // `pid_t getsid(pid_t pid)`: the session id, or -1 with errno (POSIX getsid).
        FfiSummary::new("getsid")
            .with_return_contract(ffi_ret_ge(-1))
            .with_safety(SafetyLevel::Safe)
            .binding_upstream_libc_symbol(1),
        // `pid_t tcgetpgrp(int fildes)`: the foreground process group id, or -1 with
        // errno (POSIX tcgetpgrp).
        FfiSummary::new("tcgetpgrp")
            .with_return_contract(ffi_ret_ge(-1))
            .with_safety(SafetyLevel::Safe)
            .binding_upstream_libc_symbol(1),
        // `int raise(int sig)`: 0, or nonzero on failure (C17 7.14.2.1). It delivers
        // `sig` to the calling thread, so a handler the program installed may run
        // before it returns: that handler is a function of the program, verified as
        // its own body, and what it changes outside this frame is state a foreign call
        // already leaves unconstrained (the `kill` row, the same delivery to the
        // caller's own process, has been `Safe` since T6).
        FfiSummary::new("raise").with_safety(SafetyLevel::Safe).binding_upstream_libc_symbol(1),
        // `int *__error(void)` (Darwin) and `int *__errno_location(void)` (glibc, musl):
        // the calling thread's errno slot; always succeed. What a dereference of the
        // result may assume is `ffi_pointer_contract`'s (G1), not this row's.
        FfiSummary::new("__error").with_safety(SafetyLevel::Safe).binding_upstream_libc_symbol(0),
        FfiSummary::new("__errno_location")
            .with_safety(SafetyLevel::Safe)
            .binding_upstream_libc_symbol(0),
    ]
}

/// Return the zero-based format-string argument index for printf-family calls.
#[must_use]
pub(crate) fn printf_family_format_index(name: &str) -> Option<usize> {
    let short = name.rsplit("::").next().unwrap_or(name);
    match short {
        "printf" | "vprintf" => Some(0),
        "fprintf" | "sprintf" | "asprintf" | "dprintf" | "vfprintf" | "vsprintf" | "vasprintf"
        | "vdprintf" => Some(1),
        "snprintf" | "vsnprintf" => Some(2),
        _ => None,
    }
}

/// True for libc printf-family calls with a caller-controlled format argument.
#[must_use]
pub(crate) fn is_printf_family(name: &str) -> bool {
    printf_family_format_index(name).is_some()
}

// ---------------------------------------------------------------------------
// Built-in FFI summaries for common libc functions
// ---------------------------------------------------------------------------

/// Return-contract helper: `__ffi_ret >= min`.
fn ffi_ret_ge(min: i128) -> Formula {
    Formula::Ge(Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)), Box::new(Formula::Int(min)))
}

/// Return-contract helper: `lo <= __ffi_ret <= hi` (inclusive).
fn ffi_ret_between(lo: i128, hi: i128) -> Formula {
    Formula::And(vec![
        Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(lo)),
        ),
        Formula::Le(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(hi)),
        ),
    ])
}

/// Return-contract helper for a bytes-transferred syscall: `-1 <= __ffi_ret <=
/// __ffi_arg_{count_arg}`. Models `read`/`write` (and kin): they return the
/// number of bytes transferred, which is NEVER more than the requested `count`
/// (short reads/writes are `<= count`), or -1 on error. This is a SOUND POSIX
/// guarantee (an assumption the callee provides, not a caller obligation).
///
/// The upper bound is load-bearing for panic-freedom of the ubiquitous
/// `while off < buf.len() { off += write(fd, &buf[off..], buf.len() - off) }`
/// drain loop: without `ret <= count`, `off += ret` has an unbounded addend, so
/// the overflow obligation is unprovable and the CHC solver diverges. With it,
/// `off + ret <= buf.len() <= isize::MAX`, so no overflow. (Previously only the
/// `>= -1` lower half was modeled; see `builtin_read`/`builtin_write`.)
fn ffi_ret_bytes_transferred(count_arg: usize) -> Formula {
    Formula::And(vec![
        Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(-1)),
        ),
        Formula::Le(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var(format!("__ffi_arg_{count_arg}"), Sort::Int)),
        ),
    ])
}

/// `void *malloc(size_t size)`
///
/// Allocates `size` bytes. Returns non-null on success or null on failure.
/// Caller must eventually free the returned pointer.
fn builtin_malloc() -> FfiSummary {
    FfiSummary::new("malloc")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            // size >= 0 (size_t is unsigned, but in our model we use signed int)
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        // Return value: either null (0) or positive (valid pointer)
        .with_return_contract(Formula::Or(vec![
            Formula::Eq(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]))
        .with_side_effects(vec![SideEffect::AllocatesMemory])
        .with_safety(SafetyLevel::Safe)
}

/// `void free(void *ptr)`
///
/// Frees previously allocated memory. `ptr` must be non-null and previously
/// allocated by malloc/calloc/realloc, or must be null (in which case free
/// is a no-op).
fn builtin_free() -> FfiSummary {
    FfiSummary::new("free")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: true, // free(NULL) is defined as a no-op
            valid_range: None,
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::FreesMemory])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `void *memcpy(void *dest, const void *src, size_t n)`
///
/// Copies `n` bytes from `src` to `dest`. The memory regions must not overlap.
/// Both pointers must be valid for at least `n` bytes.
fn builtin_memcpy() -> FfiSummary {
    FfiSummary::new("memcpy")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("memcpy_region".into()),
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("memcpy_region".into()),
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        // Returns dest pointer
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `size_t strlen(const char *s)`
///
/// Returns the length of the null-terminated string `s`. The pointer must
/// be non-null and point to a valid null-terminated string.
fn builtin_strlen() -> FfiSummary {
    FfiSummary::new("strlen")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        // Return value: non-negative length
        .with_return_contract(Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))
        .with_side_effects(vec![SideEffect::None])
        .with_safety(SafetyLevel::Safe)
}

/// `int printf(const char *format, ...)`
///
/// Formatted output to stdout. Format string must be non-null.
/// Returns the number of characters printed, or negative on error.
fn builtin_printf() -> FfiSummary {
    FfiSummary::new("printf")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::WritesGlobal("stdout".into())])
        .with_safety(SafetyLevel::Safe)
}

/// `int fprintf(FILE *stream, const char *format, ...)`
fn builtin_fprintf() -> FfiSummary {
    FfiSummary::new("fprintf")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::WritesGlobal("stream".into())])
        .with_safety(SafetyLevel::Safe)
}

/// `int sprintf(char *str, const char *format, ...)`
fn builtin_sprintf() -> FfiSummary {
    FfiSummary::new("sprintf")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `ssize_t read(int fd, void *buf, size_t count)`
///
/// Reads up to `count` bytes from file descriptor `fd` into `buf`.
/// Returns bytes read (0 at EOF), or -1 on error.
///
/// The buffer must be non-null and provide `count` bytes. `fd` carries NO
/// demand — a bad fd is EBADF, an
/// errno-level runtime error, not UB, so the old `[0, i128::MAX]` range
/// refuted every runtime-provided fd. `count == 0` is defined (the old
/// integer "non-null" check refuted it), but a short read does not license
/// passing a buffer smaller than the requested count.
fn builtin_read() -> FfiSummary {
    FfiSummary::new("read")
        .with_buffer(BufferContract { pointer_param: 1, count_param: 2 })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        // Guarantee (assumption, not obligation): -1 <= ret <= count.
        // count is `size_t count` = param 2.
        .with_return_contract(ffi_ret_bytes_transferred(2))
        .with_side_effects(vec![SideEffect::ReadsGlobal("fd".into())])
        .with_safety(SafetyLevel::Safe)
}

/// `ssize_t write(int fd, const void *buf, size_t count)`
///
/// Writes up to `count` bytes from `buf` to file descriptor `fd`.
/// Returns bytes written, or -1 on error.
///
/// Like `read`, requires a non-null buffer and its requested BYTE extent.
/// The former fd and integer-nonzero count demands were over-refutation
/// (EBADF is errno, `write(fd, buf, 0)` is defined). The `WritesGlobal("fd")`
/// effect is dropped: it minted an
/// undischargeable audit obligation per call site (the report's 38-obligation
/// aterm-types refutation shape), and the fd-offset havoc it described is
/// already the model default (nothing constrains kernel state here).
fn builtin_write() -> FfiSummary {
    FfiSummary::new("write")
        .with_buffer(BufferContract { pointer_param: 1, count_param: 2 })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        // Guarantee (assumption, not obligation): -1 <= ret <= count.
        // count is `size_t count` = param 2. The `ret <= count` upper bound is
        // what makes the `off += write(..)` drain-loop overflow obligation
        // provable (was the ay-divergence root cause on write_frame_locked).
        .with_return_contract(ffi_ret_bytes_transferred(2))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::Safe)
}

/// `void *calloc(size_t nmemb, size_t size)`
fn builtin_calloc() -> FfiSummary {
    FfiSummary::new("calloc")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_return_contract(Formula::Or(vec![
            Formula::Eq(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]))
        .with_side_effects(vec![SideEffect::AllocatesMemory])
        .with_safety(SafetyLevel::Safe)
}

/// `void *realloc(void *ptr, size_t size)`
fn builtin_realloc() -> FfiSummary {
    FfiSummary::new("realloc")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: true,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::AllocatesMemory, SideEffect::FreesMemory])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `void *memmove(void *dest, const void *src, size_t n)`
fn builtin_memmove() -> FfiSummary {
    FfiSummary::new("memmove")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `void *memset(void *s, int c, size_t n)`
fn builtin_memset() -> FfiSummary {
    FfiSummary::new("memset")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: Some((0, 255)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `int strcmp(const char *s1, const char *s2)`
fn builtin_strcmp() -> FfiSummary {
    FfiSummary::new("strcmp")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::None])
        .with_safety(SafetyLevel::Safe)
}

/// `char *strncpy(char *dest, const char *src, size_t n)`
fn builtin_strncpy() -> FfiSummary {
    FfiSummary::new("strncpy")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strcpy_region".into()),
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strcpy_region".into()),
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `char *strcpy(char *dest, const char *src)`
fn builtin_strcpy() -> FfiSummary {
    FfiSummary::new("strcpy")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strcpy_region".into()),
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strcpy_region".into()),
        })
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `char *strcat(char *dest, const char *src)`
fn builtin_strcat() -> FfiSummary {
    FfiSummary::new("strcat")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strcat_region".into()),
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strcat_region".into()),
        })
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `char *strncat(char *dest, const char *src, size_t n)`
fn builtin_strncat() -> FfiSummary {
    FfiSummary::new("strncat")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strncat_region".into()),
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: Some("strncat_region".into()),
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_return_contract(Formula::Eq(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `int puts(const char *s)`
fn builtin_puts() -> FfiSummary {
    FfiSummary::new("puts")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::WritesGlobal("stdout".into())])
        .with_safety(SafetyLevel::Safe)
}

/// `FILE *fopen(const char *path, const char *mode)`
fn builtin_fopen() -> FfiSummary {
    FfiSummary::new("fopen")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(Formula::Or(vec![
            Formula::Eq(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]))
        .with_side_effects(vec![SideEffect::AllocatesMemory])
        .with_safety(SafetyLevel::Safe)
}

/// `int fclose(FILE *stream)`
fn builtin_fclose() -> FfiSummary {
    FfiSummary::new("fclose")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_side_effects(vec![SideEffect::FreesMemory])
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream)`
fn builtin_fread() -> FfiSummary {
    FfiSummary::new("fread")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 3,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))
        .with_side_effects(vec![SideEffect::ReadsGlobal("stream".into())])
        .with_safety(SafetyLevel::Safe)
}

/// `size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream)`
fn builtin_fwrite() -> FfiSummary {
    FfiSummary::new("fwrite")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 3,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))
        .with_side_effects(vec![SideEffect::WritesGlobal("stream".into())])
        .with_safety(SafetyLevel::Safe)
}

/// `int snprintf(char *str, size_t size, const char *format, ...)`
fn builtin_snprintf() -> FfiSummary {
    FfiSummary::new("snprintf")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: false,
            valid_range: Some((0, i128::MAX)),
            aliasing_class: None,
        })
        .with_param(ParamContract {
            param_index: 2,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(Formula::Ge(
            Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))
        .with_side_effects(vec![])
        .with_safety(SafetyLevel::Safe)
}

// ---------------------------------------------------------------------------
// Demand-free fd/process-seam summaries (T6, report addendum)
//
// Shared soundness rule: an fd is a kernel-validated HANDLE — passing a bad
// one is an errno-level runtime error (EBADF/ESRCH/EINVAL), never UB — so
// none of these impose fd range/validity demands on the caller. The only
// demands kept are pointer non-nullability where NULL is actually UB. Return
// contracts state the callee's guarantee (assumption; currently inert at call
// sites — no assumption channel, see ffi_vcgen::generate_call_site_vcs).
// ---------------------------------------------------------------------------

/// `int close(int fd)` — returns 0 on success, -1 on error (errno).
fn builtin_close() -> FfiSummary {
    FfiSummary::new("close")
        .with_return_contract(ffi_ret_between(-1, 0))
        .with_safety(SafetyLevel::Safe)
}

/// `int dup(int fd)` — returns the new (non-negative) fd, or -1 on error.
fn builtin_dup() -> FfiSummary {
    FfiSummary::new("dup").with_return_contract(ffi_ret_ge(-1)).with_safety(SafetyLevel::Safe)
}

/// `int fcntl(int fd, int cmd, ...)` — returns a cmd-dependent non-negative
/// value, or -1 on error. The variadic third argument's meaning depends on
/// `cmd` (F_GETFL takes none, F_SETFL an int, some cmds a pointer), which is
/// why the summary is `UnsafeRequiresContract`: pointer-taking cmds have
/// validity requirements this flat summary cannot express. No demands are
/// imposed — the common int-cmd forms (F_GETFL/F_SETFL/F_DUPFD) are
/// errno-checked, not UB.
fn builtin_fcntl() -> FfiSummary {
    FfiSummary::new("fcntl")
        .with_return_contract(ffi_ret_ge(-1))
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `int kill(pid_t pid, int sig)` — returns 0 on success, -1 on error
/// (ESRCH/EPERM/EINVAL are errno, not UB).
fn builtin_kill() -> FfiSummary {
    FfiSummary::new("kill")
        .with_return_contract(ffi_ret_between(-1, 0))
        .with_safety(SafetyLevel::Safe)
}

/// `int killpg(pid_t pgrp, int sig)` — returns 0 on success, -1 on error.
fn builtin_killpg() -> FfiSummary {
    FfiSummary::new("killpg")
        .with_return_contract(ffi_ret_between(-1, 0))
        .with_safety(SafetyLevel::Safe)
}

/// `pid_t waitpid(pid_t pid, int *status, int options)` — returns the reaped
/// pid (or 0 with WNOHANG), -1 on error.
///
/// `status` is NULLABLE (NULL opts out of status reporting); on a non-null
/// pointer the kernel WRITES `*status`, so the pointee must be writable for
/// one int — from Rust the idiomatic `&mut status` is valid by construction,
/// and "valid-or-null" is not expressible as a flat demand, hence
/// `UnsafeRequiresContract` rather than a nonnull demand that would refute
/// the legal NULL form.
fn builtin_waitpid() -> FfiSummary {
    FfiSummary::new("waitpid")
        .with_param(ParamContract {
            param_index: 1,
            is_nullable: true,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(ffi_ret_ge(-1))
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

/// `uid_t getuid(void)` — always succeeds; the uid is non-negative.
fn builtin_getuid() -> FfiSummary {
    FfiSummary::new("getuid").with_return_contract(ffi_ret_ge(0)).with_safety(SafetyLevel::Safe)
}

/// `int access(const char *path, int mode)` — returns 0 on success, -1 on
/// error. `path` must be a valid C string (non-null demanded); the mode is
/// errno-checked.
fn builtin_access() -> FfiSummary {
    FfiSummary::new("access")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(ffi_ret_between(-1, 0))
        .with_safety(SafetyLevel::Safe)
}

/// `int getentropy(void *buf, size_t buflen)` — returns 0 on success, -1 on
/// error. The kernel writes `buflen` bytes into `buf` (non-null demanded);
/// over-length requests are EIO/EINVAL, not UB.
fn builtin_getentropy() -> FfiSummary {
    FfiSummary::new("getentropy")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(ffi_ret_between(-1, 0))
        .with_safety(SafetyLevel::Safe)
}

/// `int poll(struct pollfd *fds, nfds_t nfds, int timeout)` — returns the
/// number of ready fds, 0 on timeout, -1 on error. `fds` is demanded
/// non-null; the `poll(NULL, 0, ms)` sleep idiom is a conditional
/// nullability (legal only with `nfds == 0`) this flat contract cannot
/// express, so that idiom stays conservatively refuted rather than
/// permitting NULL with a positive nfds (which IS UB).
fn builtin_poll() -> FfiSummary {
    FfiSummary::new("poll")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(ffi_ret_ge(-1))
        .with_safety(SafetyLevel::Safe)
}

/// `int pipe(int fds[2])` — returns 0 on success, -1 on error. The kernel
/// writes two ints through `fds`, so it must be non-null (and valid for two
/// ints — from Rust a `&mut [c_int; 2]` is valid by construction).
fn builtin_pipe() -> FfiSummary {
    FfiSummary::new("pipe")
        .with_param(ParamContract {
            param_index: 0,
            is_nullable: false,
            valid_range: None,
            aliasing_class: None,
        })
        .with_return_contract(ffi_ret_between(-1, 0))
        .with_safety(SafetyLevel::Safe)
}

/// `int ioctl(int fd, unsigned long request, ...)` — returns >= -1 (most
/// requests return 0/-1, some return non-negative values). Like `fcntl`,
/// the variadic argument is request-dependent and often a pointer with
/// validity requirements this flat summary cannot express:
/// `UnsafeRequiresContract`, with no demands (bad fd/request are errno).
fn builtin_ioctl() -> FfiSummary {
    FfiSummary::new("ioctl")
        .with_return_contract(ffi_ret_ge(-1))
        .with_safety(SafetyLevel::UnsafeRequiresContract)
}

// ---------------------------------------------------------------------------
// Summary instantiation
// ---------------------------------------------------------------------------

/// Instantiate an FFI summary with concrete argument formulas.
///
/// Substitutes `__ffi_arg_N` placeholders in the return contract with the
/// corresponding formulas from `args`, producing a formula that constrains
/// the return value (`__ffi_ret`) in terms of the actual call-site arguments.
///
/// If the summary has no return contract, returns `Formula::Bool(true)`
/// (no constraint on the return value). If an `__ffi_arg_N` placeholder
/// references a parameter beyond the provided `args`, it is left as-is
/// (symbolic / unconstrained).
///
/// Inspired by angr's `SimProcedure.run()` which instantiates a summary
/// with concrete symbolic state.
#[must_use]
pub fn apply_summary(summary: &FfiSummary, args: &[Formula]) -> Formula {
    let Some(contract) = &summary.return_contract else {
        return Formula::Bool(true);
    };
    if args.is_empty()
        || !trust_types::any_formula_node(contract, &mut |node| {
            matches!(node, Formula::Var(var_sym, _) if var_sym.starts_with("__ffi_arg_"))
        })
    {
        return contract.clone();
    }

    // Substitute __ffi_arg_N placeholders with concrete args.
    contract.clone().map(&mut |node| {
        if let Formula::Var(ref name, _) = node
            && let Some(idx_str) = name.strip_prefix("__ffi_arg_")
            && let Ok(idx) = idx_str.parse::<usize>()
            && let Some(arg) = args.get(idx)
        {
            return arg.clone();
        }
        node
    })
}

// ---------------------------------------------------------------------------
// VC generation from FFI summaries
// ---------------------------------------------------------------------------

/// Generate verification conditions for an FFI call site.
///
/// Given a call site identifier, an FFI summary, and the actual argument
/// formulas, produces VCs that ensure:
/// 1. Non-nullable parameters receive non-null arguments
/// 2. Integer parameters fall within their valid ranges
/// 3. Parameters in the same aliasing class are not equal (no aliasing)
///
/// The `call_site` string identifies the location for diagnostics (e.g.,
/// `"main::line_42"`).
#[must_use]
pub fn generate_ffi_vcs(
    call_site: &str,
    summary: &FfiSummary,
    args: &[Formula],
    // Arg positions with proven non-null provenance at the call site (a
    // std-container `as_ptr` result, a reference, or a non-deref raw borrow —
    // see `generate::ffi_nonnull_locals`). Their null VCs are UNSAT by
    // construction and are discharged at generation; posing them over the
    // unconstrained arg symbol would only manufacture a trivially-SAT
    // counterexample (`arg := 0`) for a value that can never be 0.
    nonnull_args: &std::collections::HashSet<usize>,
) -> Vec<VerificationCondition> {
    generate_ffi_vcs_with_extents(call_site, summary, args, nonnull_args, &Default::default())
}

/// Same caller demands, with must-proven byte extents from the current call site.
pub(crate) fn generate_ffi_vcs_with_extents(
    call_site: &str,
    summary: &FfiSummary,
    args: &[Formula],
    nonnull_args: &std::collections::HashSet<usize>,
    byte_extents: &std::collections::HashMap<usize, u64>,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let location = SourceSpan::default();
    let call_site_sym: trust_types::Symbol = call_site.into();

    // 1. Non-null checks for non-nullable pointer parameters
    for contract in &summary.parameter_contracts {
        if !contract.is_nullable
            && !nonnull_args.contains(&contract.param_index)
            && let Some(arg) = args.get(contract.param_index)
        {
            // VC: argument != 0 (null pointer check)
            // Convention: we assert the negation (arg == 0) and check SAT.
            // If UNSAT, the argument is never null.
            let null_vc = Formula::Eq(Box::new(arg.clone()), Box::new(Formula::Int(0)));
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "FFI `{}`: parameter {} must be non-null at {}",
                        summary.function_name, contract.param_index, call_site,
                    ),
                },
                function: call_site_sym.clone(),
                location: location.clone(),
                formula: null_vc,
                contract_metadata: None,
                obligation: None,
            });
        }
    }

    for contract in &summary.buffer_contracts {
        let count =
            args.get(contract.count_param).filter(|_| args.get(contract.pointer_param).is_some());
        let extent = byte_extents.get(&contract.pointer_param);
        let formula = match (count, extent) {
            (Some(count), Some(bytes)) => Formula::Or(vec![
                Formula::Lt(Box::new(count.clone()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(count.clone()), Box::new(Formula::Int(i128::from(*bytes)))),
            ]),
            // No allocation is required for an empty access. No unknown extent
            // is assumed: a positive count still has a satisfiable violation.
            (Some(count), None) => Formula::Not(Box::new(Formula::Eq(
                Box::new(count.clone()),
                Box::new(Formula::Int(0)),
            ))),
            (None, _) => Formula::Bool(true),
        };
        let extent_label: std::borrow::Cow<'static, str> = match extent {
            Some(bytes) => std::borrow::Cow::Owned(bytes.to_string()),
            None => std::borrow::Cow::Borrowed("unknown"),
        };
        vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!("FFI `{}`: parameter {} byte count must fit parameter {} available byte extent ({extent_label})",
                    summary.function_name, contract.count_param, contract.pointer_param),
            },
            function: call_site_sym.clone(), location: location.clone(), formula,
            contract_metadata: None, obligation: None,
        });
    }

    // 2. Range checks for integer parameters
    for contract in &summary.parameter_contracts {
        if let Some((lo, hi)) = contract.valid_range
            && let Some(arg) = args.get(contract.param_index)
        {
            // VC: arg < lo OR arg > hi (violation formula)
            // If UNSAT, the argument is always in range.
            let range_violation = Formula::Or(vec![
                Formula::Lt(Box::new(arg.clone()), Box::new(Formula::Int(lo))),
                Formula::Gt(Box::new(arg.clone()), Box::new(Formula::Int(hi))),
            ]);
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "FFI `{}`: parameter {} must be in range [{}, {}] at {}",
                        summary.function_name, contract.param_index, lo, hi, call_site,
                    ),
                },
                function: call_site_sym.clone(),
                location: location.clone(),
                formula: range_violation,
                contract_metadata: None,
                obligation: None,
            });
        }
    }

    // 3. Non-aliasing checks for parameters in the same aliasing class
    if summary.parameter_contracts.len() >= 2 {
        let mut aliasing_groups: FxHashMap<&str, Vec<(usize, &Formula)>> = FxHashMap::default();
        for contract in &summary.parameter_contracts {
            if let Some(ref class) = contract.aliasing_class
                && let Some(arg) = args.get(contract.param_index)
            {
                aliasing_groups.entry(class.as_str()).or_default().push((contract.param_index, arg));
            }
        }
        for members in aliasing_groups.values() {
            // Check all pairs within each aliasing class
            for i in 0..members.len() {
                for j in (i + 1)..members.len() {
                    let (idx_a, arg_a) = &members[i];
                    let (idx_b, arg_b) = &members[j];
                    // VC: arg_a == arg_b (alias violation)
                    // If UNSAT, the pointers never alias.
                    let alias_vc =
                        Formula::Eq(Box::new((*arg_a).clone()), Box::new((*arg_b).clone()));
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "FFI `{}`: parameters {} and {} must not alias at {}",
                                summary.function_name, idx_a, idx_b, call_site,
                            ),
                        },
                        function: call_site_sym.clone(),
                        location: location.clone(),
                        formula: alias_vc,
                        contract_metadata: None,
                        obligation: None,
                    });
                }
            }
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ffi_vcgen::generate_call_site_vcs;

    #[test]
    fn test_ffi_summary_db_has_builtins() {
        let db = FfiSummaryDb::new();
        assert!(db.len() >= 7, "should have at least 7 builtin summaries");

        let names = db.function_names();
        for expected in &["malloc", "free", "memcpy", "strlen", "printf", "read", "write"] {
            assert!(names.contains(expected), "missing builtin summary for `{expected}`");
        }
    }

    #[test]
    fn test_printf_family_format_indices() {
        assert_eq!(printf_family_format_index("printf"), Some(0));
        assert_eq!(printf_family_format_index("libc::fprintf"), Some(1));
        assert_eq!(printf_family_format_index("snprintf"), Some(2));
        assert_eq!(printf_family_format_index("puts"), None);
        assert!(is_printf_family("sprintf"));
    }

    #[test]
    fn test_ffi_summary_db_empty() {
        let db = FfiSummaryDb::empty();
        assert!(db.is_empty());
        assert_eq!(db.len(), 0);
        assert!(db.lookup("malloc").is_none());
    }

    #[test]
    fn test_ffi_summary_db_lookup_malloc() {
        let db = FfiSummaryDb::new();
        let malloc = db.lookup("malloc").expect("malloc should exist");

        assert_eq!(malloc.function_name, "malloc");
        assert_eq!(malloc.safety_level, SafetyLevel::Safe);
        assert_eq!(malloc.parameter_contracts.len(), 1);
        assert!(!malloc.parameter_contracts[0].is_nullable);
        assert!(malloc.return_contract.is_some());
        assert!(malloc.side_effects.contains(&SideEffect::AllocatesMemory));
    }

    #[test]
    fn test_ffi_summary_db_lookup_free() {
        let db = FfiSummaryDb::new();
        let free = db.lookup("free").expect("free should exist");

        assert_eq!(free.function_name, "free");
        assert_eq!(free.safety_level, SafetyLevel::UnsafeRequiresContract);
        assert!(free.parameter_contracts[0].is_nullable);
        assert!(free.side_effects.contains(&SideEffect::FreesMemory));
    }

    #[test]
    fn test_ffi_summary_db_lookup_memcpy() {
        let db = FfiSummaryDb::new();
        let memcpy = db.lookup("memcpy").expect("memcpy should exist");

        assert_eq!(memcpy.function_name, "memcpy");
        assert_eq!(memcpy.parameter_contracts.len(), 3);

        // dest and src share aliasing class
        let dest_class = &memcpy.parameter_contracts[0].aliasing_class;
        let src_class = &memcpy.parameter_contracts[1].aliasing_class;
        assert_eq!(dest_class, src_class, "memcpy dest and src should share aliasing class");

        // count has no aliasing constraint but has a range
        let count = &memcpy.parameter_contracts[2];
        assert!(count.aliasing_class.is_none());
        assert!(count.valid_range.is_some());
    }

    #[test]
    fn test_ffi_summary_db_lookup_strlen() {
        let db = FfiSummaryDb::new();
        let strlen = db.lookup("strlen").expect("strlen should exist");

        assert_eq!(strlen.safety_level, SafetyLevel::Safe);
        assert!(!strlen.parameter_contracts[0].is_nullable);

        // Return contract: ret >= 0
        match &strlen.return_contract {
            Some(Formula::Ge(_, _)) => {} // expected
            other => panic!("strlen return contract should be Ge, got: {other:?}"),
        }
    }

    #[test]
    fn test_ffi_summary_db_register_custom() {
        let mut db = FfiSummaryDb::new();
        let initial_len = db.len();

        let custom = FfiSummary::new("my_custom_ffi")
            .with_param(ParamContract {
                param_index: 0,
                is_nullable: false,
                valid_range: Some((1, 100)),
                aliasing_class: None,
            })
            .with_safety(SafetyLevel::Safe);
        db.register(custom);

        assert_eq!(db.len(), initial_len + 1);
        let retrieved = db.lookup("my_custom_ffi").expect("custom summary should exist");
        assert_eq!(retrieved.safety_level, SafetyLevel::Safe);
    }

    #[test]
    fn test_generate_ffi_vcs_null_check() {
        let summary = FfiSummary::new("strlen")
            .with_param(ParamContract {
                param_index: 0,
                is_nullable: false,
                valid_range: None,
                aliasing_class: None,
            })
            .with_safety(SafetyLevel::Safe);

        let args = vec![Formula::Var("ptr".into(), Sort::Int)];
        let vcs = generate_ffi_vcs("test::call_strlen", &summary, &args, &Default::default());

        assert_eq!(vcs.len(), 1, "should generate 1 null-check VC");
        assert!(
            vcs[0].kind.description().contains("non-null"),
            "VC description should mention non-null"
        );

        // The formula should be ptr == 0 (violation: pointer is null)
        match &vcs[0].formula {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "ptr"));
                assert!(matches!(rhs.as_ref(), Formula::Int(0)));
            }
            other => panic!("expected Eq (null check), got: {other:?}"),
        }
    }

    #[test]
    fn test_generate_ffi_vcs_range_check() {
        let summary = FfiSummary::new("malloc")
            .with_param(ParamContract {
                param_index: 0,
                is_nullable: false,
                valid_range: Some((0, 1024)),
                aliasing_class: None,
            })
            .with_safety(SafetyLevel::Safe);

        let args = vec![Formula::Var("size".into(), Sort::Int)];
        let vcs = generate_ffi_vcs("test::call_malloc", &summary, &args, &Default::default());

        // Should have null check + range check
        assert_eq!(vcs.len(), 2, "should generate null-check and range-check VCs");

        // Second VC should be range violation
        let range_vc = &vcs[1];
        assert!(
            range_vc.kind.description().contains("range"),
            "VC description should mention range"
        );

        match &range_vc.formula {
            Formula::Or(clauses) => {
                assert_eq!(clauses.len(), 2, "range violation is (arg < lo) OR (arg > hi)");
            }
            other => panic!("expected Or (range violation), got: {other:?}"),
        }
    }

    #[test]
    fn test_generate_ffi_vcs_aliasing_check() {
        let summary = FfiSummary::new("memcpy")
            .with_param(ParamContract {
                param_index: 0,
                is_nullable: false,
                valid_range: None,
                aliasing_class: Some("region".into()),
            })
            .with_param(ParamContract {
                param_index: 1,
                is_nullable: false,
                valid_range: None,
                aliasing_class: Some("region".into()),
            })
            .with_safety(SafetyLevel::UnsafeRequiresContract);

        let args =
            vec![Formula::Var("dest".into(), Sort::Int), Formula::Var("src".into(), Sort::Int)];
        let vcs = generate_ffi_vcs("test::call_memcpy", &summary, &args, &Default::default());

        // 2 null checks + 1 aliasing check
        assert_eq!(vcs.len(), 3, "should generate 2 null-checks + 1 aliasing check");

        // The last VC should be the aliasing check (dest == src)
        let alias_vc = &vcs[2];
        assert!(
            alias_vc.kind.description().contains("must not alias"),
            "VC description should mention aliasing"
        );

        match &alias_vc.formula {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "dest"));
                assert!(matches!(rhs.as_ref(), Formula::Var(name, _) if name == "src"));
            }
            other => panic!("expected Eq (alias check), got: {other:?}"),
        }
    }

    #[test]
    fn test_generate_ffi_vcs_nullable_no_null_check() {
        let summary = FfiSummary::new("free")
            .with_param(ParamContract {
                param_index: 0,
                is_nullable: true,
                valid_range: None,
                aliasing_class: None,
            })
            .with_safety(SafetyLevel::UnsafeRequiresContract);

        let args = vec![Formula::Var("ptr".into(), Sort::Int)];
        let vcs = generate_ffi_vcs("test::call_free", &summary, &args, &Default::default());

        assert!(vcs.is_empty(), "nullable parameter should not generate a null-check VC");
    }

    #[test]
    fn test_generate_ffi_vcs_no_args_no_vcs() {
        let summary = FfiSummary::new("getpid").with_safety(SafetyLevel::Safe);

        let vcs = generate_ffi_vcs("test::call_getpid", &summary, &[], &Default::default());
        assert!(vcs.is_empty(), "function with no contracts should produce no VCs");
    }

    #[test]
    fn test_generate_ffi_vcs_missing_arg_skipped() {
        let summary = FfiSummary::new("strlen")
            .with_param(ParamContract {
                param_index: 5, // beyond provided args
                is_nullable: false,
                valid_range: None,
                aliasing_class: None,
            })
            .with_safety(SafetyLevel::Safe);

        let args = vec![Formula::Var("ptr".into(), Sort::Int)];
        let vcs = generate_ffi_vcs("test::call_strlen", &summary, &args, &Default::default());

        assert!(vcs.is_empty(), "contract referencing out-of-range param_index should be skipped");
    }

    #[test]
    fn test_ffi_summary_builder_pattern() {
        let summary = FfiSummary::new("custom")
            .with_param(ParamContract {
                param_index: 0,
                is_nullable: false,
                valid_range: Some((0, 255)),
                aliasing_class: None,
            })
            .with_return_contract(Formula::Ge(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .with_side_effects(vec![SideEffect::WritesGlobal("errno".into())])
            .with_safety(SafetyLevel::UnsafeRequiresContract);

        assert_eq!(summary.function_name, "custom");
        assert_eq!(summary.parameter_contracts.len(), 1);
        assert!(summary.return_contract.is_some());
        assert_eq!(summary.side_effects.len(), 1);
        assert_eq!(summary.safety_level, SafetyLevel::UnsafeRequiresContract);
    }

    #[test]
    fn test_side_effect_variants() {
        let effects = [
            SideEffect::AllocatesMemory,
            SideEffect::FreesMemory,
            SideEffect::WritesGlobal("errno".into()),
            SideEffect::ReadsGlobal("stdin".into()),
            SideEffect::CallsCallback,
            SideEffect::None,
        ];
        // All should be distinct
        for i in 0..effects.len() {
            for j in (i + 1)..effects.len() {
                assert_ne!(effects[i], effects[j], "side effects should be distinct");
            }
        }
    }

    #[test]
    fn test_generate_ffi_vcs_full_memcpy_from_db() {
        let db = FfiSummaryDb::new();
        let memcpy = db.lookup("memcpy").expect("memcpy should exist");

        let args = vec![
            Formula::Var("dest".into(), Sort::Int),
            Formula::Var("src".into(), Sort::Int),
            Formula::Var("n".into(), Sort::Int),
        ];
        let vcs = generate_ffi_vcs("main::line_42", memcpy, &args, &Default::default());

        // dest: non-null (1 VC)
        // src: non-null (1 VC)
        // n: non-null + range (2 VCs)
        // aliasing: dest != src (1 VC)
        assert_eq!(vcs.len(), 5, "memcpy should generate 5 VCs");

        // All VCs should reference the call site
        for vc in &vcs {
            assert_eq!(vc.function, "main::line_42");
        }
    }

    // -----------------------------------------------------------------------
    // apply_summary tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_apply_summary_no_return_contract_returns_true() {
        // A summary with no return contract should produce Bool(true).
        let summary = FfiSummary::new("getpid").with_safety(SafetyLevel::Safe);

        let result = apply_summary(&summary, &[]);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_apply_summary_substitutes_arg_placeholder() {
        // memcpy return contract: __ffi_ret == __ffi_arg_0
        // After apply_summary with args, __ffi_arg_0 -> actual dest arg.
        let db = FfiSummaryDb::new();
        let memcpy = db.lookup("memcpy").expect("memcpy should exist");

        let dest = Formula::Var("my_dest".into(), Sort::Int);
        let src = Formula::Var("my_src".into(), Sort::Int);
        let n = Formula::Var("my_n".into(), Sort::Int);

        let result = apply_summary(memcpy, &[dest.clone(), src, n]);

        // Should be: __ffi_ret == my_dest
        match &result {
            Formula::Eq(lhs, rhs) => {
                assert!(
                    matches!(lhs.as_ref(), Formula::Var(name, _) if name == "__ffi_ret"),
                    "LHS should be __ffi_ret, got: {lhs:?}"
                );
                assert_eq!(*rhs.as_ref(), dest, "RHS should be the actual dest arg");
            }
            other => panic!("expected Eq for memcpy return contract, got: {other:?}"),
        }
    }

    #[test]
    fn test_apply_summary_malloc_return_preserves_structure() {
        // malloc return contract: __ffi_ret == 0 OR __ffi_ret > 0
        // No __ffi_arg_N in the return contract, so args don't matter.
        let db = FfiSummaryDb::new();
        let malloc = db.lookup("malloc").expect("malloc should exist");

        let args = vec![Formula::Var("size".into(), Sort::Int)];
        let result = apply_summary(malloc, &args);

        match &result {
            Formula::Or(clauses) => {
                assert_eq!(clauses.len(), 2, "malloc return contract should have 2 clauses");
            }
            other => panic!("expected Or for malloc return contract, got: {other:?}"),
        }
    }

    #[test]
    fn test_apply_summary_strlen_return_nonneg() {
        // strlen return contract: __ffi_ret >= 0
        let db = FfiSummaryDb::new();
        let strlen = db.lookup("strlen").expect("strlen should exist");

        let args = vec![Formula::Var("s".into(), Sort::Int)];
        let result = apply_summary(strlen, &args);

        match &result {
            Formula::Ge(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "__ffi_ret"),);
                assert_eq!(*rhs.as_ref(), Formula::Int(0));
            }
            other => panic!("expected Ge for strlen return contract, got: {other:?}"),
        }
    }

    #[test]
    fn test_apply_summary_missing_arg_leaves_placeholder() {
        // If the summary references __ffi_arg_0 but no args are provided,
        // the placeholder should be left as-is.
        let summary = FfiSummary::new("identity")
            .with_return_contract(Formula::Eq(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
            ))
            .with_safety(SafetyLevel::Safe);

        let result = apply_summary(&summary, &[]);

        // __ffi_arg_0 should remain because no arg was provided
        match &result {
            Formula::Eq(_, rhs) => {
                assert!(
                    matches!(rhs.as_ref(), Formula::Var(name, _) if name == "__ffi_arg_0"),
                    "missing arg should leave placeholder, got: {rhs:?}"
                );
            }
            other => panic!("expected Eq, got: {other:?}"),
        }
    }

    #[test]
    fn test_apply_summary_multiple_arg_substitutions() {
        // Contract that references multiple args:
        // __ffi_ret == __ffi_arg_0 + __ffi_arg_1
        let summary = FfiSummary::new("add_ints")
            .with_return_contract(Formula::Eq(
                Box::new(Formula::Var("__ffi_ret".into(), Sort::Int)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("__ffi_arg_0".into(), Sort::Int)),
                    Box::new(Formula::Var("__ffi_arg_1".into(), Sort::Int)),
                )),
            ))
            .with_safety(SafetyLevel::Safe);

        let a = Formula::Var("x".into(), Sort::Int);
        let b = Formula::Var("y".into(), Sort::Int);
        let result = apply_summary(&summary, &[a.clone(), b.clone()]);

        // Should be: __ffi_ret == x + y
        match &result {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "__ffi_ret"));
                match rhs.as_ref() {
                    Formula::Add(left, right) => {
                        assert_eq!(*left.as_ref(), a);
                        assert_eq!(*right.as_ref(), b);
                    }
                    other => panic!("expected Add in RHS, got: {other:?}"),
                }
            }
            other => panic!("expected Eq, got: {other:?}"),
        }
    }

    #[test]
    fn test_apply_summary_concrete_arg_values() {
        // Substitute with concrete integer values, not just symbolic vars.
        let db = FfiSummaryDb::new();
        let memset = db.lookup("memset").expect("memset should exist");

        // memset(buf, 0, 100): return contract is __ffi_ret == __ffi_arg_0
        let buf = Formula::Int(0x1000);
        let c = Formula::Int(0);
        let n = Formula::Int(100);
        let result = apply_summary(memset, &[buf.clone(), c, n]);

        match &result {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == "__ffi_ret"));
                assert_eq!(*rhs.as_ref(), buf, "should substitute __ffi_arg_0 with buf address");
            }
            other => panic!("expected Eq, got: {other:?}"),
        }
    }

    #[test]
    fn test_ffi_summary_db_has_all_extended_builtins() {
        // Verify the full set of built-in summaries registered by register_builtins.
        let db = FfiSummaryDb::new();
        let expected = [
            "malloc",
            "free",
            "memcpy",
            "strlen",
            "printf",
            "fprintf",
            "sprintf",
            "read",
            "write",
            "calloc",
            "realloc",
            "memmove",
            "memset",
            "strcmp",
            "strncpy",
            "strcpy",
            "strcat",
            "strncat",
            "puts",
            "fopen",
            "fclose",
            "fread",
            "fwrite",
            "snprintf",
            // T6: demand-free fd/process-seam summaries.
            "close",
            "dup",
            "fcntl",
            "kill",
            "killpg",
            "waitpid",
            "getuid",
            "access",
            "getentropy",
            "poll",
            "pipe",
            "ioctl",
            // T9: #[link_name = "getuid"] Rust-decl-name alias (see register_builtins).
            "libc_getuid",
            // FFI-SCALAR-LIBC-1: integer-argument rows bound by libc identity.
            "getpid",
            "getpgrp",
            "geteuid",
            "getsid",
            "tcgetpgrp",
            "raise",
            "__error",
            "__errno_location",
        ];
        for name in &expected {
            assert!(db.lookup(name).is_some(), "missing builtin summary for `{name}`");
        }
        assert_eq!(db.len(), expected.len(), "should have exactly {} builtins", expected.len());
    }

    #[test]
    fn test_ffi_summary_db_register_overwrites() {
        // Registering a summary with the same name should overwrite the existing one.
        let mut db = FfiSummaryDb::new();
        let original = db.lookup("malloc").expect("malloc exists").clone();
        assert_eq!(original.safety_level, SafetyLevel::Safe);

        let custom_malloc = FfiSummary::new("malloc").with_safety(SafetyLevel::UnsafeUnknown);
        db.register(custom_malloc);

        let updated = db.lookup("malloc").expect("malloc still exists");
        assert_eq!(
            updated.safety_level,
            SafetyLevel::UnsafeUnknown,
            "register should overwrite existing entry"
        );
    }

    #[test]
    fn test_read_write_fd_and_count_demands_dropped() {
        // Retain T6's null/range demands, with a separate BYTE-buffer contract.
        // The old
        // fd range demand ([0, i128::MAX] on param 0) treated EBADF — an
        // errno-level runtime error — as UB and refuted every
        // runtime-provided fd; the old param-2 contract's integer "non-null"
        // check refuted the defined `write(fd, buf, 0)`.
        let db = FfiSummaryDb::new();
        for name in ["read", "write"] {
            let s = db.lookup(name).expect("summary exists");
            assert_eq!(
                s.parameter_contracts.len(),
                1,
                "`{name}` must carry exactly the buf contract, got {:?}",
                s.parameter_contracts
            );
            let buf = &s.parameter_contracts[0];
            assert_eq!(buf.param_index, 1, "`{name}` demand must be on the buffer");
            assert!(!buf.is_nullable, "`{name}` buffer stays non-null (NULL buf is UB)");
            assert!(buf.valid_range.is_none(), "`{name}` buffer carries no range");
            assert_eq!(
                s.buffer_contracts,
                vec![BufferContract { pointer_param: 1, count_param: 2 }]
            );
        }
        // write loses the WritesGlobal("fd") effect (it minted an
        // undischargeable per-call obligation; havoc is the model default).
        let write = db.lookup("write").expect("write exists");
        assert!(
            !write.side_effects.iter().any(|e| matches!(e, SideEffect::WritesGlobal(_))),
            "write must not carry WritesGlobal, got {:?}",
            write.side_effects
        );
    }

    #[test]
    fn test_ffi_buffer_contract_is_generic_and_unknown_is_not_capacity() {
        let summary = FfiSummary::new("custom_buffer")
            .with_buffer(BufferContract { pointer_param: 0, count_param: 1 });
        let fold = |vcs: Vec<VerificationCondition>| {
            assert_eq!(vcs.len(), 1, "the buffer contract must be charged by the public API");
            crate::simplify::SimplificationPipeline::default_pipeline()
                .run(vcs[0].formula.clone())
                .0
        };
        let args = |n| vec![Formula::Int(123), Formula::Int(n)];
        assert_eq!(
            fold(generate_ffi_vcs("caller", &summary, &args(1), &Default::default())),
            Formula::Bool(true)
        );
        assert_eq!(
            fold(generate_ffi_vcs("caller", &summary, &args(0), &Default::default())),
            Formula::Bool(false)
        );
        for count in [64, 65] {
            assert_eq!(
                fold(generate_ffi_vcs_with_extents(
                    "caller",
                    &summary,
                    &args(count),
                    &Default::default(),
                    &[(0, 64)].into_iter().collect()
                )),
                Formula::Bool(count > 64)
            );
        }
        assert_eq!(
            fold(generate_ffi_vcs("caller", &summary, &[], &Default::default())),
            Formula::Bool(true)
        );
    }

    #[test]
    fn test_fd_seam_summaries_are_demand_free() {
        // T6: fd-only integer calls impose NO caller demands — a bad fd or
        // signal number is errno, not UB.
        let db = FfiSummaryDb::new();
        for name in ["close", "dup", "fcntl", "kill", "killpg", "getuid", "ioctl"] {
            let s = db.lookup(name).expect("summary exists");
            assert!(
                s.parameter_contracts.is_empty(),
                "`{name}` must be demand-free, got {:?}",
                s.parameter_contracts
            );
            assert_ne!(
                s.safety_level,
                SafetyLevel::UnsafeUnknown,
                "`{name}` must not fail closed as unmodeled"
            );
            assert!(s.return_contract.is_some(), "`{name}` documents its return guarantee");
        }
        // Pointer-writing seam calls demand exactly their non-null out-pointer.
        for name in ["access", "getentropy", "poll", "pipe"] {
            let s = db.lookup(name).expect("summary exists");
            assert_eq!(s.parameter_contracts.len(), 1, "`{name}` demands only its pointer");
            assert_eq!(s.parameter_contracts[0].param_index, 0);
            assert!(!s.parameter_contracts[0].is_nullable);
        }
        // waitpid: the status out-pointer is NULLABLE (NULL opts out), so it
        // must not generate a null-check demand.
        let waitpid = db.lookup("waitpid").expect("waitpid exists");
        assert_eq!(waitpid.parameter_contracts.len(), 1);
        assert_eq!(waitpid.parameter_contracts[0].param_index, 1);
        assert!(waitpid.parameter_contracts[0].is_nullable);
        let vcs = generate_ffi_vcs(
            "test::call_waitpid",
            waitpid,
            &[
                Formula::Var("pid".into(), Sort::Int),
                Formula::Var("status".into(), Sort::Int),
                Formula::Int(0),
            ],
            &Default::default(),
        );
        assert!(vcs.is_empty(), "waitpid must impose no call-site demands, got {vcs:?}");
    }

    #[test]
    fn test_fd_seam_return_contracts() {
        // close/kill/killpg/access/getentropy/pipe: ret in [-1, 0];
        // dup/fcntl/waitpid/poll/ioctl: ret >= -1; getuid: ret >= 0.
        let db = FfiSummaryDb::new();
        let ret = Formula::Var("__ffi_ret".into(), Sort::Int);
        for name in ["close", "kill", "killpg", "access", "getentropy", "pipe"] {
            let s = db.lookup(name).expect("summary exists");
            let expected = Formula::And(vec![
                Formula::Ge(Box::new(ret.clone()), Box::new(Formula::Int(-1))),
                Formula::Le(Box::new(ret.clone()), Box::new(Formula::Int(0))),
            ]);
            assert_eq!(
                s.return_contract.as_ref(),
                Some(&expected),
                "`{name}` must guarantee ret in [-1, 0]"
            );
        }
        for name in ["dup", "fcntl", "waitpid", "poll", "ioctl"] {
            let s = db.lookup(name).expect("summary exists");
            let expected = Formula::Ge(Box::new(ret.clone()), Box::new(Formula::Int(-1)));
            assert_eq!(
                s.return_contract.as_ref(),
                Some(&expected),
                "`{name}` must guarantee ret >= -1"
            );
        }
        let getuid = db.lookup("getuid").expect("getuid exists");
        let expected = Formula::Ge(Box::new(ret.clone()), Box::new(Formula::Int(0)));
        assert_eq!(getuid.return_contract.as_ref(), Some(&expected));
    }

    // T9 (#[link_name] import alias): the `libc_getuid` alias must carry the
    // getuid contract verbatim (Safe, zero-arg, ret >= 0) under the RUST DECL
    // NAME that extraction actually emits for aterm-types dirs.rs's
    // `#[link_name = "getuid"] fn libc_getuid();` import — extraction drops
    // link_name, so the alias name is the only key that can ever bind.
    #[test]
    fn test_libc_getuid_link_name_alias_binds_getuid_contract() {
        let db = FfiSummaryDb::new();
        let alias = db.lookup("libc_getuid").expect("libc_getuid alias exists");
        let getuid = db.lookup("getuid").expect("getuid exists");
        assert_eq!(alias.function_name, "libc_getuid");
        assert_eq!(alias.return_contract, getuid.return_contract);
        assert_eq!(alias.safety_level, getuid.safety_level);
        assert_eq!(alias.safety_level, SafetyLevel::Safe);
        assert!(alias.parameter_contracts.is_empty());
        // The end-to-end route: the extracted callee is `dirs::libc_getuid`;
        // `generate_call_site_vcs` looks up its LAST SEGMENT. With the alias
        // bound and safety Safe, the fail-closed "unmodeled FFI call" VC is no
        // longer minted.
        let vcs = generate_call_site_vcs(
            "caller",
            "dirs::libc_getuid",
            &[],
            "_0",
            &SourceSpan::default(),
            &db,
            &Default::default(),
        );
        assert!(
            vcs.iter().all(|vc| !format!("{:?}", vc.kind).contains("unmodeled")),
            "aliased foreign import must not fail closed as unmodeled: {vcs:#?}"
        );
    }

    #[test]
    fn test_apply_summary_read_return_contract() {
        // read returns -1 <= ret <= count. count is arg 2, here 1024, so the
        // applied contract is And([__ffi_ret >= -1, __ffi_ret <= 1024]).
        let db = FfiSummaryDb::new();
        let read = db.lookup("read").expect("read should exist");

        let args = vec![
            Formula::Int(0),                       // fd
            Formula::Var("buf".into(), Sort::Int), // buf
            Formula::Int(1024),                    // count
        ];
        let result = apply_summary(read, &args);

        // Should be: __ffi_ret >= -1  AND  __ffi_ret <= 1024 (arg_2 substituted).
        let Formula::And(conjuncts) = &result else {
            panic!("expected And for read return contract, got: {result:?}");
        };
        assert_eq!(conjuncts.len(), 2, "expected two conjuncts, got: {result:?}");
        assert!(
            conjuncts.iter().any(|c| matches!(c,
                Formula::Ge(lhs, rhs)
                    if matches!(lhs.as_ref(), Formula::Var(n, _) if n == "__ffi_ret")
                        && **rhs == Formula::Int(-1))),
            "missing `__ffi_ret >= -1`: {result:?}"
        );
        assert!(
            conjuncts.iter().any(|c| matches!(c,
                Formula::Le(lhs, rhs)
                    if matches!(lhs.as_ref(), Formula::Var(n, _) if n == "__ffi_ret")
                        && **rhs == Formula::Int(1024))),
            "missing `__ffi_ret <= count(1024)` (arg_2 substitution): {result:?}"
        );
    }

    // ---------------------------------------------------------------------
    // FFI-SCALAR-LIBC-1: the identity-bound integer-argument libc rows
    // ---------------------------------------------------------------------

    /// A key as the extractor mints it for a call to `leaf`, declared in an `extern`
    /// block of the crate `krate` and linking to `link` (`None` = a declaration of
    /// the crate under verification, or no foreign function at all).
    fn scalar_key(krate: &str, leaf: Option<&str>, link: Option<&str>) -> CalleeKey {
        CalleeKey {
            sysroot_item: None,
            krate_is_real_sysroot: false,
            // The crates.io `libc` shares its name with the sysroot's copy.
            krate_name_is_ambiguous: true,
            stable_crate_id: 0x5ca1,
            krate_name: krate.to_string(),
            foreign_block_leaf: leaf.map(str::to_string),
            upstream_foreign_link_symbol: link.map(str::to_string),
            diverging_entry: None,
        }
    }

    fn libc_key(symbol: &str) -> CalleeKey {
        scalar_key("libc", Some(symbol), Some(symbol))
    }

    /// The rows a call gets: the production call-site entry point with the call's
    /// own identity.
    fn call_rows(
        callee: &str,
        arg_count: usize,
        is_foreign: bool,
        key: Option<&CalleeKey>,
    ) -> Vec<VerificationCondition> {
        let args: Vec<Formula> =
            (0..arg_count).map(|i| Formula::Var(format!("a{i}"), Sort::Int)).collect();
        crate::ffi_vcgen::generate_call_site_vcs_with_extents(
            "caller",
            callee,
            &args,
            "_0",
            &SourceSpan::default(),
            &FfiSummaryDb::new(),
            (&Default::default(), &Default::default()),
            crate::ffi_vcgen::CallIdentity { is_foreign, key, arg_count },
        )
    }

    fn is_unmodeled(rows: &[VerificationCondition]) -> bool {
        rows.len() == 1
            && rows[0].formula == Formula::Bool(true)
            && rows[0].kind.description().contains("unmodeled FFI call: no summary")
    }

    #[test]
    fn scalar_libc_rows_are_registered_safe_with_no_parameter_contract() {
        let db = FfiSummaryDb::new();
        let expected = [
            ("getpid", 0),
            ("getpgrp", 0),
            ("geteuid", 0),
            ("getsid", 1),
            ("tcgetpgrp", 1),
            ("raise", 1),
            ("__error", 0),
            ("__errno_location", 0),
        ];
        assert_eq!(scalar_libc_summaries().len(), expected.len());
        for (name, arity) in expected {
            let s = db.lookup(name).unwrap_or_else(|| panic!("`{name}` is registered"));
            assert_eq!(s.safety_level, SafetyLevel::Safe, "`{name}`");
            assert!(s.parameter_contracts.is_empty(), "`{name}` reads no argument memory");
            assert!(s.buffer_contracts.is_empty(), "`{name}`");
            assert_eq!(s.side_effects, vec![SideEffect::None], "`{name}`: no allocation effect");
            assert_eq!(
                s.binding,
                SummaryBinding::UpstreamLibcSymbol { arity },
                "`{name}` binds only by libc identity"
            );
        }
    }

    /// Positive control, then each identity component removed in turn. Every
    /// negative keeps the fail-closed `unmodeled FFI call` row the call had before
    /// the row existed.
    #[test]
    fn scalar_libc_row_binds_only_the_upstream_libc_symbol_at_its_arity() {
        let callee = "libc::unix::{extern#0}::getsid";
        // Positive: a foreign call to libc's own `getsid` at arity 1 mints nothing.
        let key = libc_key("getsid");
        assert!(call_rows(callee, 1, true, Some(&key)).is_empty());
        // Positive control for the instrument: the same call with NO identity is
        // the unmodeled row, so an empty result above is the binding, not a lane
        // that never mints.
        assert!(is_unmodeled(&call_rows(callee, 1, true, None)));

        let negatives: [(&str, bool, Option<CalleeKey>, usize); 7] = [
            ("not foreign (a Rust fn of that name)", false, Some(libc_key("getsid")), 1),
            ("no key (fn pointer, synthetic MIR)", true, None, 1),
            ("wrong arity", true, Some(libc_key("getsid")), 2),
            (
                "a crate other than libc",
                true,
                Some(scalar_key("mylibc", Some("getsid"), Some("getsid"))),
                1,
            ),
            (
                "declared by the crate under verification (no upstream link symbol)",
                true,
                Some(scalar_key("libc", Some("getsid"), None)),
                1,
            ),
            (
                "`#[link_name = \"malloc\"] fn getsid` (links another symbol)",
                true,
                Some(scalar_key("libc", Some("getsid"), Some("malloc"))),
                1,
            ),
            (
                "`#[link_name = \"getsid\"] fn other` (Rust name differs)",
                true,
                Some(scalar_key("libc", Some("other"), Some("getsid"))),
                1,
            ),
        ];
        for (label, is_foreign, key, arity) in negatives {
            let rows = call_rows(callee, arity, is_foreign, key.as_ref());
            assert!(is_unmodeled(&rows), "{label}: must keep the unmodeled row, got {rows:#?}");
        }
    }

    /// Every new row needs the identity; zero-arity rows refuse an argument.
    #[test]
    fn every_scalar_libc_row_requires_identity_and_arity() {
        for s in scalar_libc_summaries() {
            let SummaryBinding::UpstreamLibcSymbol { arity } = s.binding else {
                panic!("`{}` must be identity-bound", s.function_name);
            };
            let name = s.function_name.as_str();
            let callee = format!("libc::{name}");
            let key = libc_key(name);
            assert!(call_rows(&callee, arity, true, Some(&key)).is_empty(), "`{name}` binds");
            assert!(is_unmodeled(&call_rows(&callee, arity, true, None)), "`{name}` unkeyed");
            assert!(
                is_unmodeled(&call_rows(&callee, arity + 1, true, Some(&key))),
                "`{name}` at arity {}",
                arity + 1
            );
            assert!(
                is_unmodeled(&call_rows(&callee, arity, false, Some(&key))),
                "`{name}` not foreign"
            );
        }
    }

    /// The legacy rows keep binding by declaration name, keyed or not: the change
    /// restricts only the rows it adds.
    #[test]
    fn decl_name_rows_bind_as_before() {
        let db = FfiSummaryDb::new();
        let getuid = db.lookup("getuid").expect("getuid exists");
        assert_eq!(getuid.binding, SummaryBinding::DeclName);
        assert!(getuid.binds_call(false, None, 7));
        assert!(call_rows("dirs::libc_getuid", 0, true, None).is_empty());
        let local = scalar_key("dirs", Some("libc_getuid"), None);
        assert!(call_rows("dirs::{extern#0}::libc_getuid", 0, true, Some(&local)).is_empty());
    }
}
