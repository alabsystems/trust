#!/usr/bin/env python3
"""Structural single-source check for the native-contract support crates.

The historical harness still invokes this file under its floatbits-specific
name. It now accepts any of the four migrated crate roots. The retired
contracts.rs path must be absent: every native clause and its function body
live in one `trust_contract_fn!` invocation in lib.rs. The compiler-owned
`cfg(trust_verify)` selects only the expansion syntax, never an implementation.

Usage:
  trust_floatbits_twin_parity.py <lib.rs> <retired-contracts.rs>
  trust_floatbits_twin_parity.py --materialize-consumer-candidate \
      <repo-root> <candidate-root> <consumer-package>

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
"""

from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
from typing import Optional

try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10 and older: refuse_named_build_program scans lines
    tomllib = None  # type: ignore[assignment]


EXPECTED_BY_CRATE = {
    "trust-intbound": {
        "width_is_supported": "ensures result <= 1",
        "signed_max": "ensures result <= 9223372036854775807",
        "signed_min_magnitude": "ensures result <= 9223372036854775808",
        "clamp_width": "ensures result <= 64 ensures result <= w",
        "clamp_to_max": "ensures result <= value ensures result <= limit",
        "clamp_unsigned_to_width": "ensures result <= value",
        "unsigned_fits": "ensures result <= 1",
        "signed_fits_nonneg": "ensures result <= 1",
        "signed_fits_magnitude": "ensures result <= 1",
    },
    "trust-widthconv": {
        "width_supported": "ensures result <= 1",
        "conversion_code": "ensures result <= 3",
        "extension_bits": "ensures result <= 120 ensures result <= dst_width",
        "shift_mask": "ensures result <= 127 ensures result <= target_width",
        "join_width": "ensures result >= left_width ensures result >= right_width",
    },
    "trust-budget": {
        "per_job_bytes": "ensures result <= budget_bytes",
        "megabytes_of": "ensures result <= bytes ensures result <= 17592186044415",
        "split_budget_ms": "ensures result <= total_ms ensures total_ms > 0 ==> result > 0",
        "process_ceiling_mb": "ensures result >= budget_mb ensures result >= 2048",
    },
    "trust-floatbits": {
        "format_supported": "ensures result <= 1",
        "exponent_field_width": "ensures result <= 11",
        "fraction_field_width": "ensures result <= 52",
        "magnitude_field_width": "ensures result <= 63",
        "magnitude_mask": "ensures result <= 9223372036854775807",
        "nonfinite_exponent": "ensures result <= 2047",
        "binary64_magnitude_bits": "ensures result <= 9223372036854775807",
        "binary64_biased_exponent": "ensures result <= 2047",
        "exp2_binary64_supported": "ensures result <= 1",
        "exp2_binary64_bits": (
            "ensures result <= 9218868437227405312 "
            "ensures result >= 4607182418800017408"
        ),
    },
}

NATIVE_TEMPLATE = r'''#[cfg(trust_verify)]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
}'''

STOCK_TEMPLATE = r'''#[cfg(not(trust_verify))]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
}'''

BUILD_PROGRAM = '''fn main() {
println!("cargo::rustc-check-cfg=cfg(trust_verify)");
}'''

INVOCATION = re.compile(
    r"pub fn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*"
    r"\([^)]*\)\s*->\s*[A-Za-z_][A-Za-z0-9_]*\s*"
    r"clauses\s*\[(?P<clauses>[^]]+)\]",
    re.DOTALL,
)


class Refusal(Exception):
    pass


def replace_list(text: str, key: str, replacement: str) -> str:
    """Replace the one top-level `key = [ ... ]` list (at a line start) of a manifest."""
    found = list(re.finditer(rf"(?m)^{re.escape(key)} = \[\n(?:.*\n)*?\]\n", text))
    if len(found) != 1:
        raise Refusal(f"candidate workspace {key} list is absent, unterminated or not unique")
    return text[: found[0].start()] + replacement + text[found[0].end() :]


def materialize_consumer_candidate(
    repo_root: Path, candidate: Path, consumer: str
) -> None:
    """Create an inode-independent mutation-G workspace without copying sources."""
    if consumer not in {"trust-ir-bridge", "trust-router", "trust-coordinator", "trust-vcgen"}:
        raise Refusal(f"unsupported mutation-G consumer: {consumer}")
    if not candidate.is_dir() or any(candidate.iterdir()):
        raise Refusal(f"candidate root is absent or not empty: {candidate}")

    (candidate / ".trust-mutation-candidate").write_text(
        "owned by strict mutation G\n", encoding="utf-8"
    )
    # The workspace manifest and its lock live at the repository root (one
    # workspace for the compiler, the developer crates and Targo).
    tracked = subprocess.check_output(
        [
            "git",
            "-C",
            str(repo_root),
            "ls-files",
            "-z",
            "--",
            "Cargo.toml",
            "Cargo.lock",
            "crates",
            ".cargo/config.toml",
        ]
    )
    for raw in tracked.split(b"\0"):
        if not raw:
            continue
        relative = Path(os.fsdecode(raw))
        source = repo_root / relative
        # A staged deletion is absent from the worktree and must remain absent
        # from the candidate even if the index still names it.
        if not source.is_file():
            continue
        destination = candidate / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source.name in {"Cargo.toml", "Cargo.lock"} or relative == Path(
            ".cargo/config.toml"
        ):
            shutil.copy2(source, destination)
        else:
            os.symlink(source, destination)

    for name in ("first-party", "vendor", "compiler"):
        source = repo_root / name
        if not source.is_dir():
            raise Refusal(f"candidate dependency root is absent: {source}")
        os.symlink(source, candidate / name)

    # Resolve only the consumer graph. Retaining the authoritative dependency
    # and patch tables makes this a candidate of the workspace, while avoiding
    # unrelated members and a custom-Cargo duplicate-edge panic. The
    # default-members list names members this candidate drops, which Cargo
    # refuses, so it goes too.
    workspace = candidate / "Cargo.toml"
    if not workspace.is_file():
        raise Refusal(f"candidate workspace manifest is absent: {workspace}")
    text = workspace.read_text(encoding="utf-8")
    text = replace_list(text, "members", f'members = ["crates/{consumer}"]\n')
    text = replace_list(text, "default-members", "")
    workspace.write_text(text, encoding="utf-8")

    # The default trust-ir-bridge build never enables this rustc-private edge.
    # The referenced package is deliberately excluded from the crates workspace
    # and belongs to the outer compiler workspace, which this isolated candidate
    # does not clone. Removing the inactive edge preserves the measured default
    # consumer while preventing resolution from escaping the candidate.
    # Normalize this copied manifest for every consumer graph: trust-router and
    # trust-vcgen both reach trust-ir-bridge transitively even when it is not the
    # top-level candidate package.
    manifest = candidate / "crates/trust-ir-bridge/Cargo.toml"
    text = manifest.read_text(encoding="utf-8")
    for inactive in (
        'compiler-context = ["dep:trust-mir-extract"]\n',
        'trust-mir-extract = { path = "../trust-mir-extract", optional = true }\n',
    ):
        if text.count(inactive) != 1:
            raise Refusal(f"inactive compiler edge anchor drifted: {inactive.strip()}")
        text = text.replace(inactive, "")
    manifest.write_text(text, encoding="utf-8")


def normalized(value: str) -> str:
    return " ".join(value.split())


def layout_normalized(value: str) -> str:
    return "\n".join(line.strip() for line in value.strip().splitlines())


def rust_code_without_comments(value: str, *, mask_strings: bool = False) -> str:
    """Remove nested comments; optionally mask string contents for code scans."""
    def literal(value: str) -> str:
        if not mask_strings:
            return value
        return "".join("\n" if char == "\n" else " " for char in value)

    result = []
    index = 0
    while index < len(value):
        if value.startswith("//", index):
            end = value.find("\n", index)
            if end == -1:
                result.append(" ")
                break
            result.append(" " * (end - index))
            index = end
            continue
        if value.startswith("/*", index):
            depth = 1
            result.append("  ")
            index += 2
            while index < len(value) and depth:
                if value.startswith("/*", index):
                    depth += 1
                    result.append("  ")
                    index += 2
                elif value.startswith("*/", index):
                    depth -= 1
                    result.append("  ")
                    index += 2
                else:
                    result.append("\n" if value[index] == "\n" else " ")
                    index += 1
            continue

        boundary = index == 0 or not (
            value[index - 1].isalnum() or value[index - 1] == "_"
        )
        raw = re.match(r'(?:br|cr|r)(?P<hashes>#{0,255})"', value[index:])
        if boundary and raw is not None:
            terminator = '"' + raw.group("hashes")
            end = value.find(terminator, index + raw.end())
            if end == -1:
                result.append(value[index:])
                break
            end += len(terminator)
            result.append(literal(value[index:end]))
            index = end
            continue
        if value[index] == '"':
            end = index + 1
            escaped = False
            while end < len(value):
                char = value[end]
                if char == '"' and not escaped:
                    end += 1
                    break
                if char == "\\" and not escaped:
                    escaped = True
                else:
                    escaped = False
                end += 1
            result.append(literal(value[index:end]))
            index = end
            continue
        result.append(value[index])
        index += 1
    return "".join(result)


def build_program(value: str) -> str:
    code = rust_code_without_comments(value)
    return "\n".join(line.strip() for line in code.splitlines() if line.strip())


# A line that may spell the `build` key: bare, quoted, as a dotted segment
# (`package.build`) or inside an inline table (`package = { build = ... }`).
BUILD_KEY_SPELLING = re.compile(r"""(?:^|[\s{,.])["']?build["']?\s*=""")
# A key holding a backslash may be an escaped spelling of `build` or `package`.
ESCAPED_KEY = re.compile(r"^[^=]*\\[^=]*=")


def refuse_named_build_program(manifest_path: Path, text: str) -> None:
    """Refuse a manifest whose `[package] build` is anything but absent or `false`.

    `build = true` and `build = "build.rs"` are refused too: the rule is the
    two spellings that leave build.rs as the only program Cargo can run. With
    tomllib (Python 3.11+) the key is read as Cargo reads it. Without it the
    raw lines are scanned, and every line that could spell the key in any TOML
    form, or that has an escaped key, is refused unless it is exactly
    `build = false`; that scan refuses some manifests Cargo would accept, never
    the reverse.
    """
    if tomllib is not None:
        try:
            manifest = tomllib.loads(text)
        except tomllib.TOMLDecodeError as error:
            raise Refusal(f"{manifest_path} is not TOML: {error}") from error
        package = manifest.get("package")
        if not isinstance(package, dict):
            raise Refusal(f"{manifest_path} has no [package] table")
        if "build" in package and package["build"] is not False:
            raise Refusal(
                f"{manifest_path} names a build script (build = {package['build']!r}); "
                "only build.rs is checked"
            )
        return
    for line in text.splitlines():
        stripped = line.strip()
        if not (BUILD_KEY_SPELLING.search(stripped) or ESCAPED_KEY.search(stripped)):
            continue
        if not re.fullmatch(r"build\s*=\s*false\s*(?:#.*)?", stripped):
            raise Refusal(
                f"{manifest_path} names a build script or an escaped key ({stripped}); "
                "only build.rs is checked, and without Python 3.11's tomllib any "
                "spelling but `build = false` is refused"
            )


def crate_build_text(crate_root: Path) -> Optional[str]:
    """The crate's build.rs, or None when the crate has no build script.

    No build script is the stronger form: nothing can select or probe the
    verification surface, and the workspace `[lints.rust] unexpected_cfgs`
    declares `cfg(trust_verify)` (c133258d3c7 moved three of the four crates
    there). Only build.rs is read, so a `[package] build` key naming any other
    program is refused rather than left unchecked.
    """
    manifest_path = crate_root / "Cargo.toml"
    refuse_named_build_program(manifest_path, manifest_path.read_text(encoding="utf-8"))
    build_path = crate_root / "build.rs"
    if not build_path.exists():
        return None
    return build_path.read_text(encoding="utf-8")


def replace_nth(value: str, old: str, new: str, occurrence: int) -> str:
    starts = [match.start() for match in re.finditer(re.escape(old), value)]
    if len(starts) <= occurrence:
        raise Refusal(
            f"self-control fixture has {len(starts)} occurrences of {old!r}; "
            f"needs index {occurrence}"
        )
    start = starts[occurrence]
    return value[:start] + new + value[start + len(old) :]


def validate(
    text: str,
    retired_contracts: Optional[Path],
    crate_name: str,
    build_text: Optional[str],
) -> None:
    expected = EXPECTED_BY_CRATE.get(crate_name)
    if expected is None:
        raise Refusal(f"no authoritative contract census for crate {crate_name!r}")
    if retired_contracts is not None and retired_contracts.exists():
        raise Refusal(
            f"{retired_contracts} still exists; a second implementation surface remains"
        )
    commentless = rust_code_without_comments(text)
    code = rust_code_without_comments(text, mask_strings=True)
    forbidden = {
        "trust_native_contracts": "retired build-selected cfg",
        'include!("contracts.rs")': "retired duplicate-source include",
        "cargo::rustc-cfg": "crate source must not mint its verification cfg",
    }
    for token, label in forbidden.items():
        if token in commentless:
            raise Refusal(f"{label} is still present: {token}")

    if len(re.findall(r"\btrust_verify\b", code)) != 2:
        raise Refusal(
            "trust_verify may occur in code only in the two canonical macro selectors"
        )

    if build_text is not None and build_program(build_text) != BUILD_PROGRAM:
        raise Refusal(
            "build.rs is not the check-cfg-only program; it may select or probe "
            "the verification surface"
        )
    if code.count("#[cfg(trust_verify)]") != 1:
        raise Refusal("expected exactly one native cfg(trust_verify) macro definition")
    if code.count("#[cfg(not(trust_verify))]") != 1:
        raise Refusal("expected exactly one stock cfg(not(trust_verify)) macro definition")
    if code.count("macro_rules! trust_contract_fn") != 2:
        raise Refusal("expected exactly two trust_contract_fn macro definitions")

    source_layout = layout_normalized(code)
    if source_layout.count(layout_normalized(NATIVE_TEMPLATE)) != 1:
        raise Refusal("native macro template drifted: clauses and body are not emitted exactly")
    if source_layout.count(layout_normalized(STOCK_TEMPLATE)) != 1:
        raise Refusal("stock macro template drifted: the one authored body is not emitted exactly")
    if code.count("trust_contract_fn! {") != len(expected):
        raise Refusal(
            f"expected {len(expected)} contract invocations, found "
            f"{code.count('trust_contract_fn! {')}"
        )

    found: dict[str, str] = {}
    for match in INVOCATION.finditer(code):
        name = match.group("name")
        if name in found:
            raise Refusal(f"duplicate authored contract body: {name}")
        found[name] = normalized(match.group("clauses"))

    if list(found) != list(expected):
        missing = sorted(set(expected) - set(found))
        extra = sorted(set(found) - set(expected))
        raise Refusal(
            "contract census/order mismatch: "
            f"missing={missing}, extra={extra}, found={list(found)!r}"
        )

    for name, clauses in expected.items():
        name_pattern = rf"\bpub\s+fn\s+{re.escape(name)}\s*\("
        if len(re.findall(name_pattern, code)) != 1:
            raise Refusal(f"{name} does not have exactly one authored function body")
        if found[name] != normalized(clauses):
            raise Refusal(
                f"{name} clause drift: expected {normalized(clauses)!r}, "
                f"found {found[name]!r}"
            )


def require_rejected(
    label: str, text: str, crate_name: str, build_text: Optional[str]
) -> None:
    try:
        validate(text, None, crate_name, build_text)
    except Refusal:
        return
    raise Refusal(f"self-control {label!r} was accepted")


def main() -> None:
    if len(sys.argv) == 5 and sys.argv[1] == "--materialize-consumer-candidate":
        materialize_consumer_candidate(
            Path(sys.argv[2]), Path(sys.argv[3]), sys.argv[4]
        )
        return
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    source = Path(sys.argv[1])
    retired = Path(sys.argv[2])
    crate_name = source.parent.parent.name
    text = source.read_text(encoding="utf-8")
    build_text = crate_build_text(source.parent.parent)
    validate(text, retired, crate_name, build_text)
    # The build-script controls mutate the crate's own build.rs, or, for a
    # crate with none, the one program a build.rs may be: either way they show
    # that a build script which mints or hides the cfg is refused.
    control_build = BUILD_PROGRAM if build_text is None else build_text

    expected = EXPECTED_BY_CRATE[crate_name]
    code = rust_code_without_comments(text, mask_strings=True)
    first = next(iter(expected))
    duplicate_match = next(
        match for match in INVOCATION.finditer(code) if match.group("name") == first
    )
    duplicated = text + "\ntrust_contract_fn! {\n" + duplicate_match.group(0) + "\n{}\n}\n"
    require_rejected("duplicate body", duplicated, crate_name, build_text)
    require_rejected(
        "commented-out contract invocation",
        text.replace(
            "trust_contract_fn! {", "/* trust_contract_fn! { */", 1
        ),
        crate_name,
        build_text,
    )
    require_rejected(
        "string-spoofed contract invocation",
        text.replace(
            "trust_contract_fn! {",
            'const __CONTRACT_SPOOF: &str = "trust_contract_fn! {";',
            1,
        ),
        crate_name,
        build_text,
    )
    require_rejected(
        "missing native contract",
        text.replace(f"clauses [{expected[first]}]", "clauses []", 1),
        crate_name,
        build_text,
    )
    require_rejected(
        "wrong compiler cfg",
        text.replace("#[cfg(trust_verify)]", "#[cfg(any())]", 1),
        crate_name,
        build_text,
    )
    require_rejected(
        "native clause erasure",
        text.replace("$($clauses)+", "", 1),
        crate_name,
        build_text,
    )
    body_token = "{ $($body)* }"
    require_rejected(
        "native body divergence",
        replace_nth(text, body_token, "{ 0 }", 0),
        crate_name,
        build_text,
    )
    require_rejected(
        "stock body divergence",
        replace_nth(text, body_token, "{ 0 }", 1),
        crate_name,
        build_text,
    )
    swapped = text.replace("#[cfg(trust_verify)]", "#[cfg(__trust_swap)]", 1)
    swapped = swapped.replace(
        "#[cfg(not(trust_verify))]", "#[cfg(trust_verify)]", 1
    )
    swapped = swapped.replace("#[cfg(__trust_swap)]", "#[cfg(not(trust_verify))]", 1)
    require_rejected("cfg arm swap", swapped, crate_name, build_text)
    require_rejected(
        "hidden alternate cfg use",
        text.replace(
            "trust_contract_fn! {",
            "#[cfg(any(trust_verify))]\nconst __LANE_IMPL_DRIFT: u8 = 1;\n\n"
            "trust_contract_fn! {",
            1,
        ),
        crate_name,
        build_text,
    )
    require_rejected(
        "build-script cfg minting",
        text,
        crate_name,
        control_build.replace("rustc-check-cfg", "rustc-cfg"),
    )
    require_rejected(
        "invalid Cargo directive whitespace",
        text,
        crate_name,
        control_build.replace("cargo::rustc-check-cfg", "cargo ::rustc-check-cfg"),
    )
    require_rejected(
        "split build-script identifier",
        text,
        crate_name,
        control_build.replace("fn main()", "fn ma in()"),
    )

    print(
        f"       {crate_name}: {len(expected)} native contracts, "
        f"{len(expected)} singly-authored bodies; 13 structural controls rejected"
    )


if __name__ == "__main__":
    try:
        main()
    except (OSError, Refusal, subprocess.CalledProcessError) as error:
        raise SystemExit(f"REFUSE: {error}")
