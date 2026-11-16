"""Pure structural checks for the stage0 producer's existing Bootstrap step API.

Source reads, policy selection and public entry points remain in prepare.py.
Its explicit helper arguments preserve that module's replaceable test seams.
"""

from __future__ import annotations

# Bootstrap's command-line step API, spelled as this checkout's
# src/bootstrap/src/core/builder/mod.rs spells it. The 2026-10-16 upstream port
# (60669f9fc2, rust-lang/rust bf9448e4) split command-line registration
# (`should_run`, `make_run`, `IS_HOST`) off `Step` into `CommandLineStep`, and
# `Builder::get_step_descriptions` now returns `Vec<CommandLineStepDescription>`
# built by `CommandLineStepDescription::from::<S: CommandLineStep>`.
#
# The retired spelling (`impl Step for X`, `Vec<StepDescription>`) is
# deliberately NOT accepted. This file audits the checkout it ships in
# (`repo_root()`), and in that checkout `Step` declares no `should_run`: an
# `impl Step for X { fn should_run .. }` is not reachable from `describe!`, so
# admitting it would let a helper or decoy impl stand in for the registration
# x.py actually consults. `rust_declares_command_line_step_api` pins this
# spelling against builder/mod.rs, so the next upstream rename is reported as
# API drift instead of being misread as eleven unregistered producer aliases.
BOOTSTRAP_COMMAND_LINE_STEP_TRAIT = "CommandLineStep"
BOOTSTRAP_COMMAND_LINE_STEP_DESCRIPTION = "CommandLineStepDescription"
BOOTSTRAP_STEP_API_DRIFT_ERROR = (
    "bootstrap command-line step API drifted from the spelling the producer "
    "preflight parses: src/bootstrap/src/core/builder/mod.rs must declare a root "
    f"`trait {BOOTSTRAP_COMMAND_LINE_STEP_TRAIT}` with "
    "`fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_>;` and "
    f"`{BOOTSTRAP_COMMAND_LINE_STEP_DESCRIPTION}::from::"
    f"<S: {BOOTSTRAP_COMMAND_LINE_STEP_TRAIT}>` taking `S::should_run`; re-read "
    "bootstrap and update src/tools/trust-stage0-dist/prepare.py"
)
# These two producers intentionally register a source path and both the owned
# and compatibility aliases in one returned ShouldRun chain. Whole-file
# substring checks cannot authenticate that relationship: a matching comment,
# string, helper, or different Step (including a plain `impl Step for` helper
# under the retired spelling) would otherwise satisfy the audit. Keep the exact
# `impl CommandLineStep for <Step>`/body contract here and parse it
# structurally below.
STAGE0_DIST_PRODUCER_EXACT_SHOULD_RUN = {
    "trustc": (
        "Rustc",
        'run.path("compiler/rustc").alias("trustc").alias("rustc")',
    ),
    "trust-std": (
        "Std",
        'run.path("library/std").alias("trust-std").alias("rust-std")',
    ),
}
def _rust_tokens(source: str) -> tuple[str, ...] | None:
    """Tokenize enough Rust to authenticate a small, exact method body.

    Comments and string/character contents must not become executable-looking
    tokens: producer registration is a fail-closed source audit, so a decoy in
    either must never satisfy it. This is deliberately not a general Rust
    parser; malformed or unterminated lexical constructs return ``None``.
    """

    tokens: list[str] = []
    index = 0
    length = len(source)
    while index < length:
        char = source[index]
        if char.isspace():
            index += 1
            continue

        if source.startswith("//", index):
            newline = source.find("\n", index + 2)
            index = length if newline == -1 else newline + 1
            continue
        if source.startswith("/*", index):
            depth = 1
            index += 2
            while index < length and depth:
                if source.startswith("/*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                return None
            continue

        raw_prefix = None
        for prefix in ("br", "cr", "r"):
            if not source.startswith(prefix, index):
                continue
            cursor = index + len(prefix)
            while cursor < length and source[cursor] == "#":
                cursor += 1
            if cursor < length and source[cursor] == '"':
                raw_prefix = (cursor - index - len(prefix), cursor)
                break
        if raw_prefix is not None:
            hashes, opening_quote = raw_prefix
            terminator = '"' + "#" * hashes
            end = source.find(terminator, opening_quote + 1)
            if end == -1:
                return None
            end += len(terminator)
            tokens.append(source[index:end])
            index = end
            continue

        string_prefix = (
            1
            if char in {"b", "c"}
            and index + 1 < length
            and source[index + 1] == '"'
            else 0
        )
        if char == '"' or string_prefix:
            start = index
            index += string_prefix + 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                    continue
                if source[index] == '"':
                    index += 1
                    tokens.append(source[start:index])
                    break
                index += 1
            else:
                return None
            continue

        if char == "'":
            # Preserve lifetimes as punctuation + identifier, but collapse
            # character literals so braces/comment markers inside them cannot
            # perturb structural matching.
            if index + 2 < length and source[index + 2] == "'":
                tokens.append(source[index : index + 3])
                index += 3
                continue
            if (
                index + 3 < length
                and source[index + 1] == "\\"
                and source[index + 3] == "'"
            ):
                tokens.append(source[index : index + 4])
                index += 4
                continue

        if char.isalpha() or char == "_":
            end = index + 1
            while end < length and (source[end].isalnum() or source[end] == "_"):
                end += 1
            tokens.append(source[index:end])
            index = end
            continue

        tokens.append(char)
        index += 1

    return tuple(tokens)


def _matching_rust_delimiter(tokens: tuple[str, ...], opening: int) -> int | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    if opening >= len(tokens) or tokens[opening] not in pairs:
        return None
    stack = [pairs[tokens[opening]]]
    for index in range(opening + 1, len(tokens)):
        token = tokens[index]
        if token in pairs:
            stack.append(pairs[token])
        elif token in pairs.values():
            if token != stack[-1]:
                return None
            stack.pop()
            if not stack:
                return index
    return None


def _rust_delimiter_depths(tokens: tuple[str, ...]) -> tuple[int, ...] | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = set(pairs.values())
    stack: list[str] = []
    depths: list[int] = []
    for token in tokens:
        depths.append(len(stack))
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or token != stack[-1]:
                return None
            stack.pop()
    return None if stack else tuple(depths)


def _rust_comma_separated_items(
    tokens: tuple[str, ...],
) -> tuple[tuple[str, ...], ...] | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = set(pairs.values())
    stack: list[str] = []
    items: list[tuple[str, ...]] = []
    start = 0
    for index, token in enumerate(tokens):
        if token in pairs:
            stack.append(pairs[token])
        elif token in closing:
            if not stack or token != stack[-1]:
                return None
            stack.pop()
        elif token == "," and not stack:
            item = tokens[start:index]
            if not item:
                return None
            items.append(item)
            start = index + 1
    if stack:
        return None
    final_item = tokens[start:]
    if final_item:
        items.append(final_item)
    return tuple(items)


def _rust_is_simple_path(tokens: tuple[str, ...]) -> bool:
    if not tokens or not (tokens[0][0].isalpha() or tokens[0][0] == "_"):
        return False
    cursor = 1
    while cursor < len(tokens):
        if cursor + 2 >= len(tokens) or tokens[cursor : cursor + 2] != (":", ":"):
            return False
        segment = tokens[cursor + 2]
        if not segment or not (segment[0].isalpha() or segment[0] == "_"):
            return False
        cursor += 3
    return True


def rust_step_returns_exact_should_run(
    source: str, step_type: str, expression: str, step_trait: str,
    _rust_tokens, _rust_delimiter_depths, _matching_rust_delimiter,
) -> bool:
    """Require one root ``impl CommandLineStep for <step_type>`` whose
    ``should_run`` body is exactly ``expression``."""

    source_tokens = _rust_tokens(source)
    expected_tokens = _rust_tokens(expression)
    if source_tokens is None or expected_tokens is None:
        return False
    delimiter_depths = _rust_delimiter_depths(source_tokens)
    if delimiter_depths is None:
        return False

    impl_prefix = ("impl", step_trait, "for", step_type, "{")
    impl_blocks: list[tuple[int, int]] = []
    for index in range(len(source_tokens) - len(impl_prefix) + 1):
        if source_tokens[index : index + len(impl_prefix)] != impl_prefix:
            continue
        # The producer CommandLineStep impl must be a real root item, not
        # tokens nested in a macro, function, constant, or cfg-disabled
        # attribute. The previous root token is an item terminator in the
        # concrete source form audited here; fail closed on qualifiers or
        # attached attributes.
        if delimiter_depths[index] != 0 or (
            index > 0 and source_tokens[index - 1] not in {"}", ";"}
        ):
            continue
        opening = index + len(impl_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing is not None:
            impl_blocks.append((opening, closing))
    if len(impl_blocks) != 1:
        return False

    impl_open, impl_close = impl_blocks[0]
    method_prefix = _rust_tokens(
        "fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {"
    )
    assert method_prefix is not None
    method_blocks: list[tuple[int, int]] = []
    for index in range(impl_open + 1, impl_close - len(method_prefix) + 1):
        if source_tokens[index : index + len(method_prefix)] != method_prefix:
            continue
        if delimiter_depths[index] != 1 or source_tokens[index - 1] not in {
            "{",
            "}",
            ";",
        }:
            continue
        opening = index + len(method_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if (
            delimiter_depths[opening] != 1
            or closing is None
            or closing > impl_close
        ):
            return False
        method_blocks.append((opening, closing))
    if len(method_blocks) != 1:
        return False

    method_open, method_close = method_blocks[0]
    return source_tokens[method_open + 1 : method_close] == expected_tokens


def rust_kind_describes_exact_step(
    source: str, kind: str, step_path: str, step_description: str,
    _rust_tokens, _rust_delimiter_depths, _rust_is_simple_path,
    _matching_rust_delimiter, _rust_comma_separated_items,
) -> bool:
    """Require an exact step path in Builder's returned ``Kind`` match."""

    source_tokens = _rust_tokens(source)
    step_tokens = _rust_tokens(step_path)
    if source_tokens is None or step_tokens is None:
        return False
    delimiter_depths = _rust_delimiter_depths(source_tokens)
    if delimiter_depths is None or not _rust_is_simple_path(step_tokens):
        return False

    builder_impl_prefix = _rust_tokens("impl<'a> Builder<'a> {")
    assert builder_impl_prefix is not None
    builder_impls: list[tuple[int, int]] = []
    for index in range(
        len(source_tokens) - len(builder_impl_prefix) + 1
    ):
        if (
            source_tokens[index : index + len(builder_impl_prefix)]
            != builder_impl_prefix
            or delimiter_depths[index] != 0
        ):
            continue
        if index > 0 and source_tokens[index - 1] not in {"}", ";"}:
            continue
        opening = index + len(builder_impl_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing is not None:
            builder_impls.append((opening, closing))
    if len(builder_impls) != 1:
        return False

    impl_open, impl_close = builder_impls[0]
    method_prefix = _rust_tokens(
        "fn get_step_descriptions(kind: Kind) -> "
        f"Vec<{step_description}> {{"
    )
    assert method_prefix is not None
    method_blocks: list[tuple[int, int]] = []
    for index in range(impl_open + 1, impl_close - len(method_prefix) + 1):
        if source_tokens[index : index + len(method_prefix)] != method_prefix:
            continue
        if delimiter_depths[index] != 1 or source_tokens[index - 1] not in {
            "{",
            "}",
            ";",
        }:
            continue
        opening = index + len(method_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing is not None and closing <= impl_close:
            method_blocks.append((opening, closing))
    if len(method_blocks) != 1:
        return False

    method_open, method_close = method_blocks[0]
    match_prefix = _rust_tokens("match kind {")
    assert match_prefix is not None
    match_blocks: list[tuple[int, int]] = []
    for index in range(method_open + 1, method_close - len(match_prefix) + 1):
        if source_tokens[index : index + len(match_prefix)] != match_prefix:
            continue
        if delimiter_depths[index] != 2 or source_tokens[index - 1] not in {
            "{",
            "}",
            ";",
        }:
            continue
        opening = index + len(match_prefix) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if closing == method_close - 1:
            match_blocks.append((opening, closing))
    if len(match_blocks) != 1:
        return False

    match_open, match_close = match_blocks[0]
    prefix_tokens = _rust_tokens(f"Kind::{kind} => describe!(")
    assert prefix_tokens is not None
    describe_blocks: list[tuple[int, int]] = []
    for index in range(match_open + 1, match_close - len(prefix_tokens) + 1):
        if source_tokens[index : index + len(prefix_tokens)] != prefix_tokens:
            continue
        if delimiter_depths[index] != 3 or source_tokens[index - 1] not in {
            "{",
            ",",
        }:
            continue
        opening = index + len(prefix_tokens) - 1
        closing = _matching_rust_delimiter(source_tokens, opening)
        if (
            closing is not None
            and closing + 1 < match_close
            and source_tokens[closing + 1] == ","
            and delimiter_depths[closing + 1] == 3
        ):
            describe_blocks.append((opening, closing))
    if len(describe_blocks) != 1:
        return False

    opening, closing = describe_blocks[0]
    entries = source_tokens[opening + 1 : closing]
    items = _rust_comma_separated_items(entries)
    return (
        items is not None
        and all(_rust_is_simple_path(item) for item in items)
        and items.count(step_tokens) == 1
    )


def _rust_root_item_bodies(
    tokens: tuple[str, ...],
    depths: tuple[int, ...],
    header: tuple[str, ...],
    _matching_rust_delimiter,
) -> list[tuple[int, int]]:
    """Bodies of root items whose tokens begin with ``header``.

    A header ending in ``{`` is exact up to the body. Otherwise only a
    supertrait list (``: ..``) may follow it, at root depth, before the body.
    The item may carry ``pub``/``pub(crate)``; anything else in front of it
    (an attached ``#[cfg(..)]``, a macro, an enclosing item) fails closed.
    """

    bodies: list[tuple[int, int]] = []
    for index in range(len(tokens) - len(header) + 1):
        if tokens[index : index + len(header)] != header or depths[index] != 0:
            continue
        start = index
        if index >= 1 and tokens[index - 1] == "pub":
            start = index - 1
        elif index >= 4 and tokens[index - 4 : index] == ("pub", "(", "crate", ")"):
            start = index - 4
        if start > 0 and tokens[start - 1] not in {"}", ";"}:
            continue
        cursor = index + len(header)
        if header[-1] == "{":
            cursor -= 1
        elif cursor < len(tokens) and tokens[cursor] == ":":
            while cursor < len(tokens) and tokens[cursor] not in {"{", ";", "}"}:
                cursor += 1
        if cursor >= len(tokens) or tokens[cursor] != "{" or depths[cursor] != 0:
            continue
        closing = _matching_rust_delimiter(tokens, cursor)
        if closing is not None:
            bodies.append((cursor, closing))
    return bodies


def _rust_block_member_starts(
    tokens: tuple[str, ...],
    depths: tuple[int, ...],
    block: tuple[int, int],
    member: tuple[str, ...],
) -> list[int]:
    """Indices where ``member`` starts directly inside ``block``.

    Only a member at the block's own nesting level, following the block's
    opening or a previous member's terminator, counts.
    """

    opening, closing = block
    depth = depths[opening] + 1
    return [
        index
        for index in range(opening + 1, closing - len(member) + 1)
        if tokens[index : index + len(member)] == member
        and depths[index] == depth
        and tokens[index - 1] in {"{", "}", ";", ","}
    ]


def rust_declares_command_line_step_api(
    source: str, step_trait: str, step_description: str,
    _rust_tokens, _rust_delimiter_depths, _rust_root_item_bodies,
    _rust_block_member_starts, _matching_rust_delimiter,
) -> bool:
    """Require builder/mod.rs to declare the step API the producer parsers read.

    ``rust_step_returns_exact_should_run`` and ``rust_kind_describes_exact_step``
    match ``impl CommandLineStep for <Step>`` and
    ``Vec<CommandLineStepDescription>``. Those spellings mean "registered for
    x.py dist" only while bootstrap still routes ``should_run`` through that
    trait and that description. Require exactly one root
    ``trait CommandLineStep`` declaring ``should_run`` and exactly one root
    ``impl CommandLineStepDescription`` whose ``from`` is bounded by that trait
    and builds the description from ``S::should_run``.
    """

    tokens = _rust_tokens(source)
    if tokens is None:
        return False
    depths = _rust_delimiter_depths(tokens)
    if depths is None:
        return False

    trait = step_trait
    description = step_description
    should_run = _rust_tokens("fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_>;")
    from_method = _rust_tokens(
        f"fn from<S: {trait}>(kind: Kind) -> {description} {{"
    )
    description_impl = _rust_tokens(f"impl {description} {{")
    description_literal = _rust_tokens(f"{description} {{")
    should_run_field = _rust_tokens("should_run: S::should_run,")
    assert None not in (
        should_run,
        from_method,
        description_impl,
        description_literal,
        should_run_field,
    )

    traits = _rust_root_item_bodies(tokens, depths, ("trait", trait))
    if len(traits) != 1:
        return False
    if len(_rust_block_member_starts(tokens, depths, traits[0], should_run)) != 1:
        return False

    impls = _rust_root_item_bodies(tokens, depths, description_impl)
    if len(impls) != 1:
        return False
    from_starts = _rust_block_member_starts(tokens, depths, impls[0], from_method)
    if len(from_starts) != 1:
        return False
    from_open = from_starts[0] + len(from_method) - 1
    from_close = _matching_rust_delimiter(tokens, from_open)
    # The body of `from` is exactly the description literal, and that literal
    # takes its `should_run` from the CommandLineStep bound.
    literal_open = from_open + len(description_literal)
    if (
        from_close is None
        or tokens[from_open + 1 : literal_open + 1] != description_literal
        or _matching_rust_delimiter(tokens, literal_open) != from_close - 1
    ):
        return False
    literal = (literal_open, from_close - 1)
    return len(_rust_block_member_starts(tokens, depths, literal, should_run_field)) == 1
