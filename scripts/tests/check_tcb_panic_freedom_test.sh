#!/usr/bin/env bash
# Mutation proofs for `scripts/check_tcb_panic_freedom.sh`'s module-file rule.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# The counter drops a module FILE when every `mod` declaration of it carries
# `#[cfg(test)]` (2026-10-10: compiler_consumer_census.rs and fold_cost_fix.rs
# were read as production because only their declaration line was dropped).
# An exclusion rule is exactly the kind of change that can hide a real panic,
# so each direction is proved by PLANTING one panic site into a fixture TCB and
# reading the count back:
#
#   1. a file declared without cfg(test)                      counted  (+1)
#   2. a file declared only under cfg(test)                   not      (+0)
#   3. a file declared both with and without cfg(test)        counted  (+1)
#   4. `#[path]` and inline-module nesting resolve: a cfg(test) `#[path]`
#      target and a cfg(test) declaration nested in an inline `mod` are not
#      counted (+0); a production `#[path]` target is (+1); a declaration in a
#      non-mod-rs file resolves under that file's own directory (+0 when test)
#
# plus the fail-safe direction (a file nothing declares is counted, +1), the
# one-line `#[cfg(test)] mod x;` form (the item after it is still counted, +1),
# a declaration inside a cfg(test) inline module (+0), and `--list` printing
# exactly TOTAL lines. The fixture is a throwaway repository laid out like this
# one, so the assertions are about the counter, not about today's tree.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
SUBJECT="$REPO_ROOT/scripts/check_tcb_panic_freedom.sh"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

PASSED=0
fail() { printf 'check_tcb_panic_freedom_test: %s\n' "$*" >&2; exit 1; }
ok()   { PASSED=$((PASSED + 1)); printf '  ok  %s\n' "$*"; }

[ -f "$SUBJECT" ] || fail "subject is missing: $SUBJECT"

R="$TMP/repo"
S="$R/crates/trust-vcgen/src"
mkdir -p "$R/scripts" "$S/outer" "$S/prod" "$S/tmod"
cp "$SUBJECT" "$R/scripts/check_tcb_panic_freedom.sh"
printf '# fixture baseline\n100\n' >"$R/scripts/check_tcb_panic_freedom.baseline"
for crate in trust-router trust-types trust-loop trust-cache trust-ir-bridge \
             trust-vc-bridge trust-cg-bridge trust-wasm-bridge; do
  mkdir -p "$R/crates/$crate/src"
  printf '// Empty fixture source.\n' > "$R/crates/$crate/src/lib.rs"
done
C="$R/compiler/rustc_mir_transform/src"
mkdir -p "$C/trust_verify/nested" "$C/trust_verify/tests/deeper" "$C/trust_verify/cycle"
cat >"$C/trust_verify.rs" <<'EOF'
mod compiler_prod;
#[cfg(test)]
mod compiler_cfg_only;
mod nested {
    mod deep;
}
#[cfg(test)]
mod tests;
#[path = "trust_verify/tests/mixed.rs"]
mod mixed;
#[path = "trust_verify/tests/production_parent_tests.rs"]
mod production_parent;
EOF
cat >"$C/trust_verify/tests.rs" <<'EOF'
mod helper;
mod deeper {
    mod leaf;
}
#[path = "tests/mixed.rs"]
mod mixed;
EOF
cat >"$C/trust_verify/tests/production_parent_tests.rs" <<'EOF'
#[path = "production_child.rs"]
mod child;
EOF
# A disconnected cycle supplies no established test ancestry.
cat >"$C/trust_verify/cycle/a.rs" <<'EOF'
#[path = "b.rs"]
mod b;
pub fn f() {}
EOF
cat >"$C/trust_verify/cycle/b.rs" <<'EOF'
#[path = "a.rs"]
mod a;
pub fn f() {}
EOF
for f in compiler_prod compiler_cfg_only nested/deep tests/helper tests/deeper/leaf tests/mixed tests/orphan tests/production_child; do
  printf 'pub fn f() {}\n' >"$C/trust_verify/$f.rs"
done

cat >"$S/lib.rs" <<'EOF'
mod prod;
#[cfg(test)]
mod cfg_only;
#[cfg(test)]
mod both;
#[cfg(not(test))]
mod both;
#[cfg(test)]
#[path = "renamed_census.rs"]
mod census;
#[path = "elsewhere.rs"]
mod relocated;
mod outer {
    #[cfg(test)]
    mod nested_probe;
    pub fn keep() {}
}
#[cfg(test)]
mod tmod {
    mod helper;
}
#[cfg(test)] mod oneline;
EOF
# prod.rs is a non-mod-rs file: its declaration names prod/sub.rs.
cat >"$S/prod.rs" <<'EOF'
#[cfg(test)]
mod sub;
pub fn f() {}
EOF
for f in cfg_only both renamed_census elsewhere outer/nested_probe tmod/helper \
         oneline orphan prod/sub; do
  printf 'pub fn f() {}\n' >"$S/$f.rs"
done

PLANT='pub fn planted() -> u8 { None::<u8>.unwrap() }'

# Reads the whole report (no early `exit`: under pipefail the writer's SIGPIPE
# would be this function's status; for the same reason every `grep -q` below
# reads a here-string, never a pipe).
total() {
  bash "$R/scripts/check_tcb_panic_freedom.sh" --print \
    | awk '$1 == "TOTAL" { t = $2 } END { print t }'
}

BASE=$(total)
[ "$BASE" = "0" ] || fail "the unplanted fixture must count 0, got '$BASE':
$(bash "$R/scripts/check_tcb_panic_freedom.sh" --print)"
ok "the unplanted fixture counts 0"

# The compiler pass is split across a root file and production child modules.
# A counter that scans only trust_verify.rs silently misses the child sites.
for spec in compiler_prod.rs:1 compiler_cfg_only.rs:0 nested/deep.rs:1 \
            tests/helper.rs:0 tests/deeper/leaf.rs:0 tests/mixed.rs:1 tests/orphan.rs:1 \
            tests/production_child.rs:1 cycle/a.rs:1; do
  file=${spec%:*}; want=${spec##*:}
  cp "$C/trust_verify/$file" "$TMP/compiler.saved"
  printf '%s\n' "$PLANT" >>"$C/trust_verify/$file"
  got=$(total)
  report=$(bash "$R/scripts/check_tcb_panic_freedom.sh" --print)
  cp "$TMP/compiler.saved" "$C/trust_verify/$file"
  [ "$got" = "$want" ] || fail "compiler module $file: expected $want, counted $got"
  if [ "$want" = 0 ]; then
    grep -qF "compiler/rustc_mir_transform/src/trust_verify/$file" <<<"$report" \
      || fail "the compiler cfg(test) child was not excluded by its declaration"
  fi
  ok "compiler module $file counts $want"
done

# plant <file> <expected delta> <what>: append one panic site, count, restore.
# A +0 is only evidence when the DECLARATION rule dropped the file, so it must
# also be named in --print's not-counted list: a fixture whose name the
# test-name filter (`test_*.rs`, `*_test.rs`, ...) already drops would pass
# vacuously. (Two of this test's first fixtures did, 2026-10-10.)
plant() {
  local file="$S/$1" want="$2" what="$3" saved got report
  saved=$(cat "$file")
  printf '%s\n' "$PLANT" >>"$file"
  got=$(total)
  report=$(bash "$R/scripts/check_tcb_panic_freedom.sh" --print)
  printf '%s\n' "$saved" >"$file"
  [ "$got" = "$((BASE + want))" ] \
    || fail "$what: planted in $1, expected $((BASE + want)), counted $got"
  if [ "$want" = 0 ]; then
    grep -qE "^  crates/trust-vcgen/src/$1 +1\$" <<<"$report" \
      || fail "$what: $1 was not dropped by the declaration rule:
$report"
  fi
  ok "$what ($1: $BASE -> $got)"
}

plant prod.rs              1 "a file declared without cfg(test) is counted"
plant cfg_only.rs         0 "a file declared only under cfg(test) is not counted"
plant both.rs              1 "a file declared both with and without cfg(test) is counted"
plant renamed_census.rs    0 "a cfg(test) #[path] target is not counted"
plant elsewhere.rs         1 "a production #[path] target is counted"
plant outer/nested_probe.rs 0 "a cfg(test) declaration inside an inline module resolves and is not counted"
plant prod/sub.rs          0 "a declaration in a non-mod-rs file resolves under its own directory"
plant tmod/helper.rs       0 "a declaration inside a cfg(test) inline module is not counted"
plant oneline.rs           0 "a one-line #[cfg(test)] mod declaration is not counted"
# lib.rs ENDS with the one-line declaration, so this plant is the next item.
plant lib.rs               1 "the item after a one-line #[cfg(test)] declaration is still counted"
plant orphan.rs            1 "a file no declaration resolves to is counted"

# Undoing the declaration's cfg(test) must bring the file back into the count:
# the exclusion follows the declaration, never the file.
cp "$S/lib.rs" "$TMP/lib.rs.saved"
printf '%s\n' "$PLANT" >>"$S/cfg_only.rs"
awk '$0 == "#[cfg(test)]" { held = $0; next }
     held != "" { if ($0 != "mod cfg_only;") print held; held = "" }
     { print }' "$TMP/lib.rs.saved" >"$S/lib.rs"
grep -qx 'mod cfg_only;' "$S/lib.rs" && ! grep -qF 'cfg(test)' <<<"$(grep -B1 -x 'mod cfg_only;' "$S/lib.rs")" \
  || fail "the fixture edit did not remove cfg_only's cfg(test)"
got=$(total)
cp "$TMP/lib.rs.saved" "$S/lib.rs"
printf 'pub fn f() {}\n' >"$S/cfg_only.rs"
[ "$got" = "$((BASE + 1))" ] \
  || fail "dropping the cfg(test) from cfg_only's declaration must count its site, got $got"
ok "removing cfg(test) from the declaration counts the file again ($BASE -> $got)"

# `--list` is the same stream: exactly TOTAL lines, the excluded files absent.
printf '%s\n' "$PLANT" >>"$S/prod.rs"
printf '%s\n' "$PLANT" >>"$S/cfg_only.rs"
listed=$(bash "$R/scripts/check_tcb_panic_freedom.sh" --list)
n=$(grep -c . <<<"$listed" || true)
[ "$n" = "$(total)" ] || fail "--list printed $n lines, TOTAL is $(total)"
grep -q 'cfg_only\.rs' <<<"$listed" \
  && fail "--list names a site in a test-only file:
$listed"
report=$(bash "$R/scripts/check_tcb_panic_freedom.sh" --print)
grep -q 'cfg_only\.rs' <<<"$report" \
  || fail "--print must name the file it excluded"
ok "--list prints exactly TOTAL lines; --print names the excluded file"

# Threshold and writer controls use the fixture's actual counted site. An
# updater must never turn a newly failing gate green by raising its ceiling.
baseline="$R/scripts/check_tcb_panic_freedom.baseline"
printf '# fixture baseline\n1\n' >"$baseline"
cp "$baseline" "$TMP/threshold.saved"
bash "$R/scripts/check_tcb_panic_freedom.sh" >"$TMP/equal.log" 2>&1 \
  || fail "a count equal to the baseline must pass"
bash "$R/scripts/check_tcb_panic_freedom.sh" --update-baseline >"$TMP/equal-update.log" 2>&1 \
  || fail "an unchanged baseline update must pass"
cmp "$baseline" "$TMP/threshold.saved" || fail "an equal update changed the baseline"
ok "equal counts pass without rewriting the baseline"

printf '%s\n' "$PLANT" >>"$S/orphan.rs"
rc=0
bash "$R/scripts/check_tcb_panic_freedom.sh" >"$TMP/grew.log" 2>&1 || rc=$?
[ "$rc" = 1 ] || fail "one additional counted site must fail the gate (exit $rc)"
rc=0
bash "$R/scripts/check_tcb_panic_freedom.sh" --update-baseline >"$TMP/upward.log" 2>&1 || rc=$?
[ "$rc" = 1 ] || fail "an upward baseline update must fail (exit $rc)"
cmp "$baseline" "$TMP/threshold.saved" || fail "an upward update changed the baseline"
printf 'pub fn f() {}\n' >"$S/orphan.rs"
ok "one additional counted site fails and cannot raise the baseline"

printf '# fixture baseline\n2\n' >"$baseline"
bash "$R/scripts/check_tcb_panic_freedom.sh" --update-baseline >"$TMP/downward.log" 2>&1 \
  || fail "a downward baseline update must pass"
cmp "$baseline" "$TMP/threshold.saved" || fail "a downward update did not preserve the header and set the count"
ok "a downward update preserves the header and sets the measured count"

for bad in '' '-1' '1junk' '1.0' '01' '2147483648' '99999999999999999999999999' $'1\n2'; do
  printf '# malformed fixture\n%s\n' "$bad" >"$baseline"
  cp "$baseline" "$TMP/malformed.saved"
  for mode in gate --update-baseline; do
    rc=0
    bash "$R/scripts/check_tcb_panic_freedom.sh" "$mode" >"$TMP/malformed.log" 2>&1 || rc=$?
    [ "$rc" = 1 ] || fail "$mode accepted malformed baseline '$bad' (exit $rc)"
    cmp "$baseline" "$TMP/malformed.saved" || fail "$mode rewrote a malformed baseline"
  done
  ok "malformed baseline is refused unchanged: ${bad:-empty}"
done
rm "$baseline"
mkdir "$baseline"
printf 'keep\n' >"$baseline/sentinel"
rc=0
bash "$R/scripts/check_tcb_panic_freedom.sh" --update-baseline >"$TMP/directory-baseline.log" 2>&1 || rc=$?
[ "$rc" = 1 ] || fail "the updater accepted a directory baseline (exit $rc)"
[ "$(ls -A "$baseline")" = sentinel ] && [ "$(cat "$baseline/sentinel")" = keep ] \
  || fail "the updater changed a directory baseline"
rm "$baseline/sentinel"
rmdir "$baseline"
ok "a directory baseline is refused without adding or changing files"

printf '# external baseline\n1\n' >"$TMP/external-baseline"
cp "$TMP/external-baseline" "$TMP/external-baseline.saved"
for target in "$TMP/external-baseline" "$TMP/absent-baseline"; do
  ln -s "$target" "$baseline"
  rc=0
  bash "$R/scripts/check_tcb_panic_freedom.sh" --update-baseline >"$TMP/symlink-baseline.log" 2>&1 || rc=$?
  [ "$rc" = 1 ] || fail "the updater accepted a symlink baseline (exit $rc)"
  [ -L "$baseline" ] && [ "$(readlink "$baseline")" = "$target" ] \
    || fail "the updater changed a baseline symlink"
  cmp "$TMP/external-baseline" "$TMP/external-baseline.saved" || fail "the updater changed the symlink target"
  [ ! -e "$TMP/absent-baseline" ] || fail "the updater created a missing symlink target"
  rm "$baseline"
  ok "a symlink baseline is refused unchanged: ${target##*/}"
done

bash "$R/scripts/check_tcb_panic_freedom.sh" --update-baseline >"$TMP/seed.log" 2>&1 \
  || fail "explicit seeding of an absent baseline must pass"
[ "$(cat "$baseline")" = 1 ] || fail "seeding did not record the measured count"
ok "an absent baseline can be explicitly seeded"

# A missing sparse source must never look like a successful zero count, even
# in the baseline-writing mode. Keep the baseline unchanged on this refusal.
cp "$R/scripts/check_tcb_panic_freedom.baseline" "$TMP/baseline.saved"
mv "$R/crates/trust-router/src" "$TMP/router-src"
for mode in gate --print --list --update-baseline; do
  rc=0
  bash "$R/scripts/check_tcb_panic_freedom.sh" "$mode" > "$TMP/missing.log" 2>&1 || rc=$?
  [ "$rc" = 2 ] || fail "$mode accepted a missing source root (exit $rc)"
  grep -q '^NOT JUDGED: missing TCB source root:' "$TMP/missing.log" \
    || fail "$mode lost the missing-source diagnostic"
done
cmp "$R/scripts/check_tcb_panic_freedom.baseline" "$TMP/baseline.saved" \
  || fail "missing sources changed the baseline"
mv "$TMP/router-src" "$R/crates/trust-router/src"
ok "all modes refuse absent source roots without rewriting the baseline"

# A directory can exist while a tracked source file is omitted by sparse rules.
git -C "$R" init -q
git -C "$R" add .
git -C "$R" -c user.name=Fixture -c user.email=fixture@example.invalid \
  -c commit.gpgsign=false commit -qm fixture
mv "$S/orphan.rs" "$TMP/orphan.rs"
rc=0
bash "$R/scripts/check_tcb_panic_freedom.sh" > "$TMP/partial.log" 2>&1 || rc=$?
[ "$rc" = 2 ] || fail "accepted a missing committed source file (exit $rc)"
grep -q '^NOT JUDGED: missing committed TCB source:' "$TMP/partial.log" \
  || fail "missing committed source was not diagnosed"
mv "$TMP/orphan.rs" "$S/orphan.rs"
ok "partially populated source roots refuse a count"

mv "$C/trust_verify/compiler_prod.rs" "$TMP/compiler_prod.rs"
for mode in gate --update-baseline; do
  rc=0
  bash "$R/scripts/check_tcb_panic_freedom.sh" "$mode" >"$TMP/partial-compiler.log" 2>&1 || rc=$?
  [ "$rc" = 2 ] || fail "$mode accepted a missing committed compiler child (exit $rc)"
  grep -q '^NOT JUDGED: missing committed TCB source:' "$TMP/partial-compiler.log" \
    || fail "missing committed compiler child was not diagnosed"
done
mv "$TMP/compiler_prod.rs" "$C/trust_verify/compiler_prod.rs"
ok "a missing committed compiler child refuses a count and update"

printf 'check_tcb_panic_freedom_test: %d checks passed\n' "$PASSED"
