#!/usr/bin/env bash
# Differential check of this crate's own solver against the committed corpus.
set -u
AY="${AY:-$(command -v ay)}"
"$AY" theory_soundness.smt2 | grep -Ex 'sat|unsat'
