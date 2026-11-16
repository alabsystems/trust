-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0 OR MIT
--
-- B1B-01f harness selftest for the definitions runner (B1B-D06 (b), D49): a definition
-- closed by sorry, hidden from a hand-written comment-and-string stripper. The char
-- literal on defs_quote's line holds a double quote; a stripper that does not know
-- char literals opens a string there and blanks everything up to the next double quote
-- (defs_close's string), defs_sorry's `sorry` included. Clean's lexer reads it as one
-- Char token, so the token scan (on Clean's lexer) finds the `sorry`. Independently of
-- the scan, the kernel refuses defs_sorry twice: its axiom_deps holds the trust marker
-- sorryAx, and the certification audit reports it. Its foundational closure is empty,
-- so census rule (d) alone would pass it. defs_quote and defs_close pass every check.

set_option autoImplicit false

namespace Trust
namespace B1bSelftest
namespace DefsSorry

def defs_quote : Char := '"'

def defs_sorry : Nat := sorry

def defs_close : String := "x"

end DefsSorry
end B1bSelftest
end Trust
