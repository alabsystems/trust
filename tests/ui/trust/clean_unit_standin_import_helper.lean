-- Trust fixture: a unit that opens the way a pasted Lean file opens.
-- `import Lean` is served by Clean's built-in prelude stand-in, not by
-- Lean; `clean_unit_standin_import_disclosed.rs` pins that the build says so.
import Lean
def unit_six : UInt64 := 6
