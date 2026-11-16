/- Exact retained source-claim bytes. Decoding grants no source authority. -/
import SourceWord64Record
namespace SourceWord64RecordOriginal
open SourceWord64Record
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
def originalBytes : List Nat := [84, 82, 87, 54, 52, 83, 82, 67, 1, 0, 0, 0, 78, 95, 187, 64, 234, 101, 239, 17, 200, 98, 214, 148, 77, 186, 118, 36, 2, 2, 0, 0, 0, 4, 0, 0, 0, 10, 0, 0, 0, 36, 0, 0, 0, 109, 100, 53, 61, 49, 48, 56, 51, 100, 100, 102, 57, 52, 54, 99, 102, 97, 56, 55, 102, 56, 48, 98, 49, 53, 102, 56, 49, 97, 100, 55, 53, 57, 54, 48, 97, 2, 6, 0, 0, 0, 78, 95, 187, 64, 234, 101, 239, 17, 116, 58, 149, 106, 93, 51, 80, 200, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]
def original : Record := ⟨⟨1292363674861395790, 2627492274989589192⟩, [2, 4], 10, [109, 100, 53, 61, 49, 48, 56, 51, 100, 100, 102, 57, 52, 54, 99, 102, 97, 56, 55, 102, 56, 48, 98, 49, 53, 102, 56, 49, 97, 100, 55, 53, 57, 54, 48, 97], .call 6 ⟨1292363674861395790, 14434093282035579508⟩ true true 0 (.parameter 0) 2 (.parameter 1)⟩
theorem original_decodes : decode originalBytes = .ok original := rfl
theorem trailing_refused : decode (originalBytes ++ [0]) =
  .error (.malformed "trailing source record bytes") := rfl
def missingGeneric : List Nat := [84, 82, 87, 54, 52, 83, 82, 67, 1, 0, 0, 0, 78, 95, 187, 64, 234, 101, 239, 17, 200, 98, 214, 148, 77, 186, 118, 36, 2, 2, 0, 0, 0, 4, 0, 0, 0, 10, 0, 0, 0, 36, 0, 0, 0, 109, 100, 53, 61, 49, 48, 56, 51, 100, 100, 102, 57, 52, 54, 99, 102, 97, 56, 55, 102, 56, 48, 98, 49, 53, 102, 56, 49, 97, 100, 55, 53, 57, 54, 48, 97, 2, 6, 0, 0, 0, 78, 95, 187, 64, 234, 101, 239, 17, 116, 58, 149, 106, 93, 51, 80, 200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]
theorem missing_generic_refused : decode missingGeneric =
  .error (.malformed "source record population") := rfl

#print axioms original_decodes
#print axioms trailing_refused
#print axioms missing_generic_refused
end SourceWord64RecordOriginal
