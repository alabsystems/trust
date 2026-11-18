-- Copyright 2026 Andrew Yates | Apache-2.0
import C11OrdinaryTokens
import CAtomicDropSource
import CAtomicIncrementSource

/-! Actual complete-byte witnesses for the separate ordinary-fragment grammar. Not a C typing/execution/source-custody theorem. -/
namespace C11ActualTokens
open C11OrdinaryTokens

def drop_source83 : List UInt8 := []
def drop_tokens83 : List String := []
theorem drop_lex83 : Lexes drop_source83 drop_tokens83 := .done
def drop_source82 : List UInt8 := [125] ++ drop_source83
def drop_tokens82 : List String := "}" :: drop_tokens83
theorem drop_bytes82 : bytes "}" = [125] := by rfl
theorem drop_valid82 : valid .punctuator [125] drop_source83 = true := by decide
theorem drop_lex82 : Lexes drop_source82 drop_tokens82 := by
  change Lexes ([125] ++ drop_source83) ("}" :: drop_tokens83)
  rw [← drop_bytes82]
  exact .token .punctuator "}" _ _ (by rw [drop_bytes82]; exact drop_valid82) drop_lex83
def drop_source81 : List UInt8 := [10] ++ drop_source82
def drop_tokens81 : List String := drop_tokens82
theorem drop_lex81 : Lexes drop_source81 drop_tokens81 :=
  .whitespace [10] _ _ (by decide) drop_lex82
def drop_source80 : List UInt8 := [59] ++ drop_source81
def drop_tokens80 : List String := ";" :: drop_tokens81
theorem drop_bytes80 : bytes ";" = [59] := by rfl
theorem drop_valid80 : valid .punctuator [59] drop_source81 = true := by decide
theorem drop_lex80 : Lexes drop_source80 drop_tokens80 := by
  change Lexes ([59] ++ drop_source81) (";" :: drop_tokens81)
  rw [← drop_bytes80]
  exact .token .punctuator ";" _ _ (by rw [drop_bytes80]; exact drop_valid80) drop_lex81
def drop_source79 : List UInt8 := [116, 114, 117, 101] ++ drop_source80
def drop_tokens79 : List String := "true" :: drop_tokens80
theorem drop_bytes79 : bytes "true" = [116, 114, 117, 101] := by rfl
theorem drop_valid79 : valid .identifier [116, 114, 117, 101] drop_source80 = true := by decide
theorem drop_lex79 : Lexes drop_source79 drop_tokens79 := by
  change Lexes ([116, 114, 117, 101] ++ drop_source80) ("true" :: drop_tokens80)
  rw [← drop_bytes79]
  exact .token .identifier "true" _ _ (by rw [drop_bytes79]; exact drop_valid79) drop_lex80
def drop_source78 : List UInt8 := [32] ++ drop_source79
def drop_tokens78 : List String := drop_tokens79
theorem drop_lex78 : Lexes drop_source78 drop_tokens78 :=
  .whitespace [32] _ _ (by decide) drop_lex79
def drop_source77 : List UInt8 := [114, 101, 116, 117, 114, 110] ++ drop_source78
def drop_tokens77 : List String := "return" :: drop_tokens78
theorem drop_bytes77 : bytes "return" = [114, 101, 116, 117, 114, 110] := by rfl
theorem drop_valid77 : valid .identifier [114, 101, 116, 117, 114, 110] drop_source78 = true := by decide
theorem drop_lex77 : Lexes drop_source77 drop_tokens77 := by
  change Lexes ([114, 101, 116, 117, 114, 110] ++ drop_source78) ("return" :: drop_tokens78)
  rw [← drop_bytes77]
  exact .token .identifier "return" _ _ (by rw [drop_bytes77]; exact drop_valid77) drop_lex78
def drop_source76 : List UInt8 := [10, 32, 32, 32, 32] ++ drop_source77
def drop_tokens76 : List String := drop_tokens77
theorem drop_lex76 : Lexes drop_source76 drop_tokens76 :=
  .whitespace [10, 32, 32, 32, 32] _ _ (by decide) drop_lex77
def drop_source75 : List UInt8 := [59] ++ drop_source76
def drop_tokens75 : List String := ";" :: drop_tokens76
theorem drop_bytes75 : bytes ";" = [59] := by rfl
theorem drop_valid75 : valid .punctuator [59] drop_source76 = true := by decide
theorem drop_lex75 : Lexes drop_source75 drop_tokens75 := by
  change Lexes ([59] ++ drop_source76) (";" :: drop_tokens76)
  rw [← drop_bytes75]
  exact .token .punctuator ";" _ _ (by rw [drop_bytes75]; exact drop_valid75) drop_lex76
def drop_source74 : List UInt8 := [41] ++ drop_source75
def drop_tokens74 : List String := ")" :: drop_tokens75
theorem drop_bytes74 : bytes ")" = [41] := by rfl
theorem drop_valid74 : valid .punctuator [41] drop_source75 = true := by decide
theorem drop_lex74 : Lexes drop_source74 drop_tokens74 := by
  change Lexes ([41] ++ drop_source75) (")" :: drop_tokens75)
  rw [← drop_bytes74]
  exact .token .punctuator ")" _ _ (by rw [drop_bytes74]; exact drop_valid74) drop_lex75
def drop_source73 : List UInt8 := [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 97, 99, 113, 117, 105, 114, 101] ++ drop_source74
def drop_tokens73 : List String := "memory_order_acquire" :: drop_tokens74
theorem drop_bytes73 : bytes "memory_order_acquire" = [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 97, 99, 113, 117, 105, 114, 101] := by rfl
theorem drop_valid73 : valid .identifier [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 97, 99, 113, 117, 105, 114, 101] drop_source74 = true := by decide
theorem drop_lex73 : Lexes drop_source73 drop_tokens73 := by
  change Lexes ([109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 97, 99, 113, 117, 105, 114, 101] ++ drop_source74) ("memory_order_acquire" :: drop_tokens74)
  rw [← drop_bytes73]
  exact .token .identifier "memory_order_acquire" _ _ (by rw [drop_bytes73]; exact drop_valid73) drop_lex74
def drop_source72 : List UInt8 := [40] ++ drop_source73
def drop_tokens72 : List String := "(" :: drop_tokens73
theorem drop_bytes72 : bytes "(" = [40] := by rfl
theorem drop_valid72 : valid .punctuator [40] drop_source73 = true := by decide
theorem drop_lex72 : Lexes drop_source72 drop_tokens72 := by
  change Lexes ([40] ++ drop_source73) ("(" :: drop_tokens73)
  rw [← drop_bytes72]
  exact .token .punctuator "(" _ _ (by rw [drop_bytes72]; exact drop_valid72) drop_lex73
def drop_source71 : List UInt8 := [97, 116, 111, 109, 105, 99, 95, 116, 104, 114, 101, 97, 100, 95, 102, 101, 110, 99, 101] ++ drop_source72
def drop_tokens71 : List String := "atomic_thread_fence" :: drop_tokens72
theorem drop_bytes71 : bytes "atomic_thread_fence" = [97, 116, 111, 109, 105, 99, 95, 116, 104, 114, 101, 97, 100, 95, 102, 101, 110, 99, 101] := by rfl
theorem drop_valid71 : valid .identifier [97, 116, 111, 109, 105, 99, 95, 116, 104, 114, 101, 97, 100, 95, 102, 101, 110, 99, 101] drop_source72 = true := by decide
theorem drop_lex71 : Lexes drop_source71 drop_tokens71 := by
  change Lexes ([97, 116, 111, 109, 105, 99, 95, 116, 104, 114, 101, 97, 100, 95, 102, 101, 110, 99, 101] ++ drop_source72) ("atomic_thread_fence" :: drop_tokens72)
  rw [← drop_bytes71]
  exact .token .identifier "atomic_thread_fence" _ _ (by rw [drop_bytes71]; exact drop_valid71) drop_lex72
def drop_source70 : List UInt8 := [10, 32, 32, 32, 32] ++ drop_source71
def drop_tokens70 : List String := drop_tokens71
theorem drop_lex70 : Lexes drop_source70 drop_tokens70 :=
  .whitespace [10, 32, 32, 32, 32] _ _ (by decide) drop_lex71
def drop_source69 : List UInt8 := [59] ++ drop_source70
def drop_tokens69 : List String := ";" :: drop_tokens70
theorem drop_bytes69 : bytes ";" = [59] := by rfl
theorem drop_valid69 : valid .punctuator [59] drop_source70 = true := by decide
theorem drop_lex69 : Lexes drop_source69 drop_tokens69 := by
  change Lexes ([59] ++ drop_source70) (";" :: drop_tokens70)
  rw [← drop_bytes69]
  exact .token .punctuator ";" _ _ (by rw [drop_bytes69]; exact drop_valid69) drop_lex70
def drop_source68 : List UInt8 := [102, 97, 108, 115, 101] ++ drop_source69
def drop_tokens68 : List String := "false" :: drop_tokens69
theorem drop_bytes68 : bytes "false" = [102, 97, 108, 115, 101] := by rfl
theorem drop_valid68 : valid .identifier [102, 97, 108, 115, 101] drop_source69 = true := by decide
theorem drop_lex68 : Lexes drop_source68 drop_tokens68 := by
  change Lexes ([102, 97, 108, 115, 101] ++ drop_source69) ("false" :: drop_tokens69)
  rw [← drop_bytes68]
  exact .token .identifier "false" _ _ (by rw [drop_bytes68]; exact drop_valid68) drop_lex69
def drop_source67 : List UInt8 := [32] ++ drop_source68
def drop_tokens67 : List String := drop_tokens68
theorem drop_lex67 : Lexes drop_source67 drop_tokens67 :=
  .whitespace [32] _ _ (by decide) drop_lex68
def drop_source66 : List UInt8 := [114, 101, 116, 117, 114, 110] ++ drop_source67
def drop_tokens66 : List String := "return" :: drop_tokens67
theorem drop_bytes66 : bytes "return" = [114, 101, 116, 117, 114, 110] := by rfl
theorem drop_valid66 : valid .identifier [114, 101, 116, 117, 114, 110] drop_source67 = true := by decide
theorem drop_lex66 : Lexes drop_source66 drop_tokens66 := by
  change Lexes ([114, 101, 116, 117, 114, 110] ++ drop_source67) ("return" :: drop_tokens67)
  rw [← drop_bytes66]
  exact .token .identifier "return" _ _ (by rw [drop_bytes66]; exact drop_valid66) drop_lex67
def drop_source65 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32, 32] ++ drop_source66
def drop_tokens65 : List String := drop_tokens66
theorem drop_lex65 : Lexes drop_source65 drop_tokens65 :=
  .whitespace [10, 32, 32, 32, 32, 32, 32, 32, 32] _ _ (by decide) drop_lex66
def drop_source64 : List UInt8 := [41] ++ drop_source65
def drop_tokens64 : List String := ")" :: drop_tokens65
theorem drop_bytes64 : bytes ")" = [41] := by rfl
theorem drop_valid64 : valid .punctuator [41] drop_source65 = true := by decide
theorem drop_lex64 : Lexes drop_source64 drop_tokens64 := by
  change Lexes ([41] ++ drop_source65) (")" :: drop_tokens65)
  rw [← drop_bytes64]
  exact .token .punctuator ")" _ _ (by rw [drop_bytes64]; exact drop_valid64) drop_lex65
def drop_source63 : List UInt8 := [48] ++ drop_source64
def drop_tokens63 : List String := "0" :: drop_tokens64
theorem drop_bytes63 : bytes "0" = [48] := by rfl
theorem drop_valid63 : valid .integer01 [48] drop_source64 = true := by decide
theorem drop_lex63 : Lexes drop_source63 drop_tokens63 := by
  change Lexes ([48] ++ drop_source64) ("0" :: drop_tokens64)
  rw [← drop_bytes63]
  exact .token .integer01 "0" _ _ (by rw [drop_bytes63]; exact drop_valid63) drop_lex64
def drop_source62 : List UInt8 := [32] ++ drop_source63
def drop_tokens62 : List String := drop_tokens63
theorem drop_lex62 : Lexes drop_source62 drop_tokens62 :=
  .whitespace [32] _ _ (by decide) drop_lex63
def drop_source61 : List UInt8 := [33, 61] ++ drop_source62
def drop_tokens61 : List String := "!=" :: drop_tokens62
theorem drop_bytes61 : bytes "!=" = [33, 61] := by rfl
theorem drop_valid61 : valid .punctuator [33, 61] drop_source62 = true := by decide
theorem drop_lex61 : Lexes drop_source61 drop_tokens61 := by
  change Lexes ([33, 61] ++ drop_source62) ("!=" :: drop_tokens62)
  rw [← drop_bytes61]
  exact .token .punctuator "!=" _ _ (by rw [drop_bytes61]; exact drop_valid61) drop_lex62
def drop_source60 : List UInt8 := [32] ++ drop_source61
def drop_tokens60 : List String := drop_tokens61
theorem drop_lex60 : Lexes drop_source60 drop_tokens60 :=
  .whitespace [32] _ _ (by decide) drop_lex61
def drop_source59 : List UInt8 := [41] ++ drop_source60
def drop_tokens59 : List String := ")" :: drop_tokens60
theorem drop_bytes59 : bytes ")" = [41] := by rfl
theorem drop_valid59 : valid .punctuator [41] drop_source60 = true := by decide
theorem drop_lex59 : Lexes drop_source59 drop_tokens59 := by
  change Lexes ([41] ++ drop_source60) (")" :: drop_tokens60)
  rw [← drop_bytes59]
  exact .token .punctuator ")" _ _ (by rw [drop_bytes59]; exact drop_valid59) drop_lex60
def drop_source58 : List UInt8 := [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 101, 97, 115, 101] ++ drop_source59
def drop_tokens58 : List String := "memory_order_release" :: drop_tokens59
theorem drop_bytes58 : bytes "memory_order_release" = [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 101, 97, 115, 101] := by rfl
theorem drop_valid58 : valid .identifier [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 101, 97, 115, 101] drop_source59 = true := by decide
theorem drop_lex58 : Lexes drop_source58 drop_tokens58 := by
  change Lexes ([109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 101, 97, 115, 101] ++ drop_source59) ("memory_order_release" :: drop_tokens59)
  rw [← drop_bytes58]
  exact .token .identifier "memory_order_release" _ _ (by rw [drop_bytes58]; exact drop_valid58) drop_lex59
def drop_source57 : List UInt8 := [32] ++ drop_source58
def drop_tokens57 : List String := drop_tokens58
theorem drop_lex57 : Lexes drop_source57 drop_tokens57 :=
  .whitespace [32] _ _ (by decide) drop_lex58
def drop_source56 : List UInt8 := [44] ++ drop_source57
def drop_tokens56 : List String := "," :: drop_tokens57
theorem drop_bytes56 : bytes "," = [44] := by rfl
theorem drop_valid56 : valid .punctuator [44] drop_source57 = true := by decide
theorem drop_lex56 : Lexes drop_source56 drop_tokens56 := by
  change Lexes ([44] ++ drop_source57) ("," :: drop_tokens57)
  rw [← drop_bytes56]
  exact .token .punctuator "," _ _ (by rw [drop_bytes56]; exact drop_valid56) drop_lex57
def drop_source55 : List UInt8 := [49] ++ drop_source56
def drop_tokens55 : List String := "1" :: drop_tokens56
theorem drop_bytes55 : bytes "1" = [49] := by rfl
theorem drop_valid55 : valid .integer01 [49] drop_source56 = true := by decide
theorem drop_lex55 : Lexes drop_source55 drop_tokens55 := by
  change Lexes ([49] ++ drop_source56) ("1" :: drop_tokens56)
  rw [← drop_bytes55]
  exact .token .integer01 "1" _ _ (by rw [drop_bytes55]; exact drop_valid55) drop_lex56
def drop_source54 : List UInt8 := [32] ++ drop_source55
def drop_tokens54 : List String := drop_tokens55
theorem drop_lex54 : Lexes drop_source54 drop_tokens54 :=
  .whitespace [32] _ _ (by decide) drop_lex55
def drop_source53 : List UInt8 := [44] ++ drop_source54
def drop_tokens53 : List String := "," :: drop_tokens54
theorem drop_bytes53 : bytes "," = [44] := by rfl
theorem drop_valid53 : valid .punctuator [44] drop_source54 = true := by decide
theorem drop_lex53 : Lexes drop_source53 drop_tokens53 := by
  change Lexes ([44] ++ drop_source54) ("," :: drop_tokens54)
  rw [← drop_bytes53]
  exact .token .punctuator "," _ _ (by rw [drop_bytes53]; exact drop_valid53) drop_lex54
def drop_source52 : List UInt8 := [114, 101, 102, 95, 99, 111, 117, 110, 116] ++ drop_source53
def drop_tokens52 : List String := "ref_count" :: drop_tokens53
theorem drop_bytes52 : bytes "ref_count" = [114, 101, 102, 95, 99, 111, 117, 110, 116] := by rfl
theorem drop_valid52 : valid .identifier [114, 101, 102, 95, 99, 111, 117, 110, 116] drop_source53 = true := by decide
theorem drop_lex52 : Lexes drop_source52 drop_tokens52 := by
  change Lexes ([114, 101, 102, 95, 99, 111, 117, 110, 116] ++ drop_source53) ("ref_count" :: drop_tokens53)
  rw [← drop_bytes52]
  exact .token .identifier "ref_count" _ _ (by rw [drop_bytes52]; exact drop_valid52) drop_lex53
def drop_source51 : List UInt8 := [46] ++ drop_source52
def drop_tokens51 : List String := "." :: drop_tokens52
theorem drop_bytes51 : bytes "." = [46] := by rfl
theorem drop_valid51 : valid .punctuator [46] drop_source52 = true := by decide
theorem drop_lex51 : Lexes drop_source51 drop_tokens51 := by
  change Lexes ([46] ++ drop_source52) ("." :: drop_tokens52)
  rw [← drop_bytes51]
  exact .token .punctuator "." _ _ (by rw [drop_bytes51]; exact drop_valid51) drop_lex52
def drop_source50 : List UInt8 := [104, 101, 97, 100, 101, 114] ++ drop_source51
def drop_tokens50 : List String := "header" :: drop_tokens51
theorem drop_bytes50 : bytes "header" = [104, 101, 97, 100, 101, 114] := by rfl
theorem drop_valid50 : valid .identifier [104, 101, 97, 100, 101, 114] drop_source51 = true := by decide
theorem drop_lex50 : Lexes drop_source50 drop_tokens50 := by
  change Lexes ([104, 101, 97, 100, 101, 114] ++ drop_source51) ("header" :: drop_tokens51)
  rw [← drop_bytes50]
  exact .token .identifier "header" _ _ (by rw [drop_bytes50]; exact drop_valid50) drop_lex51
def drop_source49 : List UInt8 := [45, 62] ++ drop_source50
def drop_tokens49 : List String := "->" :: drop_tokens50
theorem drop_bytes49 : bytes "->" = [45, 62] := by rfl
theorem drop_valid49 : valid .punctuator [45, 62] drop_source50 = true := by decide
theorem drop_lex49 : Lexes drop_source49 drop_tokens49 := by
  change Lexes ([45, 62] ++ drop_source50) ("->" :: drop_tokens50)
  rw [← drop_bytes49]
  exact .token .punctuator "->" _ _ (by rw [drop_bytes49]; exact drop_valid49) drop_lex50
def drop_source48 : List UInt8 := [111] ++ drop_source49
def drop_tokens48 : List String := "o" :: drop_tokens49
theorem drop_bytes48 : bytes "o" = [111] := by rfl
theorem drop_valid48 : valid .identifier [111] drop_source49 = true := by decide
theorem drop_lex48 : Lexes drop_source48 drop_tokens48 := by
  change Lexes ([111] ++ drop_source49) ("o" :: drop_tokens49)
  rw [← drop_bytes48]
  exact .token .identifier "o" _ _ (by rw [drop_bytes48]; exact drop_valid48) drop_lex49
def drop_source47 : List UInt8 := [38] ++ drop_source48
def drop_tokens47 : List String := "&" :: drop_tokens48
theorem drop_bytes47 : bytes "&" = [38] := by rfl
theorem drop_valid47 : valid .punctuator [38] drop_source48 = true := by decide
theorem drop_lex47 : Lexes drop_source47 drop_tokens47 := by
  change Lexes ([38] ++ drop_source48) ("&" :: drop_tokens48)
  rw [← drop_bytes47]
  exact .token .punctuator "&" _ _ (by rw [drop_bytes47]; exact drop_valid47) drop_lex48
def drop_source46 : List UInt8 := [40] ++ drop_source47
def drop_tokens46 : List String := "(" :: drop_tokens47
theorem drop_bytes46 : bytes "(" = [40] := by rfl
theorem drop_valid46 : valid .punctuator [40] drop_source47 = true := by decide
theorem drop_lex46 : Lexes drop_source46 drop_tokens46 := by
  change Lexes ([40] ++ drop_source47) ("(" :: drop_tokens47)
  rw [← drop_bytes46]
  exact .token .punctuator "(" _ _ (by rw [drop_bytes46]; exact drop_valid46) drop_lex47
def drop_source45 : List UInt8 := [97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 115, 117, 98, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ drop_source46
def drop_tokens45 : List String := "atomic_fetch_sub_explicit" :: drop_tokens46
theorem drop_bytes45 : bytes "atomic_fetch_sub_explicit" = [97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 115, 117, 98, 95, 101, 120, 112, 108, 105, 99, 105, 116] := by rfl
theorem drop_valid45 : valid .identifier [97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 115, 117, 98, 95, 101, 120, 112, 108, 105, 99, 105, 116] drop_source46 = true := by decide
theorem drop_lex45 : Lexes drop_source45 drop_tokens45 := by
  change Lexes ([97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 115, 117, 98, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ drop_source46) ("atomic_fetch_sub_explicit" :: drop_tokens46)
  rw [← drop_bytes45]
  exact .token .identifier "atomic_fetch_sub_explicit" _ _ (by rw [drop_bytes45]; exact drop_valid45) drop_lex46
def drop_source44 : List UInt8 := [40] ++ drop_source45
def drop_tokens44 : List String := "(" :: drop_tokens45
theorem drop_bytes44 : bytes "(" = [40] := by rfl
theorem drop_valid44 : valid .punctuator [40] drop_source45 = true := by decide
theorem drop_lex44 : Lexes drop_source44 drop_tokens44 := by
  change Lexes ([40] ++ drop_source45) ("(" :: drop_tokens45)
  rw [← drop_bytes44]
  exact .token .punctuator "(" _ _ (by rw [drop_bytes44]; exact drop_valid44) drop_lex45
def drop_source43 : List UInt8 := [32] ++ drop_source44
def drop_tokens43 : List String := drop_tokens44
theorem drop_lex43 : Lexes drop_source43 drop_tokens43 :=
  .whitespace [32] _ _ (by decide) drop_lex44
def drop_source42 : List UInt8 := [105, 102] ++ drop_source43
def drop_tokens42 : List String := "if" :: drop_tokens43
theorem drop_bytes42 : bytes "if" = [105, 102] := by rfl
theorem drop_valid42 : valid .identifier [105, 102] drop_source43 = true := by decide
theorem drop_lex42 : Lexes drop_source42 drop_tokens42 := by
  change Lexes ([105, 102] ++ drop_source43) ("if" :: drop_tokens43)
  rw [← drop_bytes42]
  exact .token .identifier "if" _ _ (by rw [drop_bytes42]; exact drop_valid42) drop_lex43
def drop_source41 : List UInt8 := [10, 32, 32, 32, 32] ++ drop_source42
def drop_tokens41 : List String := drop_tokens42
theorem drop_lex41 : Lexes drop_source41 drop_tokens41 :=
  .whitespace [10, 32, 32, 32, 32] _ _ (by decide) drop_lex42
def drop_source40 : List UInt8 := [59] ++ drop_source41
def drop_tokens40 : List String := ";" :: drop_tokens41
theorem drop_bytes40 : bytes ";" = [59] := by rfl
theorem drop_valid40 : valid .punctuator [59] drop_source41 = true := by decide
theorem drop_lex40 : Lexes drop_source40 drop_tokens40 := by
  change Lexes ([59] ++ drop_source41) (";" :: drop_tokens41)
  rw [← drop_bytes40]
  exact .token .punctuator ";" _ _ (by rw [drop_bytes40]; exact drop_valid40) drop_lex41
def drop_source39 : List UInt8 := [102, 97, 108, 115, 101] ++ drop_source40
def drop_tokens39 : List String := "false" :: drop_tokens40
theorem drop_bytes39 : bytes "false" = [102, 97, 108, 115, 101] := by rfl
theorem drop_valid39 : valid .identifier [102, 97, 108, 115, 101] drop_source40 = true := by decide
theorem drop_lex39 : Lexes drop_source39 drop_tokens39 := by
  change Lexes ([102, 97, 108, 115, 101] ++ drop_source40) ("false" :: drop_tokens40)
  rw [← drop_bytes39]
  exact .token .identifier "false" _ _ (by rw [drop_bytes39]; exact drop_valid39) drop_lex40
def drop_source38 : List UInt8 := [32] ++ drop_source39
def drop_tokens38 : List String := drop_tokens39
theorem drop_lex38 : Lexes drop_source38 drop_tokens38 :=
  .whitespace [32] _ _ (by decide) drop_lex39
def drop_source37 : List UInt8 := [114, 101, 116, 117, 114, 110] ++ drop_source38
def drop_tokens37 : List String := "return" :: drop_tokens38
theorem drop_bytes37 : bytes "return" = [114, 101, 116, 117, 114, 110] := by rfl
theorem drop_valid37 : valid .identifier [114, 101, 116, 117, 114, 110] drop_source38 = true := by decide
theorem drop_lex37 : Lexes drop_source37 drop_tokens37 := by
  change Lexes ([114, 101, 116, 117, 114, 110] ++ drop_source38) ("return" :: drop_tokens38)
  rw [← drop_bytes37]
  exact .token .identifier "return" _ _ (by rw [drop_bytes37]; exact drop_valid37) drop_lex38
def drop_source36 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32, 32] ++ drop_source37
def drop_tokens36 : List String := drop_tokens37
theorem drop_lex36 : Lexes drop_source36 drop_tokens36 :=
  .whitespace [10, 32, 32, 32, 32, 32, 32, 32, 32] _ _ (by decide) drop_lex37
def drop_source35 : List UInt8 := [41] ++ drop_source36
def drop_tokens35 : List String := ")" :: drop_tokens36
theorem drop_bytes35 : bytes ")" = [41] := by rfl
theorem drop_valid35 : valid .punctuator [41] drop_source36 = true := by decide
theorem drop_lex35 : Lexes drop_source35 drop_tokens35 := by
  change Lexes ([41] ++ drop_source36) (")" :: drop_tokens36)
  rw [← drop_bytes35]
  exact .token .punctuator ")" _ _ (by rw [drop_bytes35]; exact drop_valid35) drop_lex36
def drop_source34 : List UInt8 := [67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89, 95, 68, 82, 79, 80] ++ drop_source35
def drop_tokens34 : List String := "CLEAN_RC_STICKY_DROP" :: drop_tokens35
theorem drop_bytes34 : bytes "CLEAN_RC_STICKY_DROP" = [67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89, 95, 68, 82, 79, 80] := by rfl
theorem drop_valid34 : valid .identifier [67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89, 95, 68, 82, 79, 80] drop_source35 = true := by decide
theorem drop_lex34 : Lexes drop_source34 drop_tokens34 := by
  change Lexes ([67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89, 95, 68, 82, 79, 80] ++ drop_source35) ("CLEAN_RC_STICKY_DROP" :: drop_tokens35)
  rw [← drop_bytes34]
  exact .token .identifier "CLEAN_RC_STICKY_DROP" _ _ (by rw [drop_bytes34]; exact drop_valid34) drop_lex35
def drop_source33 : List UInt8 := [32] ++ drop_source34
def drop_tokens33 : List String := drop_tokens34
theorem drop_lex33 : Lexes drop_source33 drop_tokens33 :=
  .whitespace [32] _ _ (by decide) drop_lex34
def drop_source32 : List UInt8 := [62, 61] ++ drop_source33
def drop_tokens32 : List String := ">=" :: drop_tokens33
theorem drop_bytes32 : bytes ">=" = [62, 61] := by rfl
theorem drop_valid32 : valid .punctuator [62, 61] drop_source33 = true := by decide
theorem drop_lex32 : Lexes drop_source32 drop_tokens32 := by
  change Lexes ([62, 61] ++ drop_source33) (">=" :: drop_tokens33)
  rw [← drop_bytes32]
  exact .token .punctuator ">=" _ _ (by rw [drop_bytes32]; exact drop_valid32) drop_lex33
def drop_source31 : List UInt8 := [32] ++ drop_source32
def drop_tokens31 : List String := drop_tokens32
theorem drop_lex31 : Lexes drop_source31 drop_tokens31 :=
  .whitespace [32] _ _ (by decide) drop_lex32
def drop_source30 : List UInt8 := [41] ++ drop_source31
def drop_tokens30 : List String := ")" :: drop_tokens31
theorem drop_bytes30 : bytes ")" = [41] := by rfl
theorem drop_valid30 : valid .punctuator [41] drop_source31 = true := by decide
theorem drop_lex30 : Lexes drop_source30 drop_tokens30 := by
  change Lexes ([41] ++ drop_source31) (")" :: drop_tokens31)
  rw [← drop_bytes30]
  exact .token .punctuator ")" _ _ (by rw [drop_bytes30]; exact drop_valid30) drop_lex31
def drop_source29 : List UInt8 := [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] ++ drop_source30
def drop_tokens29 : List String := "memory_order_relaxed" :: drop_tokens30
theorem drop_bytes29 : bytes "memory_order_relaxed" = [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] := by rfl
theorem drop_valid29 : valid .identifier [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] drop_source30 = true := by decide
theorem drop_lex29 : Lexes drop_source29 drop_tokens29 := by
  change Lexes ([109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] ++ drop_source30) ("memory_order_relaxed" :: drop_tokens30)
  rw [← drop_bytes29]
  exact .token .identifier "memory_order_relaxed" _ _ (by rw [drop_bytes29]; exact drop_valid29) drop_lex30
def drop_source28 : List UInt8 := [32] ++ drop_source29
def drop_tokens28 : List String := drop_tokens29
theorem drop_lex28 : Lexes drop_source28 drop_tokens28 :=
  .whitespace [32] _ _ (by decide) drop_lex29
def drop_source27 : List UInt8 := [44] ++ drop_source28
def drop_tokens27 : List String := "," :: drop_tokens28
theorem drop_bytes27 : bytes "," = [44] := by rfl
theorem drop_valid27 : valid .punctuator [44] drop_source28 = true := by decide
theorem drop_lex27 : Lexes drop_source27 drop_tokens27 := by
  change Lexes ([44] ++ drop_source28) ("," :: drop_tokens28)
  rw [← drop_bytes27]
  exact .token .punctuator "," _ _ (by rw [drop_bytes27]; exact drop_valid27) drop_lex28
def drop_source26 : List UInt8 := [114, 101, 102, 95, 99, 111, 117, 110, 116] ++ drop_source27
def drop_tokens26 : List String := "ref_count" :: drop_tokens27
theorem drop_bytes26 : bytes "ref_count" = [114, 101, 102, 95, 99, 111, 117, 110, 116] := by rfl
theorem drop_valid26 : valid .identifier [114, 101, 102, 95, 99, 111, 117, 110, 116] drop_source27 = true := by decide
theorem drop_lex26 : Lexes drop_source26 drop_tokens26 := by
  change Lexes ([114, 101, 102, 95, 99, 111, 117, 110, 116] ++ drop_source27) ("ref_count" :: drop_tokens27)
  rw [← drop_bytes26]
  exact .token .identifier "ref_count" _ _ (by rw [drop_bytes26]; exact drop_valid26) drop_lex27
def drop_source25 : List UInt8 := [46] ++ drop_source26
def drop_tokens25 : List String := "." :: drop_tokens26
theorem drop_bytes25 : bytes "." = [46] := by rfl
theorem drop_valid25 : valid .punctuator [46] drop_source26 = true := by decide
theorem drop_lex25 : Lexes drop_source25 drop_tokens25 := by
  change Lexes ([46] ++ drop_source26) ("." :: drop_tokens26)
  rw [← drop_bytes25]
  exact .token .punctuator "." _ _ (by rw [drop_bytes25]; exact drop_valid25) drop_lex26
def drop_source24 : List UInt8 := [104, 101, 97, 100, 101, 114] ++ drop_source25
def drop_tokens24 : List String := "header" :: drop_tokens25
theorem drop_bytes24 : bytes "header" = [104, 101, 97, 100, 101, 114] := by rfl
theorem drop_valid24 : valid .identifier [104, 101, 97, 100, 101, 114] drop_source25 = true := by decide
theorem drop_lex24 : Lexes drop_source24 drop_tokens24 := by
  change Lexes ([104, 101, 97, 100, 101, 114] ++ drop_source25) ("header" :: drop_tokens25)
  rw [← drop_bytes24]
  exact .token .identifier "header" _ _ (by rw [drop_bytes24]; exact drop_valid24) drop_lex25
def drop_source23 : List UInt8 := [45, 62] ++ drop_source24
def drop_tokens23 : List String := "->" :: drop_tokens24
theorem drop_bytes23 : bytes "->" = [45, 62] := by rfl
theorem drop_valid23 : valid .punctuator [45, 62] drop_source24 = true := by decide
theorem drop_lex23 : Lexes drop_source23 drop_tokens23 := by
  change Lexes ([45, 62] ++ drop_source24) ("->" :: drop_tokens24)
  rw [← drop_bytes23]
  exact .token .punctuator "->" _ _ (by rw [drop_bytes23]; exact drop_valid23) drop_lex24
def drop_source22 : List UInt8 := [111] ++ drop_source23
def drop_tokens22 : List String := "o" :: drop_tokens23
theorem drop_bytes22 : bytes "o" = [111] := by rfl
theorem drop_valid22 : valid .identifier [111] drop_source23 = true := by decide
theorem drop_lex22 : Lexes drop_source22 drop_tokens22 := by
  change Lexes ([111] ++ drop_source23) ("o" :: drop_tokens23)
  rw [← drop_bytes22]
  exact .token .identifier "o" _ _ (by rw [drop_bytes22]; exact drop_valid22) drop_lex23
def drop_source21 : List UInt8 := [38] ++ drop_source22
def drop_tokens21 : List String := "&" :: drop_tokens22
theorem drop_bytes21 : bytes "&" = [38] := by rfl
theorem drop_valid21 : valid .punctuator [38] drop_source22 = true := by decide
theorem drop_lex21 : Lexes drop_source21 drop_tokens21 := by
  change Lexes ([38] ++ drop_source22) ("&" :: drop_tokens22)
  rw [← drop_bytes21]
  exact .token .punctuator "&" _ _ (by rw [drop_bytes21]; exact drop_valid21) drop_lex22
def drop_source20 : List UInt8 := [40] ++ drop_source21
def drop_tokens20 : List String := "(" :: drop_tokens21
theorem drop_bytes20 : bytes "(" = [40] := by rfl
theorem drop_valid20 : valid .punctuator [40] drop_source21 = true := by decide
theorem drop_lex20 : Lexes drop_source20 drop_tokens20 := by
  change Lexes ([40] ++ drop_source21) ("(" :: drop_tokens21)
  rw [← drop_bytes20]
  exact .token .punctuator "(" _ _ (by rw [drop_bytes20]; exact drop_valid20) drop_lex21
def drop_source19 : List UInt8 := [97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ drop_source20
def drop_tokens19 : List String := "atomic_load_explicit" :: drop_tokens20
theorem drop_bytes19 : bytes "atomic_load_explicit" = [97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] := by rfl
theorem drop_valid19 : valid .identifier [97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] drop_source20 = true := by decide
theorem drop_lex19 : Lexes drop_source19 drop_tokens19 := by
  change Lexes ([97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ drop_source20) ("atomic_load_explicit" :: drop_tokens20)
  rw [← drop_bytes19]
  exact .token .identifier "atomic_load_explicit" _ _ (by rw [drop_bytes19]; exact drop_valid19) drop_lex20
def drop_source18 : List UInt8 := [40] ++ drop_source19
def drop_tokens18 : List String := "(" :: drop_tokens19
theorem drop_bytes18 : bytes "(" = [40] := by rfl
theorem drop_valid18 : valid .punctuator [40] drop_source19 = true := by decide
theorem drop_lex18 : Lexes drop_source18 drop_tokens18 := by
  change Lexes ([40] ++ drop_source19) ("(" :: drop_tokens19)
  rw [← drop_bytes18]
  exact .token .punctuator "(" _ _ (by rw [drop_bytes18]; exact drop_valid18) drop_lex19
def drop_source17 : List UInt8 := [32] ++ drop_source18
def drop_tokens17 : List String := drop_tokens18
theorem drop_lex17 : Lexes drop_source17 drop_tokens17 :=
  .whitespace [32] _ _ (by decide) drop_lex18
def drop_source16 : List UInt8 := [105, 102] ++ drop_source17
def drop_tokens16 : List String := "if" :: drop_tokens17
theorem drop_bytes16 : bytes "if" = [105, 102] := by rfl
theorem drop_valid16 : valid .identifier [105, 102] drop_source17 = true := by decide
theorem drop_lex16 : Lexes drop_source16 drop_tokens16 := by
  change Lexes ([105, 102] ++ drop_source17) ("if" :: drop_tokens17)
  rw [← drop_bytes16]
  exact .token .identifier "if" _ _ (by rw [drop_bytes16]; exact drop_valid16) drop_lex17
def drop_source15 : List UInt8 := [10, 32, 32, 32, 32] ++ drop_source16
def drop_tokens15 : List String := drop_tokens16
theorem drop_lex15 : Lexes drop_source15 drop_tokens15 :=
  .whitespace [10, 32, 32, 32, 32] _ _ (by decide) drop_lex16
def drop_source14 : List UInt8 := [123] ++ drop_source15
def drop_tokens14 : List String := "{" :: drop_tokens15
theorem drop_bytes14 : bytes "{" = [123] := by rfl
theorem drop_valid14 : valid .punctuator [123] drop_source15 = true := by decide
theorem drop_lex14 : Lexes drop_source14 drop_tokens14 := by
  change Lexes ([123] ++ drop_source15) ("{" :: drop_tokens15)
  rw [← drop_bytes14]
  exact .token .punctuator "{" _ _ (by rw [drop_bytes14]; exact drop_valid14) drop_lex15
def drop_source13 : List UInt8 := [32] ++ drop_source14
def drop_tokens13 : List String := drop_tokens14
theorem drop_lex13 : Lexes drop_source13 drop_tokens13 :=
  .whitespace [32] _ _ (by decide) drop_lex14
def drop_source12 : List UInt8 := [41] ++ drop_source13
def drop_tokens12 : List String := ")" :: drop_tokens13
theorem drop_bytes12 : bytes ")" = [41] := by rfl
theorem drop_valid12 : valid .punctuator [41] drop_source13 = true := by decide
theorem drop_lex12 : Lexes drop_source12 drop_tokens12 := by
  change Lexes ([41] ++ drop_source13) (")" :: drop_tokens13)
  rw [← drop_bytes12]
  exact .token .punctuator ")" _ _ (by rw [drop_bytes12]; exact drop_valid12) drop_lex13
def drop_source11 : List UInt8 := [111] ++ drop_source12
def drop_tokens11 : List String := "o" :: drop_tokens12
theorem drop_bytes11 : bytes "o" = [111] := by rfl
theorem drop_valid11 : valid .identifier [111] drop_source12 = true := by decide
theorem drop_lex11 : Lexes drop_source11 drop_tokens11 := by
  change Lexes ([111] ++ drop_source12) ("o" :: drop_tokens12)
  rw [← drop_bytes11]
  exact .token .identifier "o" _ _ (by rw [drop_bytes11]; exact drop_valid11) drop_lex12
def drop_source10 : List UInt8 := [32] ++ drop_source11
def drop_tokens10 : List String := drop_tokens11
theorem drop_lex10 : Lexes drop_source10 drop_tokens10 :=
  .whitespace [32] _ _ (by decide) drop_lex11
def drop_source9 : List UInt8 := [42] ++ drop_source10
def drop_tokens9 : List String := "*" :: drop_tokens10
theorem drop_bytes9 : bytes "*" = [42] := by rfl
theorem drop_valid9 : valid .punctuator [42] drop_source10 = true := by decide
theorem drop_lex9 : Lexes drop_source9 drop_tokens9 := by
  change Lexes ([42] ++ drop_source10) ("*" :: drop_tokens10)
  rw [← drop_bytes9]
  exact .token .punctuator "*" _ _ (by rw [drop_bytes9]; exact drop_valid9) drop_lex10
def drop_source8 : List UInt8 := [99, 108, 101, 97, 110, 95, 111, 98, 106] ++ drop_source9
def drop_tokens8 : List String := "clean_obj" :: drop_tokens9
theorem drop_bytes8 : bytes "clean_obj" = [99, 108, 101, 97, 110, 95, 111, 98, 106] := by rfl
theorem drop_valid8 : valid .identifier [99, 108, 101, 97, 110, 95, 111, 98, 106] drop_source9 = true := by decide
theorem drop_lex8 : Lexes drop_source8 drop_tokens8 := by
  change Lexes ([99, 108, 101, 97, 110, 95, 111, 98, 106] ++ drop_source9) ("clean_obj" :: drop_tokens9)
  rw [← drop_bytes8]
  exact .token .identifier "clean_obj" _ _ (by rw [drop_bytes8]; exact drop_valid8) drop_lex9
def drop_source7 : List UInt8 := [40] ++ drop_source8
def drop_tokens7 : List String := "(" :: drop_tokens8
theorem drop_bytes7 : bytes "(" = [40] := by rfl
theorem drop_valid7 : valid .punctuator [40] drop_source8 = true := by decide
theorem drop_lex7 : Lexes drop_source7 drop_tokens7 := by
  change Lexes ([40] ++ drop_source8) ("(" :: drop_tokens8)
  rw [← drop_bytes7]
  exact .token .punctuator "(" _ _ (by rw [drop_bytes7]; exact drop_valid7) drop_lex8
def drop_source6 : List UInt8 := [99, 108, 101, 97, 110, 95, 114, 99, 95, 100, 114, 111, 112] ++ drop_source7
def drop_tokens6 : List String := "clean_rc_drop" :: drop_tokens7
theorem drop_bytes6 : bytes "clean_rc_drop" = [99, 108, 101, 97, 110, 95, 114, 99, 95, 100, 114, 111, 112] := by rfl
theorem drop_valid6 : valid .identifier [99, 108, 101, 97, 110, 95, 114, 99, 95, 100, 114, 111, 112] drop_source7 = true := by decide
theorem drop_lex6 : Lexes drop_source6 drop_tokens6 := by
  change Lexes ([99, 108, 101, 97, 110, 95, 114, 99, 95, 100, 114, 111, 112] ++ drop_source7) ("clean_rc_drop" :: drop_tokens7)
  rw [← drop_bytes6]
  exact .token .identifier "clean_rc_drop" _ _ (by rw [drop_bytes6]; exact drop_valid6) drop_lex7
def drop_source5 : List UInt8 := [32] ++ drop_source6
def drop_tokens5 : List String := drop_tokens6
theorem drop_lex5 : Lexes drop_source5 drop_tokens5 :=
  .whitespace [32] _ _ (by decide) drop_lex6
def drop_source4 : List UInt8 := [98, 111, 111, 108] ++ drop_source5
def drop_tokens4 : List String := "bool" :: drop_tokens5
theorem drop_bytes4 : bytes "bool" = [98, 111, 111, 108] := by rfl
theorem drop_valid4 : valid .identifier [98, 111, 111, 108] drop_source5 = true := by decide
theorem drop_lex4 : Lexes drop_source4 drop_tokens4 := by
  change Lexes ([98, 111, 111, 108] ++ drop_source5) ("bool" :: drop_tokens5)
  rw [← drop_bytes4]
  exact .token .identifier "bool" _ _ (by rw [drop_bytes4]; exact drop_valid4) drop_lex5
def drop_source3 : List UInt8 := [32] ++ drop_source4
def drop_tokens3 : List String := drop_tokens4
theorem drop_lex3 : Lexes drop_source3 drop_tokens3 :=
  .whitespace [32] _ _ (by decide) drop_lex4
def drop_source2 : List UInt8 := [105, 110, 108, 105, 110, 101] ++ drop_source3
def drop_tokens2 : List String := "inline" :: drop_tokens3
theorem drop_bytes2 : bytes "inline" = [105, 110, 108, 105, 110, 101] := by rfl
theorem drop_valid2 : valid .identifier [105, 110, 108, 105, 110, 101] drop_source3 = true := by decide
theorem drop_lex2 : Lexes drop_source2 drop_tokens2 := by
  change Lexes ([105, 110, 108, 105, 110, 101] ++ drop_source3) ("inline" :: drop_tokens3)
  rw [← drop_bytes2]
  exact .token .identifier "inline" _ _ (by rw [drop_bytes2]; exact drop_valid2) drop_lex3
def drop_source1 : List UInt8 := [32] ++ drop_source2
def drop_tokens1 : List String := drop_tokens2
theorem drop_lex1 : Lexes drop_source1 drop_tokens1 :=
  .whitespace [32] _ _ (by decide) drop_lex2
def drop_source0 : List UInt8 := [115, 116, 97, 116, 105, 99] ++ drop_source1
def drop_tokens0 : List String := "static" :: drop_tokens1
theorem drop_bytes0 : bytes "static" = [115, 116, 97, 116, 105, 99] := by rfl
theorem drop_valid0 : valid .identifier [115, 116, 97, 116, 105, 99] drop_source1 = true := by decide
theorem drop_lex0 : Lexes drop_source0 drop_tokens0 := by
  change Lexes ([115, 116, 97, 116, 105, 99] ++ drop_source1) ("static" :: drop_tokens1)
  rw [← drop_bytes0]
  exact .token .identifier "static" _ _ (by rw [drop_bytes0]; exact drop_valid0) drop_lex1
theorem drop_source_exact : drop_source0 = CAtomicDropSource.actualSource := by
  simp only [drop_source0, drop_source1, drop_source2, drop_source3, drop_source4, drop_source5, drop_source6, drop_source7, drop_source8, drop_source9, drop_source10, drop_source11, drop_source12, drop_source13, drop_source14, drop_source15, drop_source16, drop_source17, drop_source18, drop_source19, drop_source20, drop_source21, drop_source22, drop_source23, drop_source24, drop_source25, drop_source26, drop_source27, drop_source28, drop_source29, drop_source30, drop_source31, drop_source32, drop_source33, drop_source34, drop_source35, drop_source36, drop_source37, drop_source38, drop_source39, drop_source40, drop_source41, drop_source42, drop_source43, drop_source44, drop_source45, drop_source46, drop_source47, drop_source48, drop_source49, drop_source50, drop_source51, drop_source52, drop_source53, drop_source54, drop_source55, drop_source56, drop_source57, drop_source58, drop_source59, drop_source60, drop_source61, drop_source62, drop_source63, drop_source64, drop_source65, drop_source66, drop_source67, drop_source68, drop_source69, drop_source70, drop_source71, drop_source72, drop_source73, drop_source74, drop_source75, drop_source76, drop_source77, drop_source78, drop_source79, drop_source80, drop_source81, drop_source82, drop_source83, CAtomicDropSource.actualSource, CAtomicDropSource.actual_chunks, CAtomicDropSource.actual_c0, CAtomicDropSource.actual_c1, CAtomicDropSource.actual_c2, CAtomicDropSource.actual_c3, CAtomicDropSource.actual_c4, CAtomicDropSource.actual_c5, CAtomicDropSource.actual_c6, CAtomicDropSource.actual_c7, CAtomicDropSource.actual_c8, CAtomicDropSource.actual_c9, CAtomicDropSource.actual_c10, CAtomicDropSource.actual_c11, CAtomicDropSource.actual_c12, CAtomicDropSource.actual_c13, CAtomicDropSource.actual_c14, CAtomicDropSource.actual_c15, CAtomicDropSource.actual_c16, CAtomicDropSource.actual_c17, CAtomicDropSource.actual_c18, CAtomicDropSource.actual_c19, CAtomicDropSource.actual_c20, CAtomicDropSource.actual_c21, CAtomicDropSource.actual_c22, CAtomicDropSource.actual_c23, CAtomicDropSource.actual_c24, CAtomicDropSource.actual_c25, CAtomicDropSource.actual_c26, CAtomicDropSource.actual_c27, CAtomicDropSource.actual_c28, CAtomicDropSource.actual_c29, CAtomicDropSource.actual_c30, CAtomicDropSource.actual_c31, CAtomicDropSource.actual_c32, CAtomicDropSource.actual_c33, CAtomicDropSource.actual_c34, CAtomicDropSource.actual_c35, CAtomicDropSource.actual_c36, CAtomicDropSource.actual_c37, CAtomicDropSource.actual_c38, CAtomicDropSource.actual_c39, CAtomicDropSource.actual_c40, CAtomicDropSource.actual_c41, CAtomicDropSource.actual_c42, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append]
theorem drop_tokens_exact : drop_tokens0 = CAtomicDropSyntax.tokens CAtomicDropSource.proposal := by rfl
theorem drop_actual_lexes : Lexes CAtomicDropSource.actualSource (CAtomicDropSyntax.tokens CAtomicDropSource.proposal) := by
  rw [← drop_source_exact, ← drop_tokens_exact]
  exact drop_lex0
#print axioms drop_actual_lexes

def increment_source67 : List UInt8 := []
def increment_tokens67 : List String := []
theorem increment_lex67 : Lexes increment_source67 increment_tokens67 := .done
def increment_source66 : List UInt8 := [125] ++ increment_source67
def increment_tokens66 : List String := "}" :: increment_tokens67
theorem increment_bytes66 : bytes "}" = [125] := by rfl
theorem increment_valid66 : valid .punctuator [125] increment_source67 = true := by decide
theorem increment_lex66 : Lexes increment_source66 increment_tokens66 := by
  change Lexes ([125] ++ increment_source67) ("}" :: increment_tokens67)
  rw [← increment_bytes66]
  exact .token .punctuator "}" _ _ (by rw [increment_bytes66]; exact increment_valid66) increment_lex67
def increment_source65 : List UInt8 := [10] ++ increment_source66
def increment_tokens65 : List String := increment_tokens66
theorem increment_lex65 : Lexes increment_source65 increment_tokens65 :=
  .whitespace [10] _ _ (by decide) increment_lex66
def increment_source64 : List UInt8 := [125] ++ increment_source65
def increment_tokens64 : List String := "}" :: increment_tokens65
theorem increment_bytes64 : bytes "}" = [125] := by rfl
theorem increment_valid64 : valid .punctuator [125] increment_source65 = true := by decide
theorem increment_lex64 : Lexes increment_source64 increment_tokens64 := by
  change Lexes ([125] ++ increment_source65) ("}" :: increment_tokens65)
  rw [← increment_bytes64]
  exact .token .punctuator "}" _ _ (by rw [increment_bytes64]; exact increment_valid64) increment_lex65
def increment_source63 : List UInt8 := [10, 32, 32, 32, 32] ++ increment_source64
def increment_tokens63 : List String := increment_tokens64
theorem increment_lex63 : Lexes increment_source63 increment_tokens63 :=
  .whitespace [10, 32, 32, 32, 32] _ _ (by decide) increment_lex64
def increment_source62 : List UInt8 := [59] ++ increment_source63
def increment_tokens62 : List String := ";" :: increment_tokens63
theorem increment_bytes62 : bytes ";" = [59] := by rfl
theorem increment_valid62 : valid .punctuator [59] increment_source63 = true := by decide
theorem increment_lex62 : Lexes increment_source62 increment_tokens62 := by
  change Lexes ([59] ++ increment_source63) (";" :: increment_tokens63)
  rw [← increment_bytes62]
  exact .token .punctuator ";" _ _ (by rw [increment_bytes62]; exact increment_valid62) increment_lex63
def increment_source61 : List UInt8 := [41] ++ increment_source62
def increment_tokens61 : List String := ")" :: increment_tokens62
theorem increment_bytes61 : bytes ")" = [41] := by rfl
theorem increment_valid61 : valid .punctuator [41] increment_source62 = true := by decide
theorem increment_lex61 : Lexes increment_source61 increment_tokens61 := by
  change Lexes ([41] ++ increment_source62) (")" :: increment_tokens62)
  rw [← increment_bytes61]
  exact .token .punctuator ")" _ _ (by rw [increment_bytes61]; exact increment_valid61) increment_lex62
def increment_source60 : List UInt8 := [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] ++ increment_source61
def increment_tokens60 : List String := "memory_order_relaxed" :: increment_tokens61
theorem increment_bytes60 : bytes "memory_order_relaxed" = [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] := by rfl
theorem increment_valid60 : valid .identifier [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] increment_source61 = true := by decide
theorem increment_lex60 : Lexes increment_source60 increment_tokens60 := by
  change Lexes ([109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] ++ increment_source61) ("memory_order_relaxed" :: increment_tokens61)
  rw [← increment_bytes60]
  exact .token .identifier "memory_order_relaxed" _ _ (by rw [increment_bytes60]; exact increment_valid60) increment_lex61
def increment_source59 : List UInt8 := [32] ++ increment_source60
def increment_tokens59 : List String := increment_tokens60
theorem increment_lex59 : Lexes increment_source59 increment_tokens59 :=
  .whitespace [32] _ _ (by decide) increment_lex60
def increment_source58 : List UInt8 := [44] ++ increment_source59
def increment_tokens58 : List String := "," :: increment_tokens59
theorem increment_bytes58 : bytes "," = [44] := by rfl
theorem increment_valid58 : valid .punctuator [44] increment_source59 = true := by decide
theorem increment_lex58 : Lexes increment_source58 increment_tokens58 := by
  change Lexes ([44] ++ increment_source59) ("," :: increment_tokens59)
  rw [← increment_bytes58]
  exact .token .punctuator "," _ _ (by rw [increment_bytes58]; exact increment_valid58) increment_lex59
def increment_source57 : List UInt8 := [49] ++ increment_source58
def increment_tokens57 : List String := "1" :: increment_tokens58
theorem increment_bytes57 : bytes "1" = [49] := by rfl
theorem increment_valid57 : valid .integer01 [49] increment_source58 = true := by decide
theorem increment_lex57 : Lexes increment_source57 increment_tokens57 := by
  change Lexes ([49] ++ increment_source58) ("1" :: increment_tokens58)
  rw [← increment_bytes57]
  exact .token .integer01 "1" _ _ (by rw [increment_bytes57]; exact increment_valid57) increment_lex58
def increment_source56 : List UInt8 := [32] ++ increment_source57
def increment_tokens56 : List String := increment_tokens57
theorem increment_lex56 : Lexes increment_source56 increment_tokens56 :=
  .whitespace [32] _ _ (by decide) increment_lex57
def increment_source55 : List UInt8 := [44] ++ increment_source56
def increment_tokens55 : List String := "," :: increment_tokens56
theorem increment_bytes55 : bytes "," = [44] := by rfl
theorem increment_valid55 : valid .punctuator [44] increment_source56 = true := by decide
theorem increment_lex55 : Lexes increment_source55 increment_tokens55 := by
  change Lexes ([44] ++ increment_source56) ("," :: increment_tokens56)
  rw [← increment_bytes55]
  exact .token .punctuator "," _ _ (by rw [increment_bytes55]; exact increment_valid55) increment_lex56
def increment_source54 : List UInt8 := [114, 101, 102, 95, 99, 111, 117, 110, 116] ++ increment_source55
def increment_tokens54 : List String := "ref_count" :: increment_tokens55
theorem increment_bytes54 : bytes "ref_count" = [114, 101, 102, 95, 99, 111, 117, 110, 116] := by rfl
theorem increment_valid54 : valid .identifier [114, 101, 102, 95, 99, 111, 117, 110, 116] increment_source55 = true := by decide
theorem increment_lex54 : Lexes increment_source54 increment_tokens54 := by
  change Lexes ([114, 101, 102, 95, 99, 111, 117, 110, 116] ++ increment_source55) ("ref_count" :: increment_tokens55)
  rw [← increment_bytes54]
  exact .token .identifier "ref_count" _ _ (by rw [increment_bytes54]; exact increment_valid54) increment_lex55
def increment_source53 : List UInt8 := [46] ++ increment_source54
def increment_tokens53 : List String := "." :: increment_tokens54
theorem increment_bytes53 : bytes "." = [46] := by rfl
theorem increment_valid53 : valid .punctuator [46] increment_source54 = true := by decide
theorem increment_lex53 : Lexes increment_source53 increment_tokens53 := by
  change Lexes ([46] ++ increment_source54) ("." :: increment_tokens54)
  rw [← increment_bytes53]
  exact .token .punctuator "." _ _ (by rw [increment_bytes53]; exact increment_valid53) increment_lex54
def increment_source52 : List UInt8 := [104, 101, 97, 100, 101, 114] ++ increment_source53
def increment_tokens52 : List String := "header" :: increment_tokens53
theorem increment_bytes52 : bytes "header" = [104, 101, 97, 100, 101, 114] := by rfl
theorem increment_valid52 : valid .identifier [104, 101, 97, 100, 101, 114] increment_source53 = true := by decide
theorem increment_lex52 : Lexes increment_source52 increment_tokens52 := by
  change Lexes ([104, 101, 97, 100, 101, 114] ++ increment_source53) ("header" :: increment_tokens53)
  rw [← increment_bytes52]
  exact .token .identifier "header" _ _ (by rw [increment_bytes52]; exact increment_valid52) increment_lex53
def increment_source51 : List UInt8 := [45, 62] ++ increment_source52
def increment_tokens51 : List String := "->" :: increment_tokens52
theorem increment_bytes51 : bytes "->" = [45, 62] := by rfl
theorem increment_valid51 : valid .punctuator [45, 62] increment_source52 = true := by decide
theorem increment_lex51 : Lexes increment_source51 increment_tokens51 := by
  change Lexes ([45, 62] ++ increment_source52) ("->" :: increment_tokens52)
  rw [← increment_bytes51]
  exact .token .punctuator "->" _ _ (by rw [increment_bytes51]; exact increment_valid51) increment_lex52
def increment_source50 : List UInt8 := [111] ++ increment_source51
def increment_tokens50 : List String := "o" :: increment_tokens51
theorem increment_bytes50 : bytes "o" = [111] := by rfl
theorem increment_valid50 : valid .identifier [111] increment_source51 = true := by decide
theorem increment_lex50 : Lexes increment_source50 increment_tokens50 := by
  change Lexes ([111] ++ increment_source51) ("o" :: increment_tokens51)
  rw [← increment_bytes50]
  exact .token .identifier "o" _ _ (by rw [increment_bytes50]; exact increment_valid50) increment_lex51
def increment_source49 : List UInt8 := [38] ++ increment_source50
def increment_tokens49 : List String := "&" :: increment_tokens50
theorem increment_bytes49 : bytes "&" = [38] := by rfl
theorem increment_valid49 : valid .punctuator [38] increment_source50 = true := by decide
theorem increment_lex49 : Lexes increment_source49 increment_tokens49 := by
  change Lexes ([38] ++ increment_source50) ("&" :: increment_tokens50)
  rw [← increment_bytes49]
  exact .token .punctuator "&" _ _ (by rw [increment_bytes49]; exact increment_valid49) increment_lex50
def increment_source48 : List UInt8 := [40] ++ increment_source49
def increment_tokens48 : List String := "(" :: increment_tokens49
theorem increment_bytes48 : bytes "(" = [40] := by rfl
theorem increment_valid48 : valid .punctuator [40] increment_source49 = true := by decide
theorem increment_lex48 : Lexes increment_source48 increment_tokens48 := by
  change Lexes ([40] ++ increment_source49) ("(" :: increment_tokens49)
  rw [← increment_bytes48]
  exact .token .punctuator "(" _ _ (by rw [increment_bytes48]; exact increment_valid48) increment_lex49
def increment_source47 : List UInt8 := [97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 97, 100, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ increment_source48
def increment_tokens47 : List String := "atomic_fetch_add_explicit" :: increment_tokens48
theorem increment_bytes47 : bytes "atomic_fetch_add_explicit" = [97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 97, 100, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] := by rfl
theorem increment_valid47 : valid .identifier [97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 97, 100, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] increment_source48 = true := by decide
theorem increment_lex47 : Lexes increment_source47 increment_tokens47 := by
  change Lexes ([97, 116, 111, 109, 105, 99, 95, 102, 101, 116, 99, 104, 95, 97, 100, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ increment_source48) ("atomic_fetch_add_explicit" :: increment_tokens48)
  rw [← increment_bytes47]
  exact .token .identifier "atomic_fetch_add_explicit" _ _ (by rw [increment_bytes47]; exact increment_valid47) increment_lex48
def increment_source46 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32, 32] ++ increment_source47
def increment_tokens46 : List String := increment_tokens47
theorem increment_lex46 : Lexes increment_source46 increment_tokens46 :=
  .whitespace [10, 32, 32, 32, 32, 32, 32, 32, 32] _ _ (by decide) increment_lex47
def increment_source45 : List UInt8 := [123] ++ increment_source46
def increment_tokens45 : List String := "{" :: increment_tokens46
theorem increment_bytes45 : bytes "{" = [123] := by rfl
theorem increment_valid45 : valid .punctuator [123] increment_source46 = true := by decide
theorem increment_lex45 : Lexes increment_source45 increment_tokens45 := by
  change Lexes ([123] ++ increment_source46) ("{" :: increment_tokens46)
  rw [← increment_bytes45]
  exact .token .punctuator "{" _ _ (by rw [increment_bytes45]; exact increment_valid45) increment_lex46
def increment_source44 : List UInt8 := [32] ++ increment_source45
def increment_tokens44 : List String := increment_tokens45
theorem increment_lex44 : Lexes increment_source44 increment_tokens44 :=
  .whitespace [32] _ _ (by decide) increment_lex45
def increment_source43 : List UInt8 := [41] ++ increment_source44
def increment_tokens43 : List String := ")" :: increment_tokens44
theorem increment_bytes43 : bytes ")" = [41] := by rfl
theorem increment_valid43 : valid .punctuator [41] increment_source44 = true := by decide
theorem increment_lex43 : Lexes increment_source43 increment_tokens43 := by
  change Lexes ([41] ++ increment_source44) (")" :: increment_tokens44)
  rw [← increment_bytes43]
  exact .token .punctuator ")" _ _ (by rw [increment_bytes43]; exact increment_valid43) increment_lex44
def increment_source42 : List UInt8 := [67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89] ++ increment_source43
def increment_tokens42 : List String := "CLEAN_RC_STICKY" :: increment_tokens43
theorem increment_bytes42 : bytes "CLEAN_RC_STICKY" = [67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89] := by rfl
theorem increment_valid42 : valid .identifier [67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89] increment_source43 = true := by decide
theorem increment_lex42 : Lexes increment_source42 increment_tokens42 := by
  change Lexes ([67, 76, 69, 65, 78, 95, 82, 67, 95, 83, 84, 73, 67, 75, 89] ++ increment_source43) ("CLEAN_RC_STICKY" :: increment_tokens43)
  rw [← increment_bytes42]
  exact .token .identifier "CLEAN_RC_STICKY" _ _ (by rw [increment_bytes42]; exact increment_valid42) increment_lex43
def increment_source41 : List UInt8 := [32] ++ increment_source42
def increment_tokens41 : List String := increment_tokens42
theorem increment_lex41 : Lexes increment_source41 increment_tokens41 :=
  .whitespace [32] _ _ (by decide) increment_lex42
def increment_source40 : List UInt8 := [60] ++ increment_source41
def increment_tokens40 : List String := "<" :: increment_tokens41
theorem increment_bytes40 : bytes "<" = [60] := by rfl
theorem increment_valid40 : valid .punctuator [60] increment_source41 = true := by decide
theorem increment_lex40 : Lexes increment_source40 increment_tokens40 := by
  change Lexes ([60] ++ increment_source41) ("<" :: increment_tokens41)
  rw [← increment_bytes40]
  exact .token .punctuator "<" _ _ (by rw [increment_bytes40]; exact increment_valid40) increment_lex41
def increment_source39 : List UInt8 := [32] ++ increment_source40
def increment_tokens39 : List String := increment_tokens40
theorem increment_lex39 : Lexes increment_source39 increment_tokens39 :=
  .whitespace [32] _ _ (by decide) increment_lex40
def increment_source38 : List UInt8 := [41] ++ increment_source39
def increment_tokens38 : List String := ")" :: increment_tokens39
theorem increment_bytes38 : bytes ")" = [41] := by rfl
theorem increment_valid38 : valid .punctuator [41] increment_source39 = true := by decide
theorem increment_lex38 : Lexes increment_source38 increment_tokens38 := by
  change Lexes ([41] ++ increment_source39) (")" :: increment_tokens39)
  rw [← increment_bytes38]
  exact .token .punctuator ")" _ _ (by rw [increment_bytes38]; exact increment_valid38) increment_lex39
def increment_source37 : List UInt8 := [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] ++ increment_source38
def increment_tokens37 : List String := "memory_order_relaxed" :: increment_tokens38
theorem increment_bytes37 : bytes "memory_order_relaxed" = [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] := by rfl
theorem increment_valid37 : valid .identifier [109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] increment_source38 = true := by decide
theorem increment_lex37 : Lexes increment_source37 increment_tokens37 := by
  change Lexes ([109, 101, 109, 111, 114, 121, 95, 111, 114, 100, 101, 114, 95, 114, 101, 108, 97, 120, 101, 100] ++ increment_source38) ("memory_order_relaxed" :: increment_tokens38)
  rw [← increment_bytes37]
  exact .token .identifier "memory_order_relaxed" _ _ (by rw [increment_bytes37]; exact increment_valid37) increment_lex38
def increment_source36 : List UInt8 := [32] ++ increment_source37
def increment_tokens36 : List String := increment_tokens37
theorem increment_lex36 : Lexes increment_source36 increment_tokens36 :=
  .whitespace [32] _ _ (by decide) increment_lex37
def increment_source35 : List UInt8 := [44] ++ increment_source36
def increment_tokens35 : List String := "," :: increment_tokens36
theorem increment_bytes35 : bytes "," = [44] := by rfl
theorem increment_valid35 : valid .punctuator [44] increment_source36 = true := by decide
theorem increment_lex35 : Lexes increment_source35 increment_tokens35 := by
  change Lexes ([44] ++ increment_source36) ("," :: increment_tokens36)
  rw [← increment_bytes35]
  exact .token .punctuator "," _ _ (by rw [increment_bytes35]; exact increment_valid35) increment_lex36
def increment_source34 : List UInt8 := [114, 101, 102, 95, 99, 111, 117, 110, 116] ++ increment_source35
def increment_tokens34 : List String := "ref_count" :: increment_tokens35
theorem increment_bytes34 : bytes "ref_count" = [114, 101, 102, 95, 99, 111, 117, 110, 116] := by rfl
theorem increment_valid34 : valid .identifier [114, 101, 102, 95, 99, 111, 117, 110, 116] increment_source35 = true := by decide
theorem increment_lex34 : Lexes increment_source34 increment_tokens34 := by
  change Lexes ([114, 101, 102, 95, 99, 111, 117, 110, 116] ++ increment_source35) ("ref_count" :: increment_tokens35)
  rw [← increment_bytes34]
  exact .token .identifier "ref_count" _ _ (by rw [increment_bytes34]; exact increment_valid34) increment_lex35
def increment_source33 : List UInt8 := [46] ++ increment_source34
def increment_tokens33 : List String := "." :: increment_tokens34
theorem increment_bytes33 : bytes "." = [46] := by rfl
theorem increment_valid33 : valid .punctuator [46] increment_source34 = true := by decide
theorem increment_lex33 : Lexes increment_source33 increment_tokens33 := by
  change Lexes ([46] ++ increment_source34) ("." :: increment_tokens34)
  rw [← increment_bytes33]
  exact .token .punctuator "." _ _ (by rw [increment_bytes33]; exact increment_valid33) increment_lex34
def increment_source32 : List UInt8 := [104, 101, 97, 100, 101, 114] ++ increment_source33
def increment_tokens32 : List String := "header" :: increment_tokens33
theorem increment_bytes32 : bytes "header" = [104, 101, 97, 100, 101, 114] := by rfl
theorem increment_valid32 : valid .identifier [104, 101, 97, 100, 101, 114] increment_source33 = true := by decide
theorem increment_lex32 : Lexes increment_source32 increment_tokens32 := by
  change Lexes ([104, 101, 97, 100, 101, 114] ++ increment_source33) ("header" :: increment_tokens33)
  rw [← increment_bytes32]
  exact .token .identifier "header" _ _ (by rw [increment_bytes32]; exact increment_valid32) increment_lex33
def increment_source31 : List UInt8 := [45, 62] ++ increment_source32
def increment_tokens31 : List String := "->" :: increment_tokens32
theorem increment_bytes31 : bytes "->" = [45, 62] := by rfl
theorem increment_valid31 : valid .punctuator [45, 62] increment_source32 = true := by decide
theorem increment_lex31 : Lexes increment_source31 increment_tokens31 := by
  change Lexes ([45, 62] ++ increment_source32) ("->" :: increment_tokens32)
  rw [← increment_bytes31]
  exact .token .punctuator "->" _ _ (by rw [increment_bytes31]; exact increment_valid31) increment_lex32
def increment_source30 : List UInt8 := [111] ++ increment_source31
def increment_tokens30 : List String := "o" :: increment_tokens31
theorem increment_bytes30 : bytes "o" = [111] := by rfl
theorem increment_valid30 : valid .identifier [111] increment_source31 = true := by decide
theorem increment_lex30 : Lexes increment_source30 increment_tokens30 := by
  change Lexes ([111] ++ increment_source31) ("o" :: increment_tokens31)
  rw [← increment_bytes30]
  exact .token .identifier "o" _ _ (by rw [increment_bytes30]; exact increment_valid30) increment_lex31
def increment_source29 : List UInt8 := [38] ++ increment_source30
def increment_tokens29 : List String := "&" :: increment_tokens30
theorem increment_bytes29 : bytes "&" = [38] := by rfl
theorem increment_valid29 : valid .punctuator [38] increment_source30 = true := by decide
theorem increment_lex29 : Lexes increment_source29 increment_tokens29 := by
  change Lexes ([38] ++ increment_source30) ("&" :: increment_tokens30)
  rw [← increment_bytes29]
  exact .token .punctuator "&" _ _ (by rw [increment_bytes29]; exact increment_valid29) increment_lex30
def increment_source28 : List UInt8 := [40] ++ increment_source29
def increment_tokens28 : List String := "(" :: increment_tokens29
theorem increment_bytes28 : bytes "(" = [40] := by rfl
theorem increment_valid28 : valid .punctuator [40] increment_source29 = true := by decide
theorem increment_lex28 : Lexes increment_source28 increment_tokens28 := by
  change Lexes ([40] ++ increment_source29) ("(" :: increment_tokens29)
  rw [← increment_bytes28]
  exact .token .punctuator "(" _ _ (by rw [increment_bytes28]; exact increment_valid28) increment_lex29
def increment_source27 : List UInt8 := [97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ increment_source28
def increment_tokens27 : List String := "atomic_load_explicit" :: increment_tokens28
theorem increment_bytes27 : bytes "atomic_load_explicit" = [97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] := by rfl
theorem increment_valid27 : valid .identifier [97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] increment_source28 = true := by decide
theorem increment_lex27 : Lexes increment_source27 increment_tokens27 := by
  change Lexes ([97, 116, 111, 109, 105, 99, 95, 108, 111, 97, 100, 95, 101, 120, 112, 108, 105, 99, 105, 116] ++ increment_source28) ("atomic_load_explicit" :: increment_tokens28)
  rw [← increment_bytes27]
  exact .token .identifier "atomic_load_explicit" _ _ (by rw [increment_bytes27]; exact increment_valid27) increment_lex28
def increment_source26 : List UInt8 := [10, 32, 32, 32, 32, 32, 32, 32, 32] ++ increment_source27
def increment_tokens26 : List String := increment_tokens27
theorem increment_lex26 : Lexes increment_source26 increment_tokens26 :=
  .whitespace [10, 32, 32, 32, 32, 32, 32, 32, 32] _ _ (by decide) increment_lex27
def increment_source25 : List UInt8 := [38, 38] ++ increment_source26
def increment_tokens25 : List String := "&&" :: increment_tokens26
theorem increment_bytes25 : bytes "&&" = [38, 38] := by rfl
theorem increment_valid25 : valid .punctuator [38, 38] increment_source26 = true := by decide
theorem increment_lex25 : Lexes increment_source25 increment_tokens25 := by
  change Lexes ([38, 38] ++ increment_source26) ("&&" :: increment_tokens26)
  rw [← increment_bytes25]
  exact .token .punctuator "&&" _ _ (by rw [increment_bytes25]; exact increment_valid25) increment_lex26
def increment_source24 : List UInt8 := [32] ++ increment_source25
def increment_tokens24 : List String := increment_tokens25
theorem increment_lex24 : Lexes increment_source24 increment_tokens24 :=
  .whitespace [32] _ _ (by decide) increment_lex25
def increment_source23 : List UInt8 := [41] ++ increment_source24
def increment_tokens23 : List String := ")" :: increment_tokens24
theorem increment_bytes23 : bytes ")" = [41] := by rfl
theorem increment_valid23 : valid .punctuator [41] increment_source24 = true := by decide
theorem increment_lex23 : Lexes increment_source23 increment_tokens23 := by
  change Lexes ([41] ++ increment_source24) (")" :: increment_tokens24)
  rw [← increment_bytes23]
  exact .token .punctuator ")" _ _ (by rw [increment_bytes23]; exact increment_valid23) increment_lex24
def increment_source22 : List UInt8 := [111] ++ increment_source23
def increment_tokens22 : List String := "o" :: increment_tokens23
theorem increment_bytes22 : bytes "o" = [111] := by rfl
theorem increment_valid22 : valid .identifier [111] increment_source23 = true := by decide
theorem increment_lex22 : Lexes increment_source22 increment_tokens22 := by
  change Lexes ([111] ++ increment_source23) ("o" :: increment_tokens23)
  rw [← increment_bytes22]
  exact .token .identifier "o" _ _ (by rw [increment_bytes22]; exact increment_valid22) increment_lex23
def increment_source21 : List UInt8 := [40] ++ increment_source22
def increment_tokens21 : List String := "(" :: increment_tokens22
theorem increment_bytes21 : bytes "(" = [40] := by rfl
theorem increment_valid21 : valid .punctuator [40] increment_source22 = true := by decide
theorem increment_lex21 : Lexes increment_source21 increment_tokens21 := by
  change Lexes ([40] ++ increment_source22) ("(" :: increment_tokens22)
  rw [← increment_bytes21]
  exact .token .punctuator "(" _ _ (by rw [increment_bytes21]; exact increment_valid21) increment_lex22
def increment_source20 : List UInt8 := [99, 108, 101, 97, 110, 95, 105, 115, 95, 115, 99, 97, 108, 97, 114] ++ increment_source21
def increment_tokens20 : List String := "clean_is_scalar" :: increment_tokens21
theorem increment_bytes20 : bytes "clean_is_scalar" = [99, 108, 101, 97, 110, 95, 105, 115, 95, 115, 99, 97, 108, 97, 114] := by rfl
theorem increment_valid20 : valid .identifier [99, 108, 101, 97, 110, 95, 105, 115, 95, 115, 99, 97, 108, 97, 114] increment_source21 = true := by decide
theorem increment_lex20 : Lexes increment_source20 increment_tokens20 := by
  change Lexes ([99, 108, 101, 97, 110, 95, 105, 115, 95, 115, 99, 97, 108, 97, 114] ++ increment_source21) ("clean_is_scalar" :: increment_tokens21)
  rw [← increment_bytes20]
  exact .token .identifier "clean_is_scalar" _ _ (by rw [increment_bytes20]; exact increment_valid20) increment_lex21
def increment_source19 : List UInt8 := [33] ++ increment_source20
def increment_tokens19 : List String := "!" :: increment_tokens20
theorem increment_bytes19 : bytes "!" = [33] := by rfl
theorem increment_valid19 : valid .punctuator [33] increment_source20 = true := by decide
theorem increment_lex19 : Lexes increment_source19 increment_tokens19 := by
  change Lexes ([33] ++ increment_source20) ("!" :: increment_tokens20)
  rw [← increment_bytes19]
  exact .token .punctuator "!" _ _ (by rw [increment_bytes19]; exact increment_valid19) increment_lex20
def increment_source18 : List UInt8 := [40] ++ increment_source19
def increment_tokens18 : List String := "(" :: increment_tokens19
theorem increment_bytes18 : bytes "(" = [40] := by rfl
theorem increment_valid18 : valid .punctuator [40] increment_source19 = true := by decide
theorem increment_lex18 : Lexes increment_source18 increment_tokens18 := by
  change Lexes ([40] ++ increment_source19) ("(" :: increment_tokens19)
  rw [← increment_bytes18]
  exact .token .punctuator "(" _ _ (by rw [increment_bytes18]; exact increment_valid18) increment_lex19
def increment_source17 : List UInt8 := [32] ++ increment_source18
def increment_tokens17 : List String := increment_tokens18
theorem increment_lex17 : Lexes increment_source17 increment_tokens17 :=
  .whitespace [32] _ _ (by decide) increment_lex18
def increment_source16 : List UInt8 := [105, 102] ++ increment_source17
def increment_tokens16 : List String := "if" :: increment_tokens17
theorem increment_bytes16 : bytes "if" = [105, 102] := by rfl
theorem increment_valid16 : valid .identifier [105, 102] increment_source17 = true := by decide
theorem increment_lex16 : Lexes increment_source16 increment_tokens16 := by
  change Lexes ([105, 102] ++ increment_source17) ("if" :: increment_tokens17)
  rw [← increment_bytes16]
  exact .token .identifier "if" _ _ (by rw [increment_bytes16]; exact increment_valid16) increment_lex17
def increment_source15 : List UInt8 := [10, 32, 32, 32, 32] ++ increment_source16
def increment_tokens15 : List String := increment_tokens16
theorem increment_lex15 : Lexes increment_source15 increment_tokens15 :=
  .whitespace [10, 32, 32, 32, 32] _ _ (by decide) increment_lex16
def increment_source14 : List UInt8 := [123] ++ increment_source15
def increment_tokens14 : List String := "{" :: increment_tokens15
theorem increment_bytes14 : bytes "{" = [123] := by rfl
theorem increment_valid14 : valid .punctuator [123] increment_source15 = true := by decide
theorem increment_lex14 : Lexes increment_source14 increment_tokens14 := by
  change Lexes ([123] ++ increment_source15) ("{" :: increment_tokens15)
  rw [← increment_bytes14]
  exact .token .punctuator "{" _ _ (by rw [increment_bytes14]; exact increment_valid14) increment_lex15
def increment_source13 : List UInt8 := [32] ++ increment_source14
def increment_tokens13 : List String := increment_tokens14
theorem increment_lex13 : Lexes increment_source13 increment_tokens13 :=
  .whitespace [32] _ _ (by decide) increment_lex14
def increment_source12 : List UInt8 := [41] ++ increment_source13
def increment_tokens12 : List String := ")" :: increment_tokens13
theorem increment_bytes12 : bytes ")" = [41] := by rfl
theorem increment_valid12 : valid .punctuator [41] increment_source13 = true := by decide
theorem increment_lex12 : Lexes increment_source12 increment_tokens12 := by
  change Lexes ([41] ++ increment_source13) (")" :: increment_tokens13)
  rw [← increment_bytes12]
  exact .token .punctuator ")" _ _ (by rw [increment_bytes12]; exact increment_valid12) increment_lex13
def increment_source11 : List UInt8 := [111] ++ increment_source12
def increment_tokens11 : List String := "o" :: increment_tokens12
theorem increment_bytes11 : bytes "o" = [111] := by rfl
theorem increment_valid11 : valid .identifier [111] increment_source12 = true := by decide
theorem increment_lex11 : Lexes increment_source11 increment_tokens11 := by
  change Lexes ([111] ++ increment_source12) ("o" :: increment_tokens12)
  rw [← increment_bytes11]
  exact .token .identifier "o" _ _ (by rw [increment_bytes11]; exact increment_valid11) increment_lex12
def increment_source10 : List UInt8 := [32] ++ increment_source11
def increment_tokens10 : List String := increment_tokens11
theorem increment_lex10 : Lexes increment_source10 increment_tokens10 :=
  .whitespace [32] _ _ (by decide) increment_lex11
def increment_source9 : List UInt8 := [42] ++ increment_source10
def increment_tokens9 : List String := "*" :: increment_tokens10
theorem increment_bytes9 : bytes "*" = [42] := by rfl
theorem increment_valid9 : valid .punctuator [42] increment_source10 = true := by decide
theorem increment_lex9 : Lexes increment_source9 increment_tokens9 := by
  change Lexes ([42] ++ increment_source10) ("*" :: increment_tokens10)
  rw [← increment_bytes9]
  exact .token .punctuator "*" _ _ (by rw [increment_bytes9]; exact increment_valid9) increment_lex10
def increment_source8 : List UInt8 := [99, 108, 101, 97, 110, 95, 111, 98, 106] ++ increment_source9
def increment_tokens8 : List String := "clean_obj" :: increment_tokens9
theorem increment_bytes8 : bytes "clean_obj" = [99, 108, 101, 97, 110, 95, 111, 98, 106] := by rfl
theorem increment_valid8 : valid .identifier [99, 108, 101, 97, 110, 95, 111, 98, 106] increment_source9 = true := by decide
theorem increment_lex8 : Lexes increment_source8 increment_tokens8 := by
  change Lexes ([99, 108, 101, 97, 110, 95, 111, 98, 106] ++ increment_source9) ("clean_obj" :: increment_tokens9)
  rw [← increment_bytes8]
  exact .token .identifier "clean_obj" _ _ (by rw [increment_bytes8]; exact increment_valid8) increment_lex9
def increment_source7 : List UInt8 := [40] ++ increment_source8
def increment_tokens7 : List String := "(" :: increment_tokens8
theorem increment_bytes7 : bytes "(" = [40] := by rfl
theorem increment_valid7 : valid .punctuator [40] increment_source8 = true := by decide
theorem increment_lex7 : Lexes increment_source7 increment_tokens7 := by
  change Lexes ([40] ++ increment_source8) ("(" :: increment_tokens8)
  rw [← increment_bytes7]
  exact .token .punctuator "(" _ _ (by rw [increment_bytes7]; exact increment_valid7) increment_lex8
def increment_source6 : List UInt8 := [99, 108, 101, 97, 110, 95, 105, 110, 99] ++ increment_source7
def increment_tokens6 : List String := "clean_inc" :: increment_tokens7
theorem increment_bytes6 : bytes "clean_inc" = [99, 108, 101, 97, 110, 95, 105, 110, 99] := by rfl
theorem increment_valid6 : valid .identifier [99, 108, 101, 97, 110, 95, 105, 110, 99] increment_source7 = true := by decide
theorem increment_lex6 : Lexes increment_source6 increment_tokens6 := by
  change Lexes ([99, 108, 101, 97, 110, 95, 105, 110, 99] ++ increment_source7) ("clean_inc" :: increment_tokens7)
  rw [← increment_bytes6]
  exact .token .identifier "clean_inc" _ _ (by rw [increment_bytes6]; exact increment_valid6) increment_lex7
def increment_source5 : List UInt8 := [32] ++ increment_source6
def increment_tokens5 : List String := increment_tokens6
theorem increment_lex5 : Lexes increment_source5 increment_tokens5 :=
  .whitespace [32] _ _ (by decide) increment_lex6
def increment_source4 : List UInt8 := [118, 111, 105, 100] ++ increment_source5
def increment_tokens4 : List String := "void" :: increment_tokens5
theorem increment_bytes4 : bytes "void" = [118, 111, 105, 100] := by rfl
theorem increment_valid4 : valid .identifier [118, 111, 105, 100] increment_source5 = true := by decide
theorem increment_lex4 : Lexes increment_source4 increment_tokens4 := by
  change Lexes ([118, 111, 105, 100] ++ increment_source5) ("void" :: increment_tokens5)
  rw [← increment_bytes4]
  exact .token .identifier "void" _ _ (by rw [increment_bytes4]; exact increment_valid4) increment_lex5
def increment_source3 : List UInt8 := [32] ++ increment_source4
def increment_tokens3 : List String := increment_tokens4
theorem increment_lex3 : Lexes increment_source3 increment_tokens3 :=
  .whitespace [32] _ _ (by decide) increment_lex4
def increment_source2 : List UInt8 := [105, 110, 108, 105, 110, 101] ++ increment_source3
def increment_tokens2 : List String := "inline" :: increment_tokens3
theorem increment_bytes2 : bytes "inline" = [105, 110, 108, 105, 110, 101] := by rfl
theorem increment_valid2 : valid .identifier [105, 110, 108, 105, 110, 101] increment_source3 = true := by decide
theorem increment_lex2 : Lexes increment_source2 increment_tokens2 := by
  change Lexes ([105, 110, 108, 105, 110, 101] ++ increment_source3) ("inline" :: increment_tokens3)
  rw [← increment_bytes2]
  exact .token .identifier "inline" _ _ (by rw [increment_bytes2]; exact increment_valid2) increment_lex3
def increment_source1 : List UInt8 := [32] ++ increment_source2
def increment_tokens1 : List String := increment_tokens2
theorem increment_lex1 : Lexes increment_source1 increment_tokens1 :=
  .whitespace [32] _ _ (by decide) increment_lex2
def increment_source0 : List UInt8 := [115, 116, 97, 116, 105, 99] ++ increment_source1
def increment_tokens0 : List String := "static" :: increment_tokens1
theorem increment_bytes0 : bytes "static" = [115, 116, 97, 116, 105, 99] := by rfl
theorem increment_valid0 : valid .identifier [115, 116, 97, 116, 105, 99] increment_source1 = true := by decide
theorem increment_lex0 : Lexes increment_source0 increment_tokens0 := by
  change Lexes ([115, 116, 97, 116, 105, 99] ++ increment_source1) ("static" :: increment_tokens1)
  rw [← increment_bytes0]
  exact .token .identifier "static" _ _ (by rw [increment_bytes0]; exact increment_valid0) increment_lex1
theorem increment_source_exact : increment_source0 = CAtomicIncrementSource.actualSource := by
  simp only [increment_source0, increment_source1, increment_source2, increment_source3, increment_source4, increment_source5, increment_source6, increment_source7, increment_source8, increment_source9, increment_source10, increment_source11, increment_source12, increment_source13, increment_source14, increment_source15, increment_source16, increment_source17, increment_source18, increment_source19, increment_source20, increment_source21, increment_source22, increment_source23, increment_source24, increment_source25, increment_source26, increment_source27, increment_source28, increment_source29, increment_source30, increment_source31, increment_source32, increment_source33, increment_source34, increment_source35, increment_source36, increment_source37, increment_source38, increment_source39, increment_source40, increment_source41, increment_source42, increment_source43, increment_source44, increment_source45, increment_source46, increment_source47, increment_source48, increment_source49, increment_source50, increment_source51, increment_source52, increment_source53, increment_source54, increment_source55, increment_source56, increment_source57, increment_source58, increment_source59, increment_source60, increment_source61, increment_source62, increment_source63, increment_source64, increment_source65, increment_source66, increment_source67, CAtomicIncrementSource.actualSource, CAtomicIncrementSource.actual_chunks, CAtomicIncrementSource.actual_c0, CAtomicIncrementSource.actual_c1, CAtomicIncrementSource.actual_c2, CAtomicIncrementSource.actual_c3, CAtomicIncrementSource.actual_c4, CAtomicIncrementSource.actual_c5, CAtomicIncrementSource.actual_c6, CAtomicIncrementSource.actual_c7, CAtomicIncrementSource.actual_c8, CAtomicIncrementSource.actual_c9, CAtomicIncrementSource.actual_c10, CAtomicIncrementSource.actual_c11, CAtomicIncrementSource.actual_c12, CAtomicIncrementSource.actual_c13, CAtomicIncrementSource.actual_c14, CAtomicIncrementSource.actual_c15, CAtomicIncrementSource.actual_c16, CAtomicIncrementSource.actual_c17, CAtomicIncrementSource.actual_c18, CAtomicIncrementSource.actual_c19, CAtomicIncrementSource.actual_c20, CAtomicIncrementSource.actual_c21, CAtomicIncrementSource.actual_c22, CAtomicIncrementSource.actual_c23, CAtomicIncrementSource.actual_c24, CAtomicIncrementSource.actual_c25, CAtomicIncrementSource.actual_c26, CAtomicIncrementSource.actual_c27, CAtomicIncrementSource.actual_c28, CAtomicIncrementSource.actual_c29, CAtomicIncrementSource.actual_c30, CAtomicIncrementSource.actual_c31, CAtomicIncrementSource.actual_c32, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append]
theorem increment_tokens_exact : increment_tokens0 = CAtomicIncrementSyntax.tokens CAtomicIncrementSource.proposal := by rfl
theorem increment_actual_lexes : Lexes CAtomicIncrementSource.actualSource (CAtomicIncrementSyntax.tokens CAtomicIncrementSource.proposal) := by
  rw [← increment_source_exact, ← increment_tokens_exact]
  exact increment_lex0
#print axioms increment_actual_lexes

end C11ActualTokens
