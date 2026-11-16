-- Hand-written vectors for the hand-authored runtime (SpecrPrelude.lean).
-- Check with: clean check <(cat SpecrPrelude.lean PreludeVectors.lean)
theorem p_div1 : SInt.div (-7) 3 = SOut.ok (-2) := rfl
theorem p_rem1 : SInt.rem (-7) 3 = SOut.ok (-1) := rfl
theorem p_rem2 : SInt.rem 7 (-3) = SOut.ok 1 := rfl
theorem p_re : SInt.rem_euclid (-1) 8 = SOut.ok 7 := rfl
theorem p_band : SInt.band 171 (-214) = 42 := rfl
theorem p_band2 : SInt.band (-2645) 62 = 42 := rfl
theorem p_band3 : SInt.band (-41) (-10) = -42 := rfl
theorem p_bor : SInt.bor 6 (-46) = -42 := rfl
theorem p_bor2 : SInt.bor (-58) (-46) = -42 := rfl
theorem p_bxor : SInt.bxor 41 (-1) = -42 := rfl
theorem p_bxor2 : SInt.bxor (-1) (-43) = 42 := rfl
theorem p_shr : SInt.shr (-4) 1 = SOut.ok (-2) := rfl
theorem p_shr2 : SInt.shr (-1) 1 = SOut.ok (-1) := rfl
theorem p_bib : SInt.bring_in_bounds 128 MR_Signedness.Signed 1 = SOut.ok (-128) := rfl
theorem p_bib2 : SInt.bring_in_bounds (-1) MR_Signedness.Unsigned 8 = SOut.ok 18446744073709551615 := rfl
theorem p_enc : SEndian.encode MR_Endianness.LittleEndian MR_Signedness.Signed 4 (-2) = SOut.ok (some [254, 255, 255, 255]) := rfl
theorem p_dec : SEndian.decode MR_Endianness.LittleEndian MR_Signedness.Signed [254, 255, 255, 255] = SOut.ok (-2) := rfl
theorem p_dec2 : SEndian.decode MR_Endianness.LittleEndian MR_Signedness.Unsigned [254, 255, 255, 255] = SOut.ok 4294967294 := rfl
theorem p_pow2 : SInt.is_power_of_two 64 = true := rfl
theorem p_pow3 : SInt.is_power_of_two 12 = false := rfl
theorem p_str : SInt.toString (-120) = "-120" := rfl
theorem p_map : SMap.insert Nat.beq [(1, (5:Int))] 2 7 = (none, [(1, 5), (2, 7)]) := rfl
theorem p_sort : SList.sortByIntKeyS [((8:Int), true), (0, false), (4, true)] (fun (p : Int × Bool) (s : Unit) => SOut.ok (p.1, s)) () = SOut.ok ([(0, false), (4, true), (8, true)], ()) := rfl
theorem p_pick : SOut.runLeast 100 (SPick.choose { start := 1, «end» := 18446744073709551616, divisor := 8 } (fun (c : Int) (s : Unit) => SOut.ok (SInt.blt 20 c, s)) ()) = SOut.ok (24, ()) := rfl
theorem p_pick_oracle : SOut.runOracle (fun (_ : List Nat) => 3) (fun (_ : List Nat) => 0) (SPick.choose { start := 1, «end» := 18446744073709551616, divisor := 8 } (fun (c : Int) (s : Unit) => SOut.ok (SInt.blt 20 c, s)) ()) = SOut.ok (32, ()) := rfl
theorem p_pick_oracle_reject : SOut.runOracle (fun (_ : List Nat) => 0) (fun (_ : List Nat) => 0) (SPick.choose { start := 1, «end» := 18446744073709551616, divisor := 8 } (fun (c : Int) (s : Unit) => SOut.ok (SInt.blt 20 c, s)) ()) = SOut.reject := rfl
theorem p_predict : SOut.runLeast 100 (SPredict.choose (fun (i : Nat) => match i with | 0 => some false | 1 => some true | _ => none) (fun (b : Bool) (s : Unit) => SOut.ok (b, s)) ()) = SOut.ok (true, ()) := rfl
theorem p_predict_oracle : SOut.runOracle (fun (_ : List Nat) => 0) (fun (_ : List Nat) => 1) (SPredict.choose (fun (i : Nat) => match i with | 0 => some false | 1 => some true | _ => none) (fun (b : Bool) (s : Unit) => SOut.ok (true, s)) ()) = SOut.ok (true, ()) := rfl
theorem p_dc : SInt.div_ceil (-23) 8 = SOut.ok (-2) := rfl
theorem p_nm : SInt.next_multiple_of 23 (-8) = SOut.ok 16 := rfl
