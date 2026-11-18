-- Copyright 2026 Andrew Yates | Apache-2.0
import C11PredefinedCuts
namespace C11PredefinedLookupCuts
open C11PredefinedRecords C11PredefinedData
def rows_0_15 : List Record := [record0, record1, record2, record3, record4, record5, record6, record7, record8, record9, record10, record11, record12, record13, record14]
def rows_0_15_reversed : List Record := [record14, record13, record12, record11, record10, record9, record8, record7, record6, record5, record4, record3, record2, record1, record0]
theorem rows_0_15_segment : reversed15 = rows_0_15_reversed ++ reversed0 := by rfl
theorem rows_0_15_forward : rows_0_15_reversed.reverse = rows_0_15 := by rfl
def rows_15_30 : List Record := [record15, record16, record17, record18, record19, record20, record21, record22, record23, record24, record25, record26, record27, record28, record29]
def rows_15_30_reversed : List Record := [record29, record28, record27, record26, record25, record24, record23, record22, record21, record20, record19, record18, record17, record16, record15]
theorem rows_15_30_segment : reversed30 = rows_15_30_reversed ++ reversed15 := by rfl
theorem rows_15_30_forward : rows_15_30_reversed.reverse = rows_15_30 := by rfl
def rows_0_30 : List Record := rows_0_15 ++ rows_15_30
def rows_0_30_reversed : List Record := rows_15_30_reversed ++ rows_0_15_reversed
theorem rows_0_30_segment : reversed30 = rows_0_30_reversed ++ reversed0 := by
  rw [rows_15_30_segment, rows_0_15_segment]
  unfold rows_0_30_reversed
  simp only [List.append_assoc]
theorem rows_0_30_forward : rows_0_30_reversed.reverse = rows_0_30 := by
  rw [rows_0_30_reversed, List.reverse_append, rows_0_15_forward, rows_15_30_forward]
  rfl
def rows_30_45 : List Record := [record30, record31, record32, record33, record34, record35, record36, record37, record38, record39, record40, record41, record42, record43, record44]
def rows_30_45_reversed : List Record := [record44, record43, record42, record41, record40, record39, record38, record37, record36, record35, record34, record33, record32, record31, record30]
theorem rows_30_45_segment : reversed45 = rows_30_45_reversed ++ reversed30 := by rfl
theorem rows_30_45_forward : rows_30_45_reversed.reverse = rows_30_45 := by rfl
def rows_45_60 : List Record := [record45, record46, record47, record48, record49, record50, record51, record52, record53, record54, record55, record56, record57, record58, record59]
def rows_45_60_reversed : List Record := [record59, record58, record57, record56, record55, record54, record53, record52, record51, record50, record49, record48, record47, record46, record45]
theorem rows_45_60_segment : reversed60 = rows_45_60_reversed ++ reversed45 := by rfl
theorem rows_45_60_forward : rows_45_60_reversed.reverse = rows_45_60 := by rfl
def rows_30_60 : List Record := rows_30_45 ++ rows_45_60
def rows_30_60_reversed : List Record := rows_45_60_reversed ++ rows_30_45_reversed
theorem rows_30_60_segment : reversed60 = rows_30_60_reversed ++ reversed30 := by
  rw [rows_45_60_segment, rows_30_45_segment]
  unfold rows_30_60_reversed
  simp only [List.append_assoc]
theorem rows_30_60_forward : rows_30_60_reversed.reverse = rows_30_60 := by
  rw [rows_30_60_reversed, List.reverse_append, rows_30_45_forward, rows_45_60_forward]
  rfl
def rows_0_60 : List Record := rows_0_30 ++ rows_30_60
def rows_0_60_reversed : List Record := rows_30_60_reversed ++ rows_0_30_reversed
theorem rows_0_60_segment : reversed60 = rows_0_60_reversed ++ reversed0 := by
  rw [rows_30_60_segment, rows_0_30_segment]
  unfold rows_0_60_reversed
  simp only [List.append_assoc]
theorem rows_0_60_forward : rows_0_60_reversed.reverse = rows_0_60 := by
  rw [rows_0_60_reversed, List.reverse_append, rows_0_30_forward, rows_30_60_forward]
  rfl
def rows_60_75 : List Record := [record60, record61, record62, record63, record64, record65, record66, record67, record68, record69, record70, record71, record72, record73, record74]
def rows_60_75_reversed : List Record := [record74, record73, record72, record71, record70, record69, record68, record67, record66, record65, record64, record63, record62, record61, record60]
theorem rows_60_75_segment : reversed75 = rows_60_75_reversed ++ reversed60 := by rfl
theorem rows_60_75_forward : rows_60_75_reversed.reverse = rows_60_75 := by rfl
def rows_75_90 : List Record := [record75, record76, record77, record78, record79, record80, record81, record82, record83, record84, record85, record86, record87, record88, record89]
def rows_75_90_reversed : List Record := [record89, record88, record87, record86, record85, record84, record83, record82, record81, record80, record79, record78, record77, record76, record75]
theorem rows_75_90_segment : reversed90 = rows_75_90_reversed ++ reversed75 := by rfl
theorem rows_75_90_forward : rows_75_90_reversed.reverse = rows_75_90 := by rfl
def rows_60_90 : List Record := rows_60_75 ++ rows_75_90
def rows_60_90_reversed : List Record := rows_75_90_reversed ++ rows_60_75_reversed
theorem rows_60_90_segment : reversed90 = rows_60_90_reversed ++ reversed60 := by
  rw [rows_75_90_segment, rows_60_75_segment]
  unfold rows_60_90_reversed
  simp only [List.append_assoc]
theorem rows_60_90_forward : rows_60_90_reversed.reverse = rows_60_90 := by
  rw [rows_60_90_reversed, List.reverse_append, rows_60_75_forward, rows_75_90_forward]
  rfl
def rows_90_105 : List Record := [record90, record91, record92, record93, record94, record95, record96, record97, record98, record99, record100, record101, record102, record103, record104]
def rows_90_105_reversed : List Record := [record104, record103, record102, record101, record100, record99, record98, record97, record96, record95, record94, record93, record92, record91, record90]
theorem rows_90_105_segment : reversed105 = rows_90_105_reversed ++ reversed90 := by rfl
theorem rows_90_105_forward : rows_90_105_reversed.reverse = rows_90_105 := by rfl
def rows_105_120 : List Record := [record105, record106, record107, record108, record109, record110, record111, record112, record113, record114, record115, record116, record117, record118, record119]
def rows_105_120_reversed : List Record := [record119, record118, record117, record116, record115, record114, record113, record112, record111, record110, record109, record108, record107, record106, record105]
theorem rows_105_120_segment : reversed120 = rows_105_120_reversed ++ reversed105 := by rfl
theorem rows_105_120_forward : rows_105_120_reversed.reverse = rows_105_120 := by rfl
def rows_90_120 : List Record := rows_90_105 ++ rows_105_120
def rows_90_120_reversed : List Record := rows_105_120_reversed ++ rows_90_105_reversed
theorem rows_90_120_segment : reversed120 = rows_90_120_reversed ++ reversed90 := by
  rw [rows_105_120_segment, rows_90_105_segment]
  unfold rows_90_120_reversed
  simp only [List.append_assoc]
theorem rows_90_120_forward : rows_90_120_reversed.reverse = rows_90_120 := by
  rw [rows_90_120_reversed, List.reverse_append, rows_90_105_forward, rows_105_120_forward]
  rfl
def rows_60_120 : List Record := rows_60_90 ++ rows_90_120
def rows_60_120_reversed : List Record := rows_90_120_reversed ++ rows_60_90_reversed
theorem rows_60_120_segment : reversed120 = rows_60_120_reversed ++ reversed60 := by
  rw [rows_90_120_segment, rows_60_90_segment]
  unfold rows_60_120_reversed
  simp only [List.append_assoc]
theorem rows_60_120_forward : rows_60_120_reversed.reverse = rows_60_120 := by
  rw [rows_60_120_reversed, List.reverse_append, rows_60_90_forward, rows_90_120_forward]
  rfl
def rows_0_120 : List Record := rows_0_60 ++ rows_60_120
def rows_0_120_reversed : List Record := rows_60_120_reversed ++ rows_0_60_reversed
theorem rows_0_120_segment : reversed120 = rows_0_120_reversed ++ reversed0 := by
  rw [rows_60_120_segment, rows_0_60_segment]
  unfold rows_0_120_reversed
  simp only [List.append_assoc]
theorem rows_0_120_forward : rows_0_120_reversed.reverse = rows_0_120 := by
  rw [rows_0_120_reversed, List.reverse_append, rows_0_60_forward, rows_60_120_forward]
  rfl
def rows_120_135 : List Record := [record120, record121, record122, record123, record124, record125, record126, record127, record128, record129, record130, record131, record132, record133, record134]
def rows_120_135_reversed : List Record := [record134, record133, record132, record131, record130, record129, record128, record127, record126, record125, record124, record123, record122, record121, record120]
theorem rows_120_135_segment : reversed135 = rows_120_135_reversed ++ reversed120 := by rfl
theorem rows_120_135_forward : rows_120_135_reversed.reverse = rows_120_135 := by rfl
def rows_135_150 : List Record := [record135, record136, record137, record138, record139, record140, record141, record142, record143, record144, record145, record146, record147, record148, record149]
def rows_135_150_reversed : List Record := [record149, record148, record147, record146, record145, record144, record143, record142, record141, record140, record139, record138, record137, record136, record135]
theorem rows_135_150_segment : reversed150 = rows_135_150_reversed ++ reversed135 := by rfl
theorem rows_135_150_forward : rows_135_150_reversed.reverse = rows_135_150 := by rfl
def rows_120_150 : List Record := rows_120_135 ++ rows_135_150
def rows_120_150_reversed : List Record := rows_135_150_reversed ++ rows_120_135_reversed
theorem rows_120_150_segment : reversed150 = rows_120_150_reversed ++ reversed120 := by
  rw [rows_135_150_segment, rows_120_135_segment]
  unfold rows_120_150_reversed
  simp only [List.append_assoc]
theorem rows_120_150_forward : rows_120_150_reversed.reverse = rows_120_150 := by
  rw [rows_120_150_reversed, List.reverse_append, rows_120_135_forward, rows_135_150_forward]
  rfl
def rows_150_165 : List Record := [record150, record151, record152, record153, record154, record155, record156, record157, record158, record159, record160, record161, record162, record163, record164]
def rows_150_165_reversed : List Record := [record164, record163, record162, record161, record160, record159, record158, record157, record156, record155, record154, record153, record152, record151, record150]
theorem rows_150_165_segment : reversed165 = rows_150_165_reversed ++ reversed150 := by rfl
theorem rows_150_165_forward : rows_150_165_reversed.reverse = rows_150_165 := by rfl
def rows_165_180 : List Record := [record165, record166, record167, record168, record169, record170, record171, record172, record173, record174, record175, record176, record177, record178, record179]
def rows_165_180_reversed : List Record := [record179, record178, record177, record176, record175, record174, record173, record172, record171, record170, record169, record168, record167, record166, record165]
theorem rows_165_180_segment : reversed180 = rows_165_180_reversed ++ reversed165 := by rfl
theorem rows_165_180_forward : rows_165_180_reversed.reverse = rows_165_180 := by rfl
def rows_150_180 : List Record := rows_150_165 ++ rows_165_180
def rows_150_180_reversed : List Record := rows_165_180_reversed ++ rows_150_165_reversed
theorem rows_150_180_segment : reversed180 = rows_150_180_reversed ++ reversed150 := by
  rw [rows_165_180_segment, rows_150_165_segment]
  unfold rows_150_180_reversed
  simp only [List.append_assoc]
theorem rows_150_180_forward : rows_150_180_reversed.reverse = rows_150_180 := by
  rw [rows_150_180_reversed, List.reverse_append, rows_150_165_forward, rows_165_180_forward]
  rfl
def rows_120_180 : List Record := rows_120_150 ++ rows_150_180
def rows_120_180_reversed : List Record := rows_150_180_reversed ++ rows_120_150_reversed
theorem rows_120_180_segment : reversed180 = rows_120_180_reversed ++ reversed120 := by
  rw [rows_150_180_segment, rows_120_150_segment]
  unfold rows_120_180_reversed
  simp only [List.append_assoc]
theorem rows_120_180_forward : rows_120_180_reversed.reverse = rows_120_180 := by
  rw [rows_120_180_reversed, List.reverse_append, rows_120_150_forward, rows_150_180_forward]
  rfl
def rows_180_195 : List Record := [record180, record181, record182, record183, record184, record185, record186, record187, record188, record189, record190, record191, record192, record193, record194]
def rows_180_195_reversed : List Record := [record194, record193, record192, record191, record190, record189, record188, record187, record186, record185, record184, record183, record182, record181, record180]
theorem rows_180_195_segment : reversed195 = rows_180_195_reversed ++ reversed180 := by rfl
theorem rows_180_195_forward : rows_180_195_reversed.reverse = rows_180_195 := by rfl
def rows_195_210 : List Record := [record195, record196, record197, record198, record199, record200, record201, record202, record203, record204, record205, record206, record207, record208, record209]
def rows_195_210_reversed : List Record := [record209, record208, record207, record206, record205, record204, record203, record202, record201, record200, record199, record198, record197, record196, record195]
theorem rows_195_210_segment : reversed210 = rows_195_210_reversed ++ reversed195 := by rfl
theorem rows_195_210_forward : rows_195_210_reversed.reverse = rows_195_210 := by rfl
def rows_180_210 : List Record := rows_180_195 ++ rows_195_210
def rows_180_210_reversed : List Record := rows_195_210_reversed ++ rows_180_195_reversed
theorem rows_180_210_segment : reversed210 = rows_180_210_reversed ++ reversed180 := by
  rw [rows_195_210_segment, rows_180_195_segment]
  unfold rows_180_210_reversed
  simp only [List.append_assoc]
theorem rows_180_210_forward : rows_180_210_reversed.reverse = rows_180_210 := by
  rw [rows_180_210_reversed, List.reverse_append, rows_180_195_forward, rows_195_210_forward]
  rfl
def rows_210_225 : List Record := [record210, record211, record212, record213, record214, record215, record216, record217, record218, record219, record220, record221, record222, record223, record224]
def rows_210_225_reversed : List Record := [record224, record223, record222, record221, record220, record219, record218, record217, record216, record215, record214, record213, record212, record211, record210]
theorem rows_210_225_segment : reversed225 = rows_210_225_reversed ++ reversed210 := by rfl
theorem rows_210_225_forward : rows_210_225_reversed.reverse = rows_210_225 := by rfl
def rows_225_241 : List Record := [record225, record226, record227, record228, record229, record230, record231, record232, record233, record234, record235, record236, record237, record238, record239, record240]
def rows_225_241_reversed : List Record := [record240, record239, record238, record237, record236, record235, record234, record233, record232, record231, record230, record229, record228, record227, record226, record225]
theorem rows_225_241_segment : reversed241 = rows_225_241_reversed ++ reversed225 := by rfl
theorem rows_225_241_forward : rows_225_241_reversed.reverse = rows_225_241 := by rfl
def rows_210_241 : List Record := rows_210_225 ++ rows_225_241
def rows_210_241_reversed : List Record := rows_225_241_reversed ++ rows_210_225_reversed
theorem rows_210_241_segment : reversed241 = rows_210_241_reversed ++ reversed210 := by
  rw [rows_225_241_segment, rows_210_225_segment]
  unfold rows_210_241_reversed
  simp only [List.append_assoc]
theorem rows_210_241_forward : rows_210_241_reversed.reverse = rows_210_241 := by
  rw [rows_210_241_reversed, List.reverse_append, rows_210_225_forward, rows_225_241_forward]
  rfl
def rows_180_241 : List Record := rows_180_210 ++ rows_210_241
def rows_180_241_reversed : List Record := rows_210_241_reversed ++ rows_180_210_reversed
theorem rows_180_241_segment : reversed241 = rows_180_241_reversed ++ reversed180 := by
  rw [rows_210_241_segment, rows_180_210_segment]
  unfold rows_180_241_reversed
  simp only [List.append_assoc]
theorem rows_180_241_forward : rows_180_241_reversed.reverse = rows_180_241 := by
  rw [rows_180_241_reversed, List.reverse_append, rows_180_210_forward, rows_210_241_forward]
  rfl
def rows_120_241 : List Record := rows_120_180 ++ rows_180_241
def rows_120_241_reversed : List Record := rows_180_241_reversed ++ rows_120_180_reversed
theorem rows_120_241_segment : reversed241 = rows_120_241_reversed ++ reversed120 := by
  rw [rows_180_241_segment, rows_120_180_segment]
  unfold rows_120_241_reversed
  simp only [List.append_assoc]
theorem rows_120_241_forward : rows_120_241_reversed.reverse = rows_120_241 := by
  rw [rows_120_241_reversed, List.reverse_append, rows_120_180_forward, rows_180_241_forward]
  rfl
def rows_0_241 : List Record := rows_0_120 ++ rows_120_241
def rows_0_241_reversed : List Record := rows_120_241_reversed ++ rows_0_120_reversed
theorem rows_0_241_segment : reversed241 = rows_0_241_reversed ++ reversed0 := by
  rw [rows_120_241_segment, rows_0_120_segment]
  unfold rows_0_241_reversed
  simp only [List.append_assoc]
theorem rows_0_241_forward : rows_0_241_reversed.reverse = rows_0_241 := by
  rw [rows_0_241_reversed, List.reverse_append, rows_0_120_forward, rows_120_241_forward]
  rfl
def rows_241_256 : List Record := [record241, record242, record243, record244, record245, record246, record247, record248, record249, record250, record251, record252, record253, record254, record255]
def rows_241_256_reversed : List Record := [record255, record254, record253, record252, record251, record250, record249, record248, record247, record246, record245, record244, record243, record242, record241]
theorem rows_241_256_segment : reversed256 = rows_241_256_reversed ++ reversed241 := by rfl
theorem rows_241_256_forward : rows_241_256_reversed.reverse = rows_241_256 := by rfl
def rows_256_271 : List Record := [record256, record257, record258, record259, record260, record261, record262, record263, record264, record265, record266, record267, record268, record269, record270]
def rows_256_271_reversed : List Record := [record270, record269, record268, record267, record266, record265, record264, record263, record262, record261, record260, record259, record258, record257, record256]
theorem rows_256_271_segment : reversed271 = rows_256_271_reversed ++ reversed256 := by rfl
theorem rows_256_271_forward : rows_256_271_reversed.reverse = rows_256_271 := by rfl
def rows_241_271 : List Record := rows_241_256 ++ rows_256_271
def rows_241_271_reversed : List Record := rows_256_271_reversed ++ rows_241_256_reversed
theorem rows_241_271_segment : reversed271 = rows_241_271_reversed ++ reversed241 := by
  rw [rows_256_271_segment, rows_241_256_segment]
  unfold rows_241_271_reversed
  simp only [List.append_assoc]
theorem rows_241_271_forward : rows_241_271_reversed.reverse = rows_241_271 := by
  rw [rows_241_271_reversed, List.reverse_append, rows_241_256_forward, rows_256_271_forward]
  rfl
def rows_271_286 : List Record := [record271, record272, record273, record274, record275, record276, record277, record278, record279, record280, record281, record282, record283, record284, record285]
def rows_271_286_reversed : List Record := [record285, record284, record283, record282, record281, record280, record279, record278, record277, record276, record275, record274, record273, record272, record271]
theorem rows_271_286_segment : reversed286 = rows_271_286_reversed ++ reversed271 := by rfl
theorem rows_271_286_forward : rows_271_286_reversed.reverse = rows_271_286 := by rfl
def rows_286_301 : List Record := [record286, record287, record288, record289, record290, record291, record292, record293, record294, record295, record296, record297, record298, record299, record300]
def rows_286_301_reversed : List Record := [record300, record299, record298, record297, record296, record295, record294, record293, record292, record291, record290, record289, record288, record287, record286]
theorem rows_286_301_segment : reversed301 = rows_286_301_reversed ++ reversed286 := by rfl
theorem rows_286_301_forward : rows_286_301_reversed.reverse = rows_286_301 := by rfl
def rows_271_301 : List Record := rows_271_286 ++ rows_286_301
def rows_271_301_reversed : List Record := rows_286_301_reversed ++ rows_271_286_reversed
theorem rows_271_301_segment : reversed301 = rows_271_301_reversed ++ reversed271 := by
  rw [rows_286_301_segment, rows_271_286_segment]
  unfold rows_271_301_reversed
  simp only [List.append_assoc]
theorem rows_271_301_forward : rows_271_301_reversed.reverse = rows_271_301 := by
  rw [rows_271_301_reversed, List.reverse_append, rows_271_286_forward, rows_286_301_forward]
  rfl
def rows_241_301 : List Record := rows_241_271 ++ rows_271_301
def rows_241_301_reversed : List Record := rows_271_301_reversed ++ rows_241_271_reversed
theorem rows_241_301_segment : reversed301 = rows_241_301_reversed ++ reversed241 := by
  rw [rows_271_301_segment, rows_241_271_segment]
  unfold rows_241_301_reversed
  simp only [List.append_assoc]
theorem rows_241_301_forward : rows_241_301_reversed.reverse = rows_241_301 := by
  rw [rows_241_301_reversed, List.reverse_append, rows_241_271_forward, rows_271_301_forward]
  rfl
def rows_301_316 : List Record := [record301, record302, record303, record304, record305, record306, record307, record308, record309, record310, record311, record312, record313, record314, record315]
def rows_301_316_reversed : List Record := [record315, record314, record313, record312, record311, record310, record309, record308, record307, record306, record305, record304, record303, record302, record301]
theorem rows_301_316_segment : reversed316 = rows_301_316_reversed ++ reversed301 := by rfl
theorem rows_301_316_forward : rows_301_316_reversed.reverse = rows_301_316 := by rfl
def rows_316_331 : List Record := [record316, record317, record318, record319, record320, record321, record322, record323, record324, record325, record326, record327, record328, record329, record330]
def rows_316_331_reversed : List Record := [record330, record329, record328, record327, record326, record325, record324, record323, record322, record321, record320, record319, record318, record317, record316]
theorem rows_316_331_segment : reversed331 = rows_316_331_reversed ++ reversed316 := by rfl
theorem rows_316_331_forward : rows_316_331_reversed.reverse = rows_316_331 := by rfl
def rows_301_331 : List Record := rows_301_316 ++ rows_316_331
def rows_301_331_reversed : List Record := rows_316_331_reversed ++ rows_301_316_reversed
theorem rows_301_331_segment : reversed331 = rows_301_331_reversed ++ reversed301 := by
  rw [rows_316_331_segment, rows_301_316_segment]
  unfold rows_301_331_reversed
  simp only [List.append_assoc]
theorem rows_301_331_forward : rows_301_331_reversed.reverse = rows_301_331 := by
  rw [rows_301_331_reversed, List.reverse_append, rows_301_316_forward, rows_316_331_forward]
  rfl
def rows_331_346 : List Record := [record331, record332, record333, record334, record335, record336, record337, record338, record339, record340, record341, record342, record343, record344, record345]
def rows_331_346_reversed : List Record := [record345, record344, record343, record342, record341, record340, record339, record338, record337, record336, record335, record334, record333, record332, record331]
theorem rows_331_346_segment : reversed346 = rows_331_346_reversed ++ reversed331 := by rfl
theorem rows_331_346_forward : rows_331_346_reversed.reverse = rows_331_346 := by rfl
def rows_346_361 : List Record := [record346, record347, record348, record349, record350, record351, record352, record353, record354, record355, record356, record357, record358, record359, record360]
def rows_346_361_reversed : List Record := [record360, record359, record358, record357, record356, record355, record354, record353, record352, record351, record350, record349, record348, record347, record346]
theorem rows_346_361_segment : reversed361 = rows_346_361_reversed ++ reversed346 := by rfl
theorem rows_346_361_forward : rows_346_361_reversed.reverse = rows_346_361 := by rfl
def rows_331_361 : List Record := rows_331_346 ++ rows_346_361
def rows_331_361_reversed : List Record := rows_346_361_reversed ++ rows_331_346_reversed
theorem rows_331_361_segment : reversed361 = rows_331_361_reversed ++ reversed331 := by
  rw [rows_346_361_segment, rows_331_346_segment]
  unfold rows_331_361_reversed
  simp only [List.append_assoc]
theorem rows_331_361_forward : rows_331_361_reversed.reverse = rows_331_361 := by
  rw [rows_331_361_reversed, List.reverse_append, rows_331_346_forward, rows_346_361_forward]
  rfl
def rows_301_361 : List Record := rows_301_331 ++ rows_331_361
def rows_301_361_reversed : List Record := rows_331_361_reversed ++ rows_301_331_reversed
theorem rows_301_361_segment : reversed361 = rows_301_361_reversed ++ reversed301 := by
  rw [rows_331_361_segment, rows_301_331_segment]
  unfold rows_301_361_reversed
  simp only [List.append_assoc]
theorem rows_301_361_forward : rows_301_361_reversed.reverse = rows_301_361 := by
  rw [rows_301_361_reversed, List.reverse_append, rows_301_331_forward, rows_331_361_forward]
  rfl
def rows_241_361 : List Record := rows_241_301 ++ rows_301_361
def rows_241_361_reversed : List Record := rows_301_361_reversed ++ rows_241_301_reversed
theorem rows_241_361_segment : reversed361 = rows_241_361_reversed ++ reversed241 := by
  rw [rows_301_361_segment, rows_241_301_segment]
  unfold rows_241_361_reversed
  simp only [List.append_assoc]
theorem rows_241_361_forward : rows_241_361_reversed.reverse = rows_241_361 := by
  rw [rows_241_361_reversed, List.reverse_append, rows_241_301_forward, rows_301_361_forward]
  rfl
def rows_361_376 : List Record := [record361, record362, record363, record364, record365, record366, record367, record368, record369, record370, record371, record372, record373, record374, record375]
def rows_361_376_reversed : List Record := [record375, record374, record373, record372, record371, record370, record369, record368, record367, record366, record365, record364, record363, record362, record361]
theorem rows_361_376_segment : reversed376 = rows_361_376_reversed ++ reversed361 := by rfl
theorem rows_361_376_forward : rows_361_376_reversed.reverse = rows_361_376 := by rfl
def rows_376_391 : List Record := [record376, record377, record378, record379, record380, record381, record382, record383, record384, record385, record386, record387, record388, record389, record390]
def rows_376_391_reversed : List Record := [record390, record389, record388, record387, record386, record385, record384, record383, record382, record381, record380, record379, record378, record377, record376]
theorem rows_376_391_segment : reversed391 = rows_376_391_reversed ++ reversed376 := by rfl
theorem rows_376_391_forward : rows_376_391_reversed.reverse = rows_376_391 := by rfl
def rows_361_391 : List Record := rows_361_376 ++ rows_376_391
def rows_361_391_reversed : List Record := rows_376_391_reversed ++ rows_361_376_reversed
theorem rows_361_391_segment : reversed391 = rows_361_391_reversed ++ reversed361 := by
  rw [rows_376_391_segment, rows_361_376_segment]
  unfold rows_361_391_reversed
  simp only [List.append_assoc]
theorem rows_361_391_forward : rows_361_391_reversed.reverse = rows_361_391 := by
  rw [rows_361_391_reversed, List.reverse_append, rows_361_376_forward, rows_376_391_forward]
  rfl
def rows_391_406 : List Record := [record391, record392, record393, record394, record395, record396, record397, record398, record399, record400, record401, record402, record403, record404, record405]
def rows_391_406_reversed : List Record := [record405, record404, record403, record402, record401, record400, record399, record398, record397, record396, record395, record394, record393, record392, record391]
theorem rows_391_406_segment : reversed406 = rows_391_406_reversed ++ reversed391 := by rfl
theorem rows_391_406_forward : rows_391_406_reversed.reverse = rows_391_406 := by rfl
def rows_406_421 : List Record := [record406, record407, record408, record409, record410, record411, record412, record413, record414, record415, record416, record417, record418, record419, record420]
def rows_406_421_reversed : List Record := [record420, record419, record418, record417, record416, record415, record414, record413, record412, record411, record410, record409, record408, record407, record406]
theorem rows_406_421_segment : reversed421 = rows_406_421_reversed ++ reversed406 := by rfl
theorem rows_406_421_forward : rows_406_421_reversed.reverse = rows_406_421 := by rfl
def rows_391_421 : List Record := rows_391_406 ++ rows_406_421
def rows_391_421_reversed : List Record := rows_406_421_reversed ++ rows_391_406_reversed
theorem rows_391_421_segment : reversed421 = rows_391_421_reversed ++ reversed391 := by
  rw [rows_406_421_segment, rows_391_406_segment]
  unfold rows_391_421_reversed
  simp only [List.append_assoc]
theorem rows_391_421_forward : rows_391_421_reversed.reverse = rows_391_421 := by
  rw [rows_391_421_reversed, List.reverse_append, rows_391_406_forward, rows_406_421_forward]
  rfl
def rows_361_421 : List Record := rows_361_391 ++ rows_391_421
def rows_361_421_reversed : List Record := rows_391_421_reversed ++ rows_361_391_reversed
theorem rows_361_421_segment : reversed421 = rows_361_421_reversed ++ reversed361 := by
  rw [rows_391_421_segment, rows_361_391_segment]
  unfold rows_361_421_reversed
  simp only [List.append_assoc]
theorem rows_361_421_forward : rows_361_421_reversed.reverse = rows_361_421 := by
  rw [rows_361_421_reversed, List.reverse_append, rows_361_391_forward, rows_391_421_forward]
  rfl
def rows_421_436 : List Record := [record421, record422, record423, record424, record425, record426, record427, record428, record429, record430, record431, record432, record433, record434, record435]
def rows_421_436_reversed : List Record := [record435, record434, record433, record432, record431, record430, record429, record428, record427, record426, record425, record424, record423, record422, record421]
theorem rows_421_436_segment : reversed436 = rows_421_436_reversed ++ reversed421 := by rfl
theorem rows_421_436_forward : rows_421_436_reversed.reverse = rows_421_436 := by rfl
def rows_436_451 : List Record := [record436, record437, record438, record439, record440, record441, record442, record443, record444, record445, record446, record447, record448, record449, record450]
def rows_436_451_reversed : List Record := [record450, record449, record448, record447, record446, record445, record444, record443, record442, record441, record440, record439, record438, record437, record436]
theorem rows_436_451_segment : reversed451 = rows_436_451_reversed ++ reversed436 := by rfl
theorem rows_436_451_forward : rows_436_451_reversed.reverse = rows_436_451 := by rfl
def rows_421_451 : List Record := rows_421_436 ++ rows_436_451
def rows_421_451_reversed : List Record := rows_436_451_reversed ++ rows_421_436_reversed
theorem rows_421_451_segment : reversed451 = rows_421_451_reversed ++ reversed421 := by
  rw [rows_436_451_segment, rows_421_436_segment]
  unfold rows_421_451_reversed
  simp only [List.append_assoc]
theorem rows_421_451_forward : rows_421_451_reversed.reverse = rows_421_451 := by
  rw [rows_421_451_reversed, List.reverse_append, rows_421_436_forward, rows_436_451_forward]
  rfl
def rows_451_466 : List Record := [record451, record452, record453, record454, record455, record456, record457, record458, record459, record460, record461, record462, record463, record464, record465]
def rows_451_466_reversed : List Record := [record465, record464, record463, record462, record461, record460, record459, record458, record457, record456, record455, record454, record453, record452, record451]
theorem rows_451_466_segment : reversed466 = rows_451_466_reversed ++ reversed451 := by rfl
theorem rows_451_466_forward : rows_451_466_reversed.reverse = rows_451_466 := by rfl
def rows_466_482 : List Record := [record466, record467, record468, record469, record470, record471, record472, record473, record474, record475, record476, record477, record478, record479, record480, record481]
def rows_466_482_reversed : List Record := [record481, record480, record479, record478, record477, record476, record475, record474, record473, record472, record471, record470, record469, record468, record467, record466]
theorem rows_466_482_segment : reversed482 = rows_466_482_reversed ++ reversed466 := by rfl
theorem rows_466_482_forward : rows_466_482_reversed.reverse = rows_466_482 := by rfl
def rows_451_482 : List Record := rows_451_466 ++ rows_466_482
def rows_451_482_reversed : List Record := rows_466_482_reversed ++ rows_451_466_reversed
theorem rows_451_482_segment : reversed482 = rows_451_482_reversed ++ reversed451 := by
  rw [rows_466_482_segment, rows_451_466_segment]
  unfold rows_451_482_reversed
  simp only [List.append_assoc]
theorem rows_451_482_forward : rows_451_482_reversed.reverse = rows_451_482 := by
  rw [rows_451_482_reversed, List.reverse_append, rows_451_466_forward, rows_466_482_forward]
  rfl
def rows_421_482 : List Record := rows_421_451 ++ rows_451_482
def rows_421_482_reversed : List Record := rows_451_482_reversed ++ rows_421_451_reversed
theorem rows_421_482_segment : reversed482 = rows_421_482_reversed ++ reversed421 := by
  rw [rows_451_482_segment, rows_421_451_segment]
  unfold rows_421_482_reversed
  simp only [List.append_assoc]
theorem rows_421_482_forward : rows_421_482_reversed.reverse = rows_421_482 := by
  rw [rows_421_482_reversed, List.reverse_append, rows_421_451_forward, rows_451_482_forward]
  rfl
def rows_361_482 : List Record := rows_361_421 ++ rows_421_482
def rows_361_482_reversed : List Record := rows_421_482_reversed ++ rows_361_421_reversed
theorem rows_361_482_segment : reversed482 = rows_361_482_reversed ++ reversed361 := by
  rw [rows_421_482_segment, rows_361_421_segment]
  unfold rows_361_482_reversed
  simp only [List.append_assoc]
theorem rows_361_482_forward : rows_361_482_reversed.reverse = rows_361_482 := by
  rw [rows_361_482_reversed, List.reverse_append, rows_361_421_forward, rows_421_482_forward]
  rfl
def rows_241_482 : List Record := rows_241_361 ++ rows_361_482
def rows_241_482_reversed : List Record := rows_361_482_reversed ++ rows_241_361_reversed
theorem rows_241_482_segment : reversed482 = rows_241_482_reversed ++ reversed241 := by
  rw [rows_361_482_segment, rows_241_361_segment]
  unfold rows_241_482_reversed
  simp only [List.append_assoc]
theorem rows_241_482_forward : rows_241_482_reversed.reverse = rows_241_482 := by
  rw [rows_241_482_reversed, List.reverse_append, rows_241_361_forward, rows_361_482_forward]
  rfl
def rows_0_482 : List Record := rows_0_241 ++ rows_241_482
def rows_0_482_reversed : List Record := rows_241_482_reversed ++ rows_0_241_reversed
theorem rows_0_482_segment : reversed482 = rows_0_482_reversed ++ reversed0 := by
  rw [rows_241_482_segment, rows_0_241_segment]
  unfold rows_0_482_reversed
  simp only [List.append_assoc]
theorem rows_0_482_forward : rows_0_482_reversed.reverse = rows_0_482 := by
  rw [rows_0_482_reversed, List.reverse_append, rows_0_241_forward, rows_241_482_forward]
  rfl
theorem complete_records_balanced : actualRecords = rows_0_482 := by
  unfold actualRecords
  rw [rows_0_482_segment]
  simp only [reversed0, List.append_nil]
  exact rows_0_482_forward
theorem rows_0_15_guard : rows_0_15.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_15_30_guard : rows_15_30.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_0_30_guard : rows_0_30.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_0_30, List.filter_append, rows_0_15_guard, rows_15_30_guard]
  rfl
theorem rows_30_45_guard : rows_30_45.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_45_60_guard : rows_45_60.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_30_60_guard : rows_30_60.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_30_60, List.filter_append, rows_30_45_guard, rows_45_60_guard]
  rfl
theorem rows_0_60_guard : rows_0_60.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_0_60, List.filter_append, rows_0_30_guard, rows_30_60_guard]
  rfl
theorem rows_60_75_guard : rows_60_75.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_75_90_guard : rows_75_90.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_60_90_guard : rows_60_90.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_60_90, List.filter_append, rows_60_75_guard, rows_75_90_guard]
  rfl
theorem rows_90_105_guard : rows_90_105.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_105_120_guard : rows_105_120.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_90_120_guard : rows_90_120.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_90_120, List.filter_append, rows_90_105_guard, rows_105_120_guard]
  rfl
theorem rows_60_120_guard : rows_60_120.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_60_120, List.filter_append, rows_60_90_guard, rows_90_120_guard]
  rfl
theorem rows_0_120_guard : rows_0_120.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_0_120, List.filter_append, rows_0_60_guard, rows_60_120_guard]
  rfl
theorem rows_120_135_guard : rows_120_135.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_135_150_guard : rows_135_150.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_120_150_guard : rows_120_150.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_120_150, List.filter_append, rows_120_135_guard, rows_135_150_guard]
  rfl
theorem rows_150_165_guard : rows_150_165.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_165_180_guard : rows_165_180.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_150_180_guard : rows_150_180.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_150_180, List.filter_append, rows_150_165_guard, rows_165_180_guard]
  rfl
theorem rows_120_180_guard : rows_120_180.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_120_180, List.filter_append, rows_120_150_guard, rows_150_180_guard]
  rfl
theorem rows_180_195_guard : rows_180_195.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_195_210_guard : rows_195_210.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_180_210_guard : rows_180_210.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_180_210, List.filter_append, rows_180_195_guard, rows_195_210_guard]
  rfl
theorem rows_210_225_guard : rows_210_225.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_225_241_guard : rows_225_241.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_210_241_guard : rows_210_241.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_210_241, List.filter_append, rows_210_225_guard, rows_225_241_guard]
  rfl
theorem rows_180_241_guard : rows_180_241.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_180_241, List.filter_append, rows_180_210_guard, rows_210_241_guard]
  rfl
theorem rows_120_241_guard : rows_120_241.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_120_241, List.filter_append, rows_120_180_guard, rows_180_241_guard]
  rfl
theorem rows_0_241_guard : rows_0_241.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_0_241, List.filter_append, rows_0_120_guard, rows_120_241_guard]
  rfl
theorem rows_241_256_guard : rows_241_256.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_256_271_guard : rows_256_271.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_241_271_guard : rows_241_271.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_241_271, List.filter_append, rows_241_256_guard, rows_256_271_guard]
  rfl
theorem rows_271_286_guard : rows_271_286.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_286_301_guard : rows_286_301.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_271_301_guard : rows_271_301.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_271_301, List.filter_append, rows_271_286_guard, rows_286_301_guard]
  rfl
theorem rows_241_301_guard : rows_241_301.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_241_301, List.filter_append, rows_241_271_guard, rows_271_301_guard]
  rfl
theorem rows_301_316_guard : rows_301_316.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_316_331_guard : rows_316_331.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_301_331_guard : rows_301_331.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_301_331, List.filter_append, rows_301_316_guard, rows_316_331_guard]
  rfl
theorem rows_331_346_guard : rows_331_346.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_346_361_guard : rows_346_361.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_331_361_guard : rows_331_361.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_331_361, List.filter_append, rows_331_346_guard, rows_346_361_guard]
  rfl
theorem rows_301_361_guard : rows_301_361.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_301_361, List.filter_append, rows_301_331_guard, rows_331_361_guard]
  rfl
theorem rows_241_361_guard : rows_241_361.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_241_361, List.filter_append, rows_241_301_guard, rows_301_361_guard]
  rfl
theorem rows_361_376_guard : rows_361_376.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_376_391_guard : rows_376_391.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_361_391_guard : rows_361_391.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_361_391, List.filter_append, rows_361_376_guard, rows_376_391_guard]
  rfl
theorem rows_391_406_guard : rows_391_406.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_406_421_guard : rows_406_421.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_391_421_guard : rows_391_421.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_391_421, List.filter_append, rows_391_406_guard, rows_406_421_guard]
  rfl
theorem rows_361_421_guard : rows_361_421.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_361_421, List.filter_append, rows_361_391_guard, rows_391_421_guard]
  rfl
theorem rows_421_436_guard : rows_421_436.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_436_451_guard : rows_436_451.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_421_451_guard : rows_421_451.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_421_451, List.filter_append, rows_421_436_guard, rows_436_451_guard]
  rfl
theorem rows_451_466_guard : rows_451_466.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_466_482_guard : rows_466_482.filter (fun record => record.name == "_ASSERT_H_") = [] := by rfl
theorem rows_451_482_guard : rows_451_482.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_451_482, List.filter_append, rows_451_466_guard, rows_466_482_guard]
  rfl
theorem rows_421_482_guard : rows_421_482.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_421_482, List.filter_append, rows_421_451_guard, rows_451_482_guard]
  rfl
theorem rows_361_482_guard : rows_361_482.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_361_482, List.filter_append, rows_361_421_guard, rows_421_482_guard]
  rfl
theorem rows_241_482_guard : rows_241_482.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_241_482, List.filter_append, rows_241_361_guard, rows_361_482_guard]
  rfl
theorem rows_0_482_guard : rows_0_482.filter (fun record => record.name == "_ASSERT_H_") = [] := by
  rw [rows_0_482, List.filter_append, rows_0_241_guard, rows_241_482_guard]
  rfl
theorem captured_guard_lookup : lookup actualRecords "_ASSERT_H_" = some none := by
  unfold lookup
  rw [complete_records_balanced, rows_0_482_guard] <;> rfl
theorem rows_0_15_cpp : rows_0_15.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_15_30_cpp : rows_15_30.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_0_30_cpp : rows_0_30.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_0_30, List.filter_append, rows_0_15_cpp, rows_15_30_cpp]
  rfl
theorem rows_30_45_cpp : rows_30_45.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_45_60_cpp : rows_45_60.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_30_60_cpp : rows_30_60.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_30_60, List.filter_append, rows_30_45_cpp, rows_45_60_cpp]
  rfl
theorem rows_0_60_cpp : rows_0_60.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_0_60, List.filter_append, rows_0_30_cpp, rows_30_60_cpp]
  rfl
theorem rows_60_75_cpp : rows_60_75.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_75_90_cpp : rows_75_90.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_60_90_cpp : rows_60_90.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_60_90, List.filter_append, rows_60_75_cpp, rows_75_90_cpp]
  rfl
theorem rows_90_105_cpp : rows_90_105.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_105_120_cpp : rows_105_120.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_90_120_cpp : rows_90_120.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_90_120, List.filter_append, rows_90_105_cpp, rows_105_120_cpp]
  rfl
theorem rows_60_120_cpp : rows_60_120.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_60_120, List.filter_append, rows_60_90_cpp, rows_90_120_cpp]
  rfl
theorem rows_0_120_cpp : rows_0_120.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_0_120, List.filter_append, rows_0_60_cpp, rows_60_120_cpp]
  rfl
theorem rows_120_135_cpp : rows_120_135.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_135_150_cpp : rows_135_150.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_120_150_cpp : rows_120_150.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_120_150, List.filter_append, rows_120_135_cpp, rows_135_150_cpp]
  rfl
theorem rows_150_165_cpp : rows_150_165.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_165_180_cpp : rows_165_180.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_150_180_cpp : rows_150_180.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_150_180, List.filter_append, rows_150_165_cpp, rows_165_180_cpp]
  rfl
theorem rows_120_180_cpp : rows_120_180.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_120_180, List.filter_append, rows_120_150_cpp, rows_150_180_cpp]
  rfl
theorem rows_180_195_cpp : rows_180_195.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_195_210_cpp : rows_195_210.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_180_210_cpp : rows_180_210.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_180_210, List.filter_append, rows_180_195_cpp, rows_195_210_cpp]
  rfl
theorem rows_210_225_cpp : rows_210_225.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_225_241_cpp : rows_225_241.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_210_241_cpp : rows_210_241.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_210_241, List.filter_append, rows_210_225_cpp, rows_225_241_cpp]
  rfl
theorem rows_180_241_cpp : rows_180_241.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_180_241, List.filter_append, rows_180_210_cpp, rows_210_241_cpp]
  rfl
theorem rows_120_241_cpp : rows_120_241.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_120_241, List.filter_append, rows_120_180_cpp, rows_180_241_cpp]
  rfl
theorem rows_0_241_cpp : rows_0_241.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_0_241, List.filter_append, rows_0_120_cpp, rows_120_241_cpp]
  rfl
theorem rows_241_256_cpp : rows_241_256.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_256_271_cpp : rows_256_271.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_241_271_cpp : rows_241_271.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_241_271, List.filter_append, rows_241_256_cpp, rows_256_271_cpp]
  rfl
theorem rows_271_286_cpp : rows_271_286.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_286_301_cpp : rows_286_301.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_271_301_cpp : rows_271_301.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_271_301, List.filter_append, rows_271_286_cpp, rows_286_301_cpp]
  rfl
theorem rows_241_301_cpp : rows_241_301.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_241_301, List.filter_append, rows_241_271_cpp, rows_271_301_cpp]
  rfl
theorem rows_301_316_cpp : rows_301_316.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_316_331_cpp : rows_316_331.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_301_331_cpp : rows_301_331.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_301_331, List.filter_append, rows_301_316_cpp, rows_316_331_cpp]
  rfl
theorem rows_331_346_cpp : rows_331_346.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_346_361_cpp : rows_346_361.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_331_361_cpp : rows_331_361.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_331_361, List.filter_append, rows_331_346_cpp, rows_346_361_cpp]
  rfl
theorem rows_301_361_cpp : rows_301_361.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_301_361, List.filter_append, rows_301_331_cpp, rows_331_361_cpp]
  rfl
theorem rows_241_361_cpp : rows_241_361.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_241_361, List.filter_append, rows_241_301_cpp, rows_301_361_cpp]
  rfl
theorem rows_361_376_cpp : rows_361_376.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_376_391_cpp : rows_376_391.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_361_391_cpp : rows_361_391.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_361_391, List.filter_append, rows_361_376_cpp, rows_376_391_cpp]
  rfl
theorem rows_391_406_cpp : rows_391_406.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_406_421_cpp : rows_406_421.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_391_421_cpp : rows_391_421.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_391_421, List.filter_append, rows_391_406_cpp, rows_406_421_cpp]
  rfl
theorem rows_361_421_cpp : rows_361_421.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_361_421, List.filter_append, rows_361_391_cpp, rows_391_421_cpp]
  rfl
theorem rows_421_436_cpp : rows_421_436.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_436_451_cpp : rows_436_451.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_421_451_cpp : rows_421_451.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_421_451, List.filter_append, rows_421_436_cpp, rows_436_451_cpp]
  rfl
theorem rows_451_466_cpp : rows_451_466.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_466_482_cpp : rows_466_482.filter (fun record => record.name == "__cplusplus") = [] := by rfl
theorem rows_451_482_cpp : rows_451_482.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_451_482, List.filter_append, rows_451_466_cpp, rows_466_482_cpp]
  rfl
theorem rows_421_482_cpp : rows_421_482.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_421_482, List.filter_append, rows_421_451_cpp, rows_451_482_cpp]
  rfl
theorem rows_361_482_cpp : rows_361_482.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_361_482, List.filter_append, rows_361_421_cpp, rows_421_482_cpp]
  rfl
theorem rows_241_482_cpp : rows_241_482.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_241_482, List.filter_append, rows_241_361_cpp, rows_361_482_cpp]
  rfl
theorem rows_0_482_cpp : rows_0_482.filter (fun record => record.name == "__cplusplus") = [] := by
  rw [rows_0_482, List.filter_append, rows_0_241_cpp, rows_241_482_cpp]
  rfl
theorem captured_cpp_lookup : lookup actualRecords "__cplusplus" = some none := by
  unfold lookup
  rw [complete_records_balanced, rows_0_482_cpp] <;> rfl
theorem rows_0_15_version : rows_0_15.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_15_30_version : rows_15_30.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_0_30_version : rows_0_30.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_0_30, List.filter_append, rows_0_15_version, rows_15_30_version]
  rfl
theorem rows_30_45_version : rows_30_45.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_45_60_version : rows_45_60.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_30_60_version : rows_30_60.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_30_60, List.filter_append, rows_30_45_version, rows_45_60_version]
  rfl
theorem rows_0_60_version : rows_0_60.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_0_60, List.filter_append, rows_0_30_version, rows_30_60_version]
  rfl
theorem rows_60_75_version : rows_60_75.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_75_90_version : rows_75_90.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_60_90_version : rows_60_90.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_60_90, List.filter_append, rows_60_75_version, rows_75_90_version]
  rfl
theorem rows_90_105_version : rows_90_105.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_105_120_version : rows_105_120.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_90_120_version : rows_90_120.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_90_120, List.filter_append, rows_90_105_version, rows_105_120_version]
  rfl
theorem rows_60_120_version : rows_60_120.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_60_120, List.filter_append, rows_60_90_version, rows_90_120_version]
  rfl
theorem rows_0_120_version : rows_0_120.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_0_120, List.filter_append, rows_0_60_version, rows_60_120_version]
  rfl
theorem rows_120_135_version : rows_120_135.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_135_150_version : rows_135_150.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_120_150_version : rows_120_150.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_120_150, List.filter_append, rows_120_135_version, rows_135_150_version]
  rfl
theorem rows_150_165_version : rows_150_165.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_165_180_version : rows_165_180.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_150_180_version : rows_150_180.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_150_180, List.filter_append, rows_150_165_version, rows_165_180_version]
  rfl
theorem rows_120_180_version : rows_120_180.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_120_180, List.filter_append, rows_120_150_version, rows_150_180_version]
  rfl
theorem rows_180_195_version : rows_180_195.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_195_210_version : rows_195_210.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_180_210_version : rows_180_210.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_180_210, List.filter_append, rows_180_195_version, rows_195_210_version]
  rfl
theorem rows_210_225_version : rows_210_225.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_225_241_version : rows_225_241.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_210_241_version : rows_210_241.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_210_241, List.filter_append, rows_210_225_version, rows_225_241_version]
  rfl
theorem rows_180_241_version : rows_180_241.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_180_241, List.filter_append, rows_180_210_version, rows_210_241_version]
  rfl
theorem rows_120_241_version : rows_120_241.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_120_241, List.filter_append, rows_120_180_version, rows_180_241_version]
  rfl
theorem rows_0_241_version : rows_0_241.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_0_241, List.filter_append, rows_0_120_version, rows_120_241_version]
  rfl
theorem rows_241_256_version : rows_241_256.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_256_271_version : rows_256_271.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_241_271_version : rows_241_271.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_241_271, List.filter_append, rows_241_256_version, rows_256_271_version]
  rfl
theorem rows_271_286_version : rows_271_286.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_286_301_version : rows_286_301.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_271_301_version : rows_271_301.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_271_301, List.filter_append, rows_271_286_version, rows_286_301_version]
  rfl
theorem rows_241_301_version : rows_241_301.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_241_301, List.filter_append, rows_241_271_version, rows_271_301_version]
  rfl
theorem rows_301_316_version : rows_301_316.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_316_331_version : rows_316_331.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_301_331_version : rows_301_331.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_301_331, List.filter_append, rows_301_316_version, rows_316_331_version]
  rfl
theorem rows_331_346_version : rows_331_346.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_346_361_version : rows_346_361.filter (fun record => record.name == "__STDC_VERSION__") = [record355] := by rfl
theorem rows_331_361_version : rows_331_361.filter (fun record => record.name == "__STDC_VERSION__") = [record355] := by
  rw [rows_331_361, List.filter_append, rows_331_346_version, rows_346_361_version]
  rfl
theorem rows_301_361_version : rows_301_361.filter (fun record => record.name == "__STDC_VERSION__") = [record355] := by
  rw [rows_301_361, List.filter_append, rows_301_331_version, rows_331_361_version]
  rfl
theorem rows_241_361_version : rows_241_361.filter (fun record => record.name == "__STDC_VERSION__") = [record355] := by
  rw [rows_241_361, List.filter_append, rows_241_301_version, rows_301_361_version]
  rfl
theorem rows_361_376_version : rows_361_376.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_376_391_version : rows_376_391.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_361_391_version : rows_361_391.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_361_391, List.filter_append, rows_361_376_version, rows_376_391_version]
  rfl
theorem rows_391_406_version : rows_391_406.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_406_421_version : rows_406_421.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_391_421_version : rows_391_421.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_391_421, List.filter_append, rows_391_406_version, rows_406_421_version]
  rfl
theorem rows_361_421_version : rows_361_421.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_361_421, List.filter_append, rows_361_391_version, rows_391_421_version]
  rfl
theorem rows_421_436_version : rows_421_436.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_436_451_version : rows_436_451.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_421_451_version : rows_421_451.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_421_451, List.filter_append, rows_421_436_version, rows_436_451_version]
  rfl
theorem rows_451_466_version : rows_451_466.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_466_482_version : rows_466_482.filter (fun record => record.name == "__STDC_VERSION__") = [] := by rfl
theorem rows_451_482_version : rows_451_482.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_451_482, List.filter_append, rows_451_466_version, rows_466_482_version]
  rfl
theorem rows_421_482_version : rows_421_482.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_421_482, List.filter_append, rows_421_451_version, rows_451_482_version]
  rfl
theorem rows_361_482_version : rows_361_482.filter (fun record => record.name == "__STDC_VERSION__") = [] := by
  rw [rows_361_482, List.filter_append, rows_361_421_version, rows_421_482_version]
  rfl
theorem rows_241_482_version : rows_241_482.filter (fun record => record.name == "__STDC_VERSION__") = [record355] := by
  rw [rows_241_482, List.filter_append, rows_241_361_version, rows_361_482_version]
  rfl
theorem rows_0_482_version : rows_0_482.filter (fun record => record.name == "__STDC_VERSION__") = [record355] := by
  rw [rows_0_482, List.filter_append, rows_0_241_version, rows_241_482_version]
  rfl
theorem captured_version_lookup : lookup actualRecords "__STDC_VERSION__" = some (some record355) := by
  unfold lookup
  rw [complete_records_balanced, rows_0_482_version] <;> rfl
theorem rows_0_15_builtin : rows_0_15.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_15_30_builtin : rows_15_30.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_0_30_builtin : rows_0_30.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_0_30, List.filter_append, rows_0_15_builtin, rows_15_30_builtin]
  rfl
theorem rows_30_45_builtin : rows_30_45.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_45_60_builtin : rows_45_60.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_30_60_builtin : rows_30_60.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_30_60, List.filter_append, rows_30_45_builtin, rows_45_60_builtin]
  rfl
theorem rows_0_60_builtin : rows_0_60.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_0_60, List.filter_append, rows_0_30_builtin, rows_30_60_builtin]
  rfl
theorem rows_60_75_builtin : rows_60_75.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_75_90_builtin : rows_75_90.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_60_90_builtin : rows_60_90.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_60_90, List.filter_append, rows_60_75_builtin, rows_75_90_builtin]
  rfl
theorem rows_90_105_builtin : rows_90_105.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_105_120_builtin : rows_105_120.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_90_120_builtin : rows_90_120.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_90_120, List.filter_append, rows_90_105_builtin, rows_105_120_builtin]
  rfl
theorem rows_60_120_builtin : rows_60_120.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_60_120, List.filter_append, rows_60_90_builtin, rows_90_120_builtin]
  rfl
theorem rows_0_120_builtin : rows_0_120.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_0_120, List.filter_append, rows_0_60_builtin, rows_60_120_builtin]
  rfl
theorem rows_120_135_builtin : rows_120_135.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_135_150_builtin : rows_135_150.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_120_150_builtin : rows_120_150.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_120_150, List.filter_append, rows_120_135_builtin, rows_135_150_builtin]
  rfl
theorem rows_150_165_builtin : rows_150_165.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_165_180_builtin : rows_165_180.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_150_180_builtin : rows_150_180.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_150_180, List.filter_append, rows_150_165_builtin, rows_165_180_builtin]
  rfl
theorem rows_120_180_builtin : rows_120_180.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_120_180, List.filter_append, rows_120_150_builtin, rows_150_180_builtin]
  rfl
theorem rows_180_195_builtin : rows_180_195.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_195_210_builtin : rows_195_210.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_180_210_builtin : rows_180_210.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_180_210, List.filter_append, rows_180_195_builtin, rows_195_210_builtin]
  rfl
theorem rows_210_225_builtin : rows_210_225.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_225_241_builtin : rows_225_241.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_210_241_builtin : rows_210_241.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_210_241, List.filter_append, rows_210_225_builtin, rows_225_241_builtin]
  rfl
theorem rows_180_241_builtin : rows_180_241.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_180_241, List.filter_append, rows_180_210_builtin, rows_210_241_builtin]
  rfl
theorem rows_120_241_builtin : rows_120_241.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_120_241, List.filter_append, rows_120_180_builtin, rows_180_241_builtin]
  rfl
theorem rows_0_241_builtin : rows_0_241.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_0_241, List.filter_append, rows_0_120_builtin, rows_120_241_builtin]
  rfl
theorem rows_241_256_builtin : rows_241_256.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_256_271_builtin : rows_256_271.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_241_271_builtin : rows_241_271.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_241_271, List.filter_append, rows_241_256_builtin, rows_256_271_builtin]
  rfl
theorem rows_271_286_builtin : rows_271_286.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_286_301_builtin : rows_286_301.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_271_301_builtin : rows_271_301.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_271_301, List.filter_append, rows_271_286_builtin, rows_286_301_builtin]
  rfl
theorem rows_241_301_builtin : rows_241_301.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_241_301, List.filter_append, rows_241_271_builtin, rows_271_301_builtin]
  rfl
theorem rows_301_316_builtin : rows_301_316.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_316_331_builtin : rows_316_331.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_301_331_builtin : rows_301_331.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_301_331, List.filter_append, rows_301_316_builtin, rows_316_331_builtin]
  rfl
theorem rows_331_346_builtin : rows_331_346.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_346_361_builtin : rows_346_361.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_331_361_builtin : rows_331_361.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_331_361, List.filter_append, rows_331_346_builtin, rows_346_361_builtin]
  rfl
theorem rows_301_361_builtin : rows_301_361.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_301_361, List.filter_append, rows_301_331_builtin, rows_331_361_builtin]
  rfl
theorem rows_241_361_builtin : rows_241_361.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_241_361, List.filter_append, rows_241_301_builtin, rows_301_361_builtin]
  rfl
theorem rows_361_376_builtin : rows_361_376.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_376_391_builtin : rows_376_391.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_361_391_builtin : rows_361_391.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_361_391, List.filter_append, rows_361_376_builtin, rows_376_391_builtin]
  rfl
theorem rows_391_406_builtin : rows_391_406.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_406_421_builtin : rows_406_421.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_391_421_builtin : rows_391_421.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_391_421, List.filter_append, rows_391_406_builtin, rows_406_421_builtin]
  rfl
theorem rows_361_421_builtin : rows_361_421.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_361_421, List.filter_append, rows_361_391_builtin, rows_391_421_builtin]
  rfl
theorem rows_421_436_builtin : rows_421_436.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_436_451_builtin : rows_436_451.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_421_451_builtin : rows_421_451.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_421_451, List.filter_append, rows_421_436_builtin, rows_436_451_builtin]
  rfl
theorem rows_451_466_builtin : rows_451_466.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_466_482_builtin : rows_466_482.filter (fun record => record.name == "__has_include") = [] := by rfl
theorem rows_451_482_builtin : rows_451_482.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_451_482, List.filter_append, rows_451_466_builtin, rows_466_482_builtin]
  rfl
theorem rows_421_482_builtin : rows_421_482.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_421_482, List.filter_append, rows_421_451_builtin, rows_451_482_builtin]
  rfl
theorem rows_361_482_builtin : rows_361_482.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_361_482, List.filter_append, rows_361_421_builtin, rows_421_482_builtin]
  rfl
theorem rows_241_482_builtin : rows_241_482.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_241_482, List.filter_append, rows_241_361_builtin, rows_361_482_builtin]
  rfl
theorem rows_0_482_builtin : rows_0_482.filter (fun record => record.name == "__has_include") = [] := by
  rw [rows_0_482, List.filter_append, rows_0_241_builtin, rows_241_482_builtin]
  rfl
theorem captured_builtin_lookup : lookup actualRecords "__has_include" = some none := by
  unfold lookup
  rw [complete_records_balanced, rows_0_482_builtin] <;> rfl
theorem rows_0_15_static : rows_0_15.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_15_30_static : rows_15_30.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_0_30_static : rows_0_30.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_0_30, List.filter_append, rows_0_15_static, rows_15_30_static]
  rfl
theorem rows_30_45_static : rows_30_45.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_45_60_static : rows_45_60.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_30_60_static : rows_30_60.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_30_60, List.filter_append, rows_30_45_static, rows_45_60_static]
  rfl
theorem rows_0_60_static : rows_0_60.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_0_60, List.filter_append, rows_0_30_static, rows_30_60_static]
  rfl
theorem rows_60_75_static : rows_60_75.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_75_90_static : rows_75_90.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_60_90_static : rows_60_90.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_60_90, List.filter_append, rows_60_75_static, rows_75_90_static]
  rfl
theorem rows_90_105_static : rows_90_105.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_105_120_static : rows_105_120.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_90_120_static : rows_90_120.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_90_120, List.filter_append, rows_90_105_static, rows_105_120_static]
  rfl
theorem rows_60_120_static : rows_60_120.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_60_120, List.filter_append, rows_60_90_static, rows_90_120_static]
  rfl
theorem rows_0_120_static : rows_0_120.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_0_120, List.filter_append, rows_0_60_static, rows_60_120_static]
  rfl
theorem rows_120_135_static : rows_120_135.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_135_150_static : rows_135_150.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_120_150_static : rows_120_150.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_120_150, List.filter_append, rows_120_135_static, rows_135_150_static]
  rfl
theorem rows_150_165_static : rows_150_165.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_165_180_static : rows_165_180.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_150_180_static : rows_150_180.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_150_180, List.filter_append, rows_150_165_static, rows_165_180_static]
  rfl
theorem rows_120_180_static : rows_120_180.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_120_180, List.filter_append, rows_120_150_static, rows_150_180_static]
  rfl
theorem rows_180_195_static : rows_180_195.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_195_210_static : rows_195_210.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_180_210_static : rows_180_210.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_180_210, List.filter_append, rows_180_195_static, rows_195_210_static]
  rfl
theorem rows_210_225_static : rows_210_225.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_225_241_static : rows_225_241.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_210_241_static : rows_210_241.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_210_241, List.filter_append, rows_210_225_static, rows_225_241_static]
  rfl
theorem rows_180_241_static : rows_180_241.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_180_241, List.filter_append, rows_180_210_static, rows_210_241_static]
  rfl
theorem rows_120_241_static : rows_120_241.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_120_241, List.filter_append, rows_120_180_static, rows_180_241_static]
  rfl
theorem rows_0_241_static : rows_0_241.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_0_241, List.filter_append, rows_0_120_static, rows_120_241_static]
  rfl
theorem rows_241_256_static : rows_241_256.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_256_271_static : rows_256_271.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_241_271_static : rows_241_271.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_241_271, List.filter_append, rows_241_256_static, rows_256_271_static]
  rfl
theorem rows_271_286_static : rows_271_286.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_286_301_static : rows_286_301.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_271_301_static : rows_271_301.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_271_301, List.filter_append, rows_271_286_static, rows_286_301_static]
  rfl
theorem rows_241_301_static : rows_241_301.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_241_301, List.filter_append, rows_241_271_static, rows_271_301_static]
  rfl
theorem rows_301_316_static : rows_301_316.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_316_331_static : rows_316_331.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_301_331_static : rows_301_331.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_301_331, List.filter_append, rows_301_316_static, rows_316_331_static]
  rfl
theorem rows_331_346_static : rows_331_346.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_346_361_static : rows_346_361.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_331_361_static : rows_331_361.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_331_361, List.filter_append, rows_331_346_static, rows_346_361_static]
  rfl
theorem rows_301_361_static : rows_301_361.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_301_361, List.filter_append, rows_301_331_static, rows_331_361_static]
  rfl
theorem rows_241_361_static : rows_241_361.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_241_361, List.filter_append, rows_241_301_static, rows_301_361_static]
  rfl
theorem rows_361_376_static : rows_361_376.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_376_391_static : rows_376_391.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_361_391_static : rows_361_391.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_361_391, List.filter_append, rows_361_376_static, rows_376_391_static]
  rfl
theorem rows_391_406_static : rows_391_406.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_406_421_static : rows_406_421.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_391_421_static : rows_391_421.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_391_421, List.filter_append, rows_391_406_static, rows_406_421_static]
  rfl
theorem rows_361_421_static : rows_361_421.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_361_421, List.filter_append, rows_361_391_static, rows_391_421_static]
  rfl
theorem rows_421_436_static : rows_421_436.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_436_451_static : rows_436_451.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_421_451_static : rows_421_451.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_421_451, List.filter_append, rows_421_436_static, rows_436_451_static]
  rfl
theorem rows_451_466_static : rows_451_466.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_466_482_static : rows_466_482.filter (fun record => record.name == "static_assert") = [] := by rfl
theorem rows_451_482_static : rows_451_482.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_451_482, List.filter_append, rows_451_466_static, rows_466_482_static]
  rfl
theorem rows_421_482_static : rows_421_482.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_421_482, List.filter_append, rows_421_451_static, rows_451_482_static]
  rfl
theorem rows_361_482_static : rows_361_482.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_361_482, List.filter_append, rows_361_421_static, rows_421_482_static]
  rfl
theorem rows_241_482_static : rows_241_482.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_241_482, List.filter_append, rows_241_361_static, rows_361_482_static]
  rfl
theorem rows_0_482_static : rows_0_482.filter (fun record => record.name == "static_assert") = [] := by
  rw [rows_0_482, List.filter_append, rows_0_241_static, rows_241_482_static]
  rfl
theorem captured_static_lookup : lookup actualRecords "static_assert" = some none := by
  unfold lookup
  rw [complete_records_balanced, rows_0_482_static] <;> rfl
end C11PredefinedLookupCuts
