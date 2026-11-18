-- Copyright 2026 Andrew Yates | Apache-2.0
import C11DirectiveLines
import C11AssertHeaderCuts
namespace C11AssertDirectiveCuts
open C11DirectiveLines C11AssertHeaderCuts
def state1 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut0 : C11DirectiveLines.feed (some initial) assertHeader_chunk0 = state1 := by rfl
def state2 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut1 : C11DirectiveLines.feed state1 assertHeader_chunk1 = state2 := by rfl
def state3 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut2 : C11DirectiveLines.feed state2 assertHeader_chunk2 = state3 := by rfl
def state4 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut3 : C11DirectiveLines.feed state3 assertHeader_chunk3 = state4 := by rfl
def state5 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut4 : C11DirectiveLines.feed state4 assertHeader_chunk4 = state5 := by rfl
def state6 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut5 : C11DirectiveLines.feed state5 assertHeader_chunk5 = state6 := by rfl
def state7 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut6 : C11DirectiveLines.feed state6 assertHeader_chunk6 = state7 := by rfl
def state8 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut7 : C11DirectiveLines.feed state7 assertHeader_chunk7 = state8 := by rfl
def state9 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut8 : C11DirectiveLines.feed state8 assertHeader_chunk8 = state9 := by rfl
def state10 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut9 : C11DirectiveLines.feed state9 assertHeader_chunk9 = state10 := by rfl
def state11 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut10 : C11DirectiveLines.feed state10 assertHeader_chunk10 = state11 := by rfl
def state12 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut11 : C11DirectiveLines.feed state11 assertHeader_chunk11 = state12 := by rfl
def state13 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut12 : C11DirectiveLines.feed state12 assertHeader_chunk12 = state13 := by rfl
def state14 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut13 : C11DirectiveLines.feed state13 assertHeader_chunk13 = state14 := by rfl
def state15 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut14 : C11DirectiveLines.feed state14 assertHeader_chunk14 = state15 := by rfl
def state16 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut15 : C11DirectiveLines.feed state15 assertHeader_chunk15 = state16 := by rfl
def state17 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut16 : C11DirectiveLines.feed state16 assertHeader_chunk16 = state17 := by rfl
def state18 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut17 : C11DirectiveLines.feed state17 assertHeader_chunk17 = state18 := by rfl
def state19 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut18 : C11DirectiveLines.feed state18 assertHeader_chunk18 = state19 := by rfl
def state20 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut19 : C11DirectiveLines.feed state19 assertHeader_chunk19 = state20 := by rfl
def state21 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut20 : C11DirectiveLines.feed state20 assertHeader_chunk20 = state21 := by rfl
def state22 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut21 : C11DirectiveLines.feed state21 assertHeader_chunk21 = state22 := by rfl
def state23 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut22 : C11DirectiveLines.feed state22 assertHeader_chunk22 = state23 := by rfl
def state24 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut23 : C11DirectiveLines.feed state23 assertHeader_chunk23 = state24 := by rfl
def state25 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut24 : C11DirectiveLines.feed state24 assertHeader_chunk24 = state25 := by rfl
def state26 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut25 : C11DirectiveLines.feed state25 assertHeader_chunk25 = state26 := by rfl
def state27 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut26 : C11DirectiveLines.feed state26 assertHeader_chunk26 = state27 := by rfl
def state28 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut27 : C11DirectiveLines.feed state27 assertHeader_chunk27 = state28 := by rfl
def state29 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut28 : C11DirectiveLines.feed state28 assertHeader_chunk28 = state29 := by rfl
def state30 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut29 : C11DirectiveLines.feed state29 assertHeader_chunk29 = state30 := by rfl
def state31 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut30 : C11DirectiveLines.feed state30 assertHeader_chunk30 = state31 := by rfl
def state32 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut31 : C11DirectiveLines.feed state31 assertHeader_chunk31 = state32 := by rfl
def state33 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut32 : C11DirectiveLines.feed state32 assertHeader_chunk32 = state33 := by rfl
def state34 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut33 : C11DirectiveLines.feed state33 assertHeader_chunk33 = state34 := by rfl
def state35 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut34 : C11DirectiveLines.feed state34 assertHeader_chunk34 = state35 := by rfl
def state36 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut35 : C11DirectiveLines.feed state35 assertHeader_chunk35 = state36 := by rfl
def state37 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut36 : C11DirectiveLines.feed state36 assertHeader_chunk36 = state37 := by rfl
def state38 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut37 : C11DirectiveLines.feed state37 assertHeader_chunk37 = state38 := by rfl
def state39 : Option C11DirectiveLines.State := some { mode := .star, beginning := true, directive := false }
theorem cut38 : C11DirectiveLines.feed state38 assertHeader_chunk38 = state39 := by rfl
def state40 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut39 : C11DirectiveLines.feed state39 assertHeader_chunk39 = state40 := by rfl
def state41 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut40 : C11DirectiveLines.feed state40 assertHeader_chunk40 = state41 := by rfl
def state42 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut41 : C11DirectiveLines.feed state41 assertHeader_chunk41 = state42 := by rfl
def state43 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut42 : C11DirectiveLines.feed state42 assertHeader_chunk42 = state43 := by rfl
def state44 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut43 : C11DirectiveLines.feed state43 assertHeader_chunk43 = state44 := by rfl
def state45 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut44 : C11DirectiveLines.feed state44 assertHeader_chunk44 = state45 := by rfl
def state46 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut45 : C11DirectiveLines.feed state45 assertHeader_chunk45 = state46 := by rfl
def state47 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut46 : C11DirectiveLines.feed state46 assertHeader_chunk46 = state47 := by rfl
def state48 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut47 : C11DirectiveLines.feed state47 assertHeader_chunk47 = state48 := by rfl
def state49 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut48 : C11DirectiveLines.feed state48 assertHeader_chunk48 = state49 := by rfl
def state50 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut49 : C11DirectiveLines.feed state49 assertHeader_chunk49 = state50 := by rfl
def state51 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut50 : C11DirectiveLines.feed state50 assertHeader_chunk50 = state51 := by rfl
def state52 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut51 : C11DirectiveLines.feed state51 assertHeader_chunk51 = state52 := by rfl
def state53 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut52 : C11DirectiveLines.feed state52 assertHeader_chunk52 = state53 := by rfl
def state54 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut53 : C11DirectiveLines.feed state53 assertHeader_chunk53 = state54 := by rfl
def state55 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut54 : C11DirectiveLines.feed state54 assertHeader_chunk54 = state55 := by rfl
def state56 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut55 : C11DirectiveLines.feed state55 assertHeader_chunk55 = state56 := by rfl
def state57 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut56 : C11DirectiveLines.feed state56 assertHeader_chunk56 = state57 := by rfl
def state58 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut57 : C11DirectiveLines.feed state57 assertHeader_chunk57 = state58 := by rfl
def state59 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut58 : C11DirectiveLines.feed state58 assertHeader_chunk58 = state59 := by rfl
def state60 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut59 : C11DirectiveLines.feed state59 assertHeader_chunk59 = state60 := by rfl
def state61 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut60 : C11DirectiveLines.feed state60 assertHeader_chunk60 = state61 := by rfl
def state62 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut61 : C11DirectiveLines.feed state61 assertHeader_chunk61 = state62 := by rfl
def state63 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut62 : C11DirectiveLines.feed state62 assertHeader_chunk62 = state63 := by rfl
def state64 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut63 : C11DirectiveLines.feed state63 assertHeader_chunk63 = state64 := by rfl
def state65 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut64 : C11DirectiveLines.feed state64 assertHeader_chunk64 = state65 := by rfl
def state66 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut65 : C11DirectiveLines.feed state65 assertHeader_chunk65 = state66 := by rfl
def state67 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut66 : C11DirectiveLines.feed state66 assertHeader_chunk66 = state67 := by rfl
def state68 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut67 : C11DirectiveLines.feed state67 assertHeader_chunk67 = state68 := by rfl
def state69 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut68 : C11DirectiveLines.feed state68 assertHeader_chunk68 = state69 := by rfl
def state70 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut69 : C11DirectiveLines.feed state69 assertHeader_chunk69 = state70 := by rfl
def state71 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut70 : C11DirectiveLines.feed state70 assertHeader_chunk70 = state71 := by rfl
def state72 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut71 : C11DirectiveLines.feed state71 assertHeader_chunk71 = state72 := by rfl
def state73 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut72 : C11DirectiveLines.feed state72 assertHeader_chunk72 = state73 := by rfl
def state74 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut73 : C11DirectiveLines.feed state73 assertHeader_chunk73 = state74 := by rfl
def state75 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut74 : C11DirectiveLines.feed state74 assertHeader_chunk74 = state75 := by rfl
def state76 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut75 : C11DirectiveLines.feed state75 assertHeader_chunk75 = state76 := by rfl
def state77 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut76 : C11DirectiveLines.feed state76 assertHeader_chunk76 = state77 := by rfl
def state78 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut77 : C11DirectiveLines.feed state77 assertHeader_chunk77 = state78 := by rfl
def state79 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut78 : C11DirectiveLines.feed state78 assertHeader_chunk78 = state79 := by rfl
def state80 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut79 : C11DirectiveLines.feed state79 assertHeader_chunk79 = state80 := by rfl
def state81 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut80 : C11DirectiveLines.feed state80 assertHeader_chunk80 = state81 := by rfl
def state82 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut81 : C11DirectiveLines.feed state81 assertHeader_chunk81 = state82 := by rfl
def state83 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut82 : C11DirectiveLines.feed state82 assertHeader_chunk82 = state83 := by rfl
def state84 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut83 : C11DirectiveLines.feed state83 assertHeader_chunk83 = state84 := by rfl
def state85 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut84 : C11DirectiveLines.feed state84 assertHeader_chunk84 = state85 := by rfl
def state86 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut85 : C11DirectiveLines.feed state85 assertHeader_chunk85 = state86 := by rfl
def state87 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut86 : C11DirectiveLines.feed state86 assertHeader_chunk86 = state87 := by rfl
def state88 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut87 : C11DirectiveLines.feed state87 assertHeader_chunk87 = state88 := by rfl
def state89 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut88 : C11DirectiveLines.feed state88 assertHeader_chunk88 = state89 := by rfl
def state90 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut89 : C11DirectiveLines.feed state89 assertHeader_chunk89 = state90 := by rfl
def state91 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut90 : C11DirectiveLines.feed state90 assertHeader_chunk90 = state91 := by rfl
def state92 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut91 : C11DirectiveLines.feed state91 assertHeader_chunk91 = state92 := by rfl
def state93 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut92 : C11DirectiveLines.feed state92 assertHeader_chunk92 = state93 := by rfl
def state94 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut93 : C11DirectiveLines.feed state93 assertHeader_chunk93 = state94 := by rfl
def state95 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut94 : C11DirectiveLines.feed state94 assertHeader_chunk94 = state95 := by rfl
def state96 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut95 : C11DirectiveLines.feed state95 assertHeader_chunk95 = state96 := by rfl
def state97 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut96 : C11DirectiveLines.feed state96 assertHeader_chunk96 = state97 := by rfl
def state98 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut97 : C11DirectiveLines.feed state97 assertHeader_chunk97 = state98 := by rfl
def state99 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut98 : C11DirectiveLines.feed state98 assertHeader_chunk98 = state99 := by rfl
def state100 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut99 : C11DirectiveLines.feed state99 assertHeader_chunk99 = state100 := by rfl
def state101 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut100 : C11DirectiveLines.feed state100 assertHeader_chunk100 = state101 := by rfl
def state102 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut101 : C11DirectiveLines.feed state101 assertHeader_chunk101 = state102 := by rfl
def state103 : Option C11DirectiveLines.State := some { mode := .star, beginning := true, directive := false }
theorem cut102 : C11DirectiveLines.feed state102 assertHeader_chunk102 = state103 := by rfl
def state104 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut103 : C11DirectiveLines.feed state103 assertHeader_chunk103 = state104 := by rfl
def state105 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut104 : C11DirectiveLines.feed state104 assertHeader_chunk104 = state105 := by rfl
def state106 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut105 : C11DirectiveLines.feed state105 assertHeader_chunk105 = state106 := by rfl
def state107 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut106 : C11DirectiveLines.feed state106 assertHeader_chunk106 = state107 := by rfl
def state108 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut107 : C11DirectiveLines.feed state107 assertHeader_chunk107 = state108 := by rfl
def state109 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut108 : C11DirectiveLines.feed state108 assertHeader_chunk108 = state109 := by rfl
def state110 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut109 : C11DirectiveLines.feed state109 assertHeader_chunk109 = state110 := by rfl
def state111 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut110 : C11DirectiveLines.feed state110 assertHeader_chunk110 = state111 := by rfl
def state112 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut111 : C11DirectiveLines.feed state111 assertHeader_chunk111 = state112 := by rfl
def state113 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut112 : C11DirectiveLines.feed state112 assertHeader_chunk112 = state113 := by rfl
def state114 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut113 : C11DirectiveLines.feed state113 assertHeader_chunk113 = state114 := by rfl
def state115 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut114 : C11DirectiveLines.feed state114 assertHeader_chunk114 = state115 := by rfl
def state116 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut115 : C11DirectiveLines.feed state115 assertHeader_chunk115 = state116 := by rfl
def state117 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut116 : C11DirectiveLines.feed state116 assertHeader_chunk116 = state117 := by rfl
def state118 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut117 : C11DirectiveLines.feed state117 assertHeader_chunk117 = state118 := by rfl
def state119 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut118 : C11DirectiveLines.feed state118 assertHeader_chunk118 = state119 := by rfl
def state120 : Option C11DirectiveLines.State := some { mode := .block, beginning := true, directive := false }
theorem cut119 : C11DirectiveLines.feed state119 assertHeader_chunk119 = state120 := by rfl
def state121 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut120 : C11DirectiveLines.feed state120 assertHeader_chunk120 = state121 := by rfl
def state122 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut121 : C11DirectiveLines.feed state121 assertHeader_chunk121 = state122 := by rfl
def state123 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut122 : C11DirectiveLines.feed state122 assertHeader_chunk122 = state123 := by rfl
def state124 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut123 : C11DirectiveLines.feed state123 assertHeader_chunk123 = state124 := by rfl
def state125 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut124 : C11DirectiveLines.feed state124 assertHeader_chunk124 = state125 := by rfl
def state126 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut125 : C11DirectiveLines.feed state125 assertHeader_chunk125 = state126 := by rfl
def state127 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut126 : C11DirectiveLines.feed state126 assertHeader_chunk126 = state127 := by rfl
def state128 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut127 : C11DirectiveLines.feed state127 assertHeader_chunk127 = state128 := by rfl
def state129 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut128 : C11DirectiveLines.feed state128 assertHeader_chunk128 = state129 := by rfl
def state130 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut129 : C11DirectiveLines.feed state129 assertHeader_chunk129 = state130 := by rfl
def state131 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut130 : C11DirectiveLines.feed state130 assertHeader_chunk130 = state131 := by rfl
def state132 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut131 : C11DirectiveLines.feed state131 assertHeader_chunk131 = state132 := by rfl
def state133 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut132 : C11DirectiveLines.feed state132 assertHeader_chunk132 = state133 := by rfl
def state134 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut133 : C11DirectiveLines.feed state133 assertHeader_chunk133 = state134 := by rfl
def state135 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut134 : C11DirectiveLines.feed state134 assertHeader_chunk134 = state135 := by rfl
def state136 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut135 : C11DirectiveLines.feed state135 assertHeader_chunk135 = state136 := by rfl
def state137 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut136 : C11DirectiveLines.feed state136 assertHeader_chunk136 = state137 := by rfl
def state138 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut137 : C11DirectiveLines.feed state137 assertHeader_chunk137 = state138 := by rfl
def state139 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut138 : C11DirectiveLines.feed state138 assertHeader_chunk138 = state139 := by rfl
def state140 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut139 : C11DirectiveLines.feed state139 assertHeader_chunk139 = state140 := by rfl
def state141 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut140 : C11DirectiveLines.feed state140 assertHeader_chunk140 = state141 := by rfl
def state142 : Option C11DirectiveLines.State := some { mode := .block, beginning := false, directive := true }
theorem cut141 : C11DirectiveLines.feed state141 assertHeader_chunk141 = state142 := by rfl
def state143 : Option C11DirectiveLines.State := some { mode := .block, beginning := false, directive := true }
theorem cut142 : C11DirectiveLines.feed state142 assertHeader_chunk142 = state143 := by rfl
def state144 : Option C11DirectiveLines.State := some { mode := .star, beginning := false, directive := true }
theorem cut143 : C11DirectiveLines.feed state143 assertHeader_chunk143 = state144 := by rfl
def state145 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut144 : C11DirectiveLines.feed state144 assertHeader_chunk144 = state145 := by rfl
def state146 : Option C11DirectiveLines.State := some { mode := .block, beginning := false, directive := true }
theorem cut145 : C11DirectiveLines.feed state145 assertHeader_chunk145 = state146 := by rfl
def state147 : Option C11DirectiveLines.State := some { mode := .block, beginning := false, directive := true }
theorem cut146 : C11DirectiveLines.feed state146 assertHeader_chunk146 = state147 := by rfl
def state148 : Option C11DirectiveLines.State := some { mode := .normal, beginning := false, directive := true }
theorem cut147 : C11DirectiveLines.feed state147 assertHeader_chunk147 = state148 := by rfl
def state149 : Option C11DirectiveLines.State := some { mode := .block, beginning := false, directive := true }
theorem cut148 : C11DirectiveLines.feed state148 assertHeader_chunk148 = state149 := by rfl
def state150 : Option C11DirectiveLines.State := some { mode := .block, beginning := false, directive := true }
theorem cut149 : C11DirectiveLines.feed state149 assertHeader_chunk149 = state150 := by rfl
def state151 : Option C11DirectiveLines.State := some { mode := .normal, beginning := true, directive := false }
theorem cut150 : C11DirectiveLines.feed state150 assertHeader_chunk150 = state151 := by rfl
theorem complete_characters_supported : supportedCharacters assertHeader_chunks.flatten = true := by
  rw [← C11DirectiveLines.chunks_exact]
  simp only [supportedChunks, assertHeader_chunks, List.foldl_cons, List.foldl_nil]
  rw [cut0, cut1, cut2, cut3, cut4, cut5, cut6, cut7, cut8, cut9, cut10, cut11, cut12, cut13, cut14, cut15, cut16, cut17, cut18, cut19, cut20, cut21, cut22, cut23, cut24, cut25, cut26, cut27, cut28, cut29, cut30, cut31, cut32, cut33, cut34, cut35, cut36, cut37, cut38, cut39, cut40, cut41, cut42, cut43, cut44, cut45, cut46, cut47, cut48, cut49, cut50, cut51, cut52, cut53, cut54, cut55, cut56, cut57, cut58, cut59, cut60, cut61, cut62, cut63, cut64, cut65, cut66, cut67, cut68, cut69, cut70, cut71, cut72, cut73, cut74, cut75, cut76, cut77, cut78, cut79, cut80, cut81, cut82, cut83, cut84, cut85, cut86, cut87, cut88, cut89, cut90, cut91, cut92, cut93, cut94, cut95, cut96, cut97, cut98, cut99, cut100, cut101, cut102, cut103, cut104, cut105, cut106, cut107, cut108, cut109, cut110, cut111, cut112, cut113, cut114, cut115, cut116, cut117, cut118, cut119, cut120, cut121, cut122, cut123, cut124, cut125, cut126, cut127, cut128, cut129, cut130, cut131, cut132, cut133, cut134, cut135, cut136, cut137, cut138, cut139, cut140, cut141, cut142, cut143, cut144, cut145, cut146, cut147, cut148, cut149, cut150]
  rfl
theorem complete_source_supported : supported C11AssertHeaderData.assertHeader_0 = true := by
  unfold supported
  rw [← assertHeader_string_exact, assertHeader_node_0_151_characters, assertHeader_flatten_exact]
  exact complete_characters_supported
end C11AssertDirectiveCuts
