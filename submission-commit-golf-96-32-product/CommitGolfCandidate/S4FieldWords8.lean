import CommitGolfCandidate.S4FieldPC
set_option Elab.async false

namespace CommitGolfCandidate.S4.Open
set_option maxRecDepth 6500
set_option maxHeartbeats 4000000
private theorem w0 : fieldValid false 0 0 := by decide
private theorem w1 : fieldValid false 0 1 := by decide
private theorem w2 : fieldValid false 0 2 := by decide
private theorem w3 : fieldValid false 0 3 := by decide
private theorem w4 : fieldValid false 0 4 := by decide
private theorem w5 : fieldValid false 0 5 := by decide
private theorem w6 : fieldValid false 0 6 := by decide
private theorem w7 : fieldValid false 0 7 := by decide
private theorem w8 : fieldValid false 0 8 := by decide
private theorem w9 : fieldValid false 0 9 := by decide
private theorem w10 : fieldValid false 0 10 := by decide
private theorem w11 : fieldValid false 0 11 := by decide
private theorem w12 : fieldValid false 0 12 := by decide
private theorem w13 : fieldValid false 0 13 := by decide
private theorem w14 : fieldValid false 0 14 := by decide
private theorem w15 : fieldValid false 0 15 := by decide
private theorem w16 : fieldValid false 0 16 := by decide
private theorem w17 : fieldValid false 0 17 := by decide
private theorem w18 : fieldValid false 0 18 := by decide
private theorem w19 : fieldValid false 0 19 := by decide
private theorem w20 : fieldValid false 0 20 := by decide
private theorem w21 : fieldValid false 0 21 := by decide
private theorem w22 : fieldValid false 0 22 := by decide
private theorem w23 : fieldValid false 0 23 := by decide
private theorem w24 : fieldValid false 0 24 := by decide
private theorem w25 : fieldValid false 0 25 := by decide
theorem allWords8 (q : Fin 26) : fieldValid false 0 q.val := by
  rcases q with ⟨q,hq⟩
  interval_cases q
  · exact w0
  · exact w1
  · exact w2
  · exact w3
  · exact w4
  · exact w5
  · exact w6
  · exact w7
  · exact w8
  · exact w9
  · exact w10
  · exact w11
  · exact w12
  · exact w13
  · exact w14
  · exact w15
  · exact w16
  · exact w17
  · exact w18
  · exact w19
  · exact w20
  · exact w21
  · exact w22
  · exact w23
  · exact w24
  · exact w25
end CommitGolfCandidate.S4.Open
