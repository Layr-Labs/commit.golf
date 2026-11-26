import CommitGolfCandidate.S4FieldPC
namespace CommitGolfCandidate.S4.Open
set_option maxRecDepth 6500
set_option maxHeartbeats 4000000
private theorem w0 : fieldValid true 3 0 := by decide
private theorem w1 : fieldValid true 3 1 := by decide
private theorem w2 : fieldValid true 3 2 := by decide
private theorem w3 : fieldValid true 3 3 := by decide
private theorem w4 : fieldValid true 3 4 := by decide
private theorem w5 : fieldValid true 3 5 := by decide
private theorem w6 : fieldValid true 3 6 := by decide
private theorem w7 : fieldValid true 3 7 := by decide
private theorem w8 : fieldValid true 3 8 := by decide
private theorem w9 : fieldValid true 3 9 := by decide
private theorem w10 : fieldValid true 3 10 := by decide
private theorem w11 : fieldValid true 3 11 := by decide
private theorem w12 : fieldValid true 3 12 := by decide
private theorem w13 : fieldValid true 3 13 := by decide
private theorem w14 : fieldValid true 3 14 := by decide
private theorem w15 : fieldValid true 3 15 := by decide
private theorem w16 : fieldValid true 3 16 := by decide
theorem allWords3 (q : Fin 17) : fieldValid true 3 q.val := by
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
end CommitGolfCandidate.S4.Open
