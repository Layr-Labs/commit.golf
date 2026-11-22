import CommitGolfCandidate.CapBLabels
namespace CommitGolfCandidate.CapB.Symbol
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
private theorem row1_0 : scan 1 0 240=true := by decide +kernel
theorem labels1 (i : Nat) (hi : i<240) : compareAt 1 i=true := by
  exact in_scan _ _ _ row1_0 _ (by omega) (by omega)

private theorem row2_0 : scan 2 0 384=true := by decide +kernel
private theorem row2_384 : scan 2 384 96=true := by decide +kernel
theorem labels2 (i : Nat) (hi : i<480) : compareAt 2 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row2_0 _ (by omega) (by omega)
  exact in_scan _ _ _ row2_384 _ (by omega) (by omega)

private theorem row3_0 : scan 3 0 384=true := by decide +kernel
private theorem row3_384 : scan 3 384 336=true := by decide +kernel
theorem labels3 (i : Nat) (hi : i<720) : compareAt 3 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row3_0 _ (by omega) (by omega)
  exact in_scan _ _ _ row3_384 _ (by omega) (by omega)

private theorem row4_0 : scan 4 0 384=true := by decide +kernel
private theorem row4_384 : scan 4 384 384=true := by decide +kernel
private theorem row4_768 : scan 4 768 192=true := by decide +kernel
theorem labels4 (i : Nat) (hi : i<960) : compareAt 4 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row4_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row4_384 _ (by omega) (by omega)
  exact in_scan _ _ _ row4_768 _ (by omega) (by omega)

private theorem row5_0 : scan 5 0 384=true := by decide +kernel
private theorem row5_384 : scan 5 384 384=true := by decide +kernel
private theorem row5_768 : scan 5 768 384=true := by decide +kernel
private theorem row5_1152 : scan 5 1152 48=true := by decide +kernel
theorem labels5 (i : Nat) (hi : i<1200) : compareAt 5 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row5_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row5_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row5_768 _ (by omega) (by omega)
  exact in_scan _ _ _ row5_1152 _ (by omega) (by omega)

private theorem row6_0 : scan 6 0 384=true := by decide +kernel
private theorem row6_384 : scan 6 384 384=true := by decide +kernel
private theorem row6_768 : scan 6 768 384=true := by decide +kernel
private theorem row6_1152 : scan 6 1152 288=true := by decide +kernel
theorem labels6 (i : Nat) (hi : i<1440) : compareAt 6 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row6_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row6_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row6_768 _ (by omega) (by omega)
  exact in_scan _ _ _ row6_1152 _ (by omega) (by omega)

private theorem row7_0 : scan 7 0 384=true := by decide +kernel
private theorem row7_384 : scan 7 384 384=true := by decide +kernel
private theorem row7_768 : scan 7 768 384=true := by decide +kernel
private theorem row7_1152 : scan 7 1152 384=true := by decide +kernel
private theorem row7_1536 : scan 7 1536 144=true := by decide +kernel
theorem labels7 (i : Nat) (hi : i<1680) : compareAt 7 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row7_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row7_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row7_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row7_1152 _ (by omega) (by omega)
  exact in_scan _ _ _ row7_1536 _ (by omega) (by omega)

private theorem row8_0 : scan 8 0 384=true := by decide +kernel
private theorem row8_384 : scan 8 384 384=true := by decide +kernel
private theorem row8_768 : scan 8 768 384=true := by decide +kernel
private theorem row8_1152 : scan 8 1152 384=true := by decide +kernel
private theorem row8_1536 : scan 8 1536 368=true := by decide +kernel
theorem labels8 (i : Nat) (hi : i<1904) : compareAt 8 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row8_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row8_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row8_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row8_1152 _ (by omega) (by omega)
  exact in_scan _ _ _ row8_1536 _ (by omega) (by omega)

end CommitGolfCandidate.CapB.Symbol
