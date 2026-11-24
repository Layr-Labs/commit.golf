import CommitGolfCandidate.CapBScans0
namespace CommitGolfCandidate.CapB.Symbol
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
private theorem row9_0 : scan 9 0 384=true := by decide +kernel
private theorem row9_384 : scan 9 384 384=true := by decide +kernel
private theorem row9_768 : scan 9 768 384=true := by decide +kernel
private theorem row9_1152 : scan 9 1152 384=true := by decide +kernel
private theorem row9_1536 : scan 9 1536 384=true := by decide +kernel
private theorem row9_1920 : scan 9 1920 224=true := by decide +kernel
theorem labels9 (i : Nat) (hi : i<2144) : compareAt 9 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row9_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row9_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row9_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row9_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row9_1536 _ (by omega) (by omega)
  exact in_scan _ _ _ row9_1920 _ (by omega) (by omega)

private theorem row10_0 : scan 10 0 384=true := by decide +kernel
private theorem row10_384 : scan 10 384 384=true := by decide +kernel
private theorem row10_768 : scan 10 768 384=true := by decide +kernel
private theorem row10_1152 : scan 10 1152 384=true := by decide +kernel
private theorem row10_1536 : scan 10 1536 384=true := by decide +kernel
private theorem row10_1920 : scan 10 1920 384=true := by decide +kernel
private theorem row10_2304 : scan 10 2304 80=true := by decide +kernel
theorem labels10 (i : Nat) (hi : i<2384) : compareAt 10 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row10_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row10_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row10_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row10_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row10_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row10_1920 _ (by omega) (by omega)
  exact in_scan _ _ _ row10_2304 _ (by omega) (by omega)

private theorem row11_0 : scan 11 0 384=true := by decide +kernel
private theorem row11_384 : scan 11 384 384=true := by decide +kernel
private theorem row11_768 : scan 11 768 384=true := by decide +kernel
private theorem row11_1152 : scan 11 1152 384=true := by decide +kernel
private theorem row11_1536 : scan 11 1536 384=true := by decide +kernel
private theorem row11_1920 : scan 11 1920 384=true := by decide +kernel
private theorem row11_2304 : scan 11 2304 320=true := by decide +kernel
theorem labels11 (i : Nat) (hi : i<2624) : compareAt 11 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row11_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row11_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row11_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row11_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row11_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row11_1920 _ (by omega) (by omega)
  exact in_scan _ _ _ row11_2304 _ (by omega) (by omega)

private theorem row12_0 : scan 12 0 384=true := by decide +kernel
private theorem row12_384 : scan 12 384 384=true := by decide +kernel
private theorem row12_768 : scan 12 768 384=true := by decide +kernel
private theorem row12_1152 : scan 12 1152 384=true := by decide +kernel
private theorem row12_1536 : scan 12 1536 384=true := by decide +kernel
private theorem row12_1920 : scan 12 1920 384=true := by decide +kernel
private theorem row12_2304 : scan 12 2304 384=true := by decide +kernel
private theorem row12_2688 : scan 12 2688 176=true := by decide +kernel
theorem labels12 (i : Nat) (hi : i<2864) : compareAt 12 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row12_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row12_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row12_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row12_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row12_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row12_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row12_2304 _ (by omega) (by omega)
  exact in_scan _ _ _ row12_2688 _ (by omega) (by omega)

private theorem row13_0 : scan 13 0 384=true := by decide +kernel
private theorem row13_384 : scan 13 384 384=true := by decide +kernel
private theorem row13_768 : scan 13 768 384=true := by decide +kernel
private theorem row13_1152 : scan 13 1152 384=true := by decide +kernel
private theorem row13_1536 : scan 13 1536 384=true := by decide +kernel
private theorem row13_1920 : scan 13 1920 384=true := by decide +kernel
private theorem row13_2304 : scan 13 2304 384=true := by decide +kernel
private theorem row13_2688 : scan 13 2688 384=true := by decide +kernel
private theorem row13_3072 : scan 13 3072 32=true := by decide +kernel
theorem labels13 (i : Nat) (hi : i<3104) : compareAt 13 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row13_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row13_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row13_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row13_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row13_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row13_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row13_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row13_2688 _ (by omega) (by omega)
  exact in_scan _ _ _ row13_3072 _ (by omega) (by omega)

private theorem row14_0 : scan 14 0 384=true := by decide +kernel
private theorem row14_384 : scan 14 384 384=true := by decide +kernel
private theorem row14_768 : scan 14 768 384=true := by decide +kernel
private theorem row14_1152 : scan 14 1152 384=true := by decide +kernel
private theorem row14_1536 : scan 14 1536 384=true := by decide +kernel
private theorem row14_1920 : scan 14 1920 384=true := by decide +kernel
private theorem row14_2304 : scan 14 2304 384=true := by decide +kernel
private theorem row14_2688 : scan 14 2688 384=true := by decide +kernel
private theorem row14_3072 : scan 14 3072 272=true := by decide +kernel
theorem labels14 (i : Nat) (hi : i<3344) : compareAt 14 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row14_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row14_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row14_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row14_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row14_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row14_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row14_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row14_2688 _ (by omega) (by omega)
  exact in_scan _ _ _ row14_3072 _ (by omega) (by omega)

private theorem row15_0 : scan 15 0 384=true := by decide +kernel
private theorem row15_384 : scan 15 384 384=true := by decide +kernel
private theorem row15_768 : scan 15 768 384=true := by decide +kernel
private theorem row15_1152 : scan 15 1152 384=true := by decide +kernel
private theorem row15_1536 : scan 15 1536 384=true := by decide +kernel
private theorem row15_1920 : scan 15 1920 384=true := by decide +kernel
private theorem row15_2304 : scan 15 2304 384=true := by decide +kernel
private theorem row15_2688 : scan 15 2688 384=true := by decide +kernel
private theorem row15_3072 : scan 15 3072 384=true := by decide +kernel
private theorem row15_3456 : scan 15 3456 128=true := by decide +kernel
theorem labels15 (i : Nat) (hi : i<3584) : compareAt 15 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row15_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row15_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row15_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row15_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row15_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row15_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row15_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row15_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row15_3072 _ (by omega) (by omega)
  exact in_scan _ _ _ row15_3456 _ (by omega) (by omega)

private theorem row16_0 : scan 16 0 384=true := by decide +kernel
private theorem row16_384 : scan 16 384 384=true := by decide +kernel
private theorem row16_768 : scan 16 768 384=true := by decide +kernel
private theorem row16_1152 : scan 16 1152 384=true := by decide +kernel
private theorem row16_1536 : scan 16 1536 384=true := by decide +kernel
private theorem row16_1920 : scan 16 1920 384=true := by decide +kernel
private theorem row16_2304 : scan 16 2304 384=true := by decide +kernel
private theorem row16_2688 : scan 16 2688 384=true := by decide +kernel
private theorem row16_3072 : scan 16 3072 384=true := by decide +kernel
private theorem row16_3456 : scan 16 3456 352=true := by decide +kernel
theorem labels16 (i : Nat) (hi : i<3808) : compareAt 16 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row16_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row16_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row16_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row16_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row16_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row16_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row16_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row16_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row16_3072 _ (by omega) (by omega)
  exact in_scan _ _ _ row16_3456 _ (by omega) (by omega)

end CommitGolfCandidate.CapB.Symbol
