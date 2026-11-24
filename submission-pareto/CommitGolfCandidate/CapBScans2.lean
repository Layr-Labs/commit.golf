import CommitGolfCandidate.CapBScans1
namespace CommitGolfCandidate.CapB.Symbol
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
private theorem row17_0 : scan 17 0 384=true := by decide +kernel
private theorem row17_384 : scan 17 384 384=true := by decide +kernel
private theorem row17_768 : scan 17 768 384=true := by decide +kernel
private theorem row17_1152 : scan 17 1152 384=true := by decide +kernel
private theorem row17_1536 : scan 17 1536 384=true := by decide +kernel
private theorem row17_1920 : scan 17 1920 384=true := by decide +kernel
private theorem row17_2304 : scan 17 2304 384=true := by decide +kernel
private theorem row17_2688 : scan 17 2688 384=true := by decide +kernel
private theorem row17_3072 : scan 17 3072 384=true := by decide +kernel
private theorem row17_3456 : scan 17 3456 384=true := by decide +kernel
private theorem row17_3840 : scan 17 3840 208=true := by decide +kernel
theorem labels17 (i : Nat) (hi : i<4048) : compareAt 17 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row17_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row17_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row17_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row17_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row17_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row17_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row17_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row17_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row17_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row17_3456 _ (by omega) (by omega)
  exact in_scan _ _ _ row17_3840 _ (by omega) (by omega)

private theorem row18_0 : scan 18 0 384=true := by decide +kernel
private theorem row18_384 : scan 18 384 384=true := by decide +kernel
private theorem row18_768 : scan 18 768 384=true := by decide +kernel
private theorem row18_1152 : scan 18 1152 384=true := by decide +kernel
private theorem row18_1536 : scan 18 1536 384=true := by decide +kernel
private theorem row18_1920 : scan 18 1920 384=true := by decide +kernel
private theorem row18_2304 : scan 18 2304 384=true := by decide +kernel
private theorem row18_2688 : scan 18 2688 384=true := by decide +kernel
private theorem row18_3072 : scan 18 3072 384=true := by decide +kernel
private theorem row18_3456 : scan 18 3456 384=true := by decide +kernel
private theorem row18_3840 : scan 18 3840 384=true := by decide +kernel
private theorem row18_4224 : scan 18 4224 64=true := by decide +kernel
theorem labels18 (i : Nat) (hi : i<4288) : compareAt 18 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row18_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row18_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row18_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row18_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row18_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row18_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row18_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row18_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row18_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row18_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row18_3840 _ (by omega) (by omega)
  exact in_scan _ _ _ row18_4224 _ (by omega) (by omega)

private theorem row19_0 : scan 19 0 384=true := by decide +kernel
private theorem row19_384 : scan 19 384 384=true := by decide +kernel
private theorem row19_768 : scan 19 768 384=true := by decide +kernel
private theorem row19_1152 : scan 19 1152 384=true := by decide +kernel
private theorem row19_1536 : scan 19 1536 384=true := by decide +kernel
private theorem row19_1920 : scan 19 1920 384=true := by decide +kernel
private theorem row19_2304 : scan 19 2304 384=true := by decide +kernel
private theorem row19_2688 : scan 19 2688 384=true := by decide +kernel
private theorem row19_3072 : scan 19 3072 384=true := by decide +kernel
private theorem row19_3456 : scan 19 3456 384=true := by decide +kernel
private theorem row19_3840 : scan 19 3840 384=true := by decide +kernel
private theorem row19_4224 : scan 19 4224 304=true := by decide +kernel
theorem labels19 (i : Nat) (hi : i<4528) : compareAt 19 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row19_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row19_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row19_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row19_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row19_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row19_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row19_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row19_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row19_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row19_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row19_3840 _ (by omega) (by omega)
  exact in_scan _ _ _ row19_4224 _ (by omega) (by omega)

private theorem row20_0 : scan 20 0 384=true := by decide +kernel
private theorem row20_384 : scan 20 384 384=true := by decide +kernel
private theorem row20_768 : scan 20 768 384=true := by decide +kernel
private theorem row20_1152 : scan 20 1152 384=true := by decide +kernel
private theorem row20_1536 : scan 20 1536 384=true := by decide +kernel
private theorem row20_1920 : scan 20 1920 384=true := by decide +kernel
private theorem row20_2304 : scan 20 2304 384=true := by decide +kernel
private theorem row20_2688 : scan 20 2688 384=true := by decide +kernel
private theorem row20_3072 : scan 20 3072 384=true := by decide +kernel
private theorem row20_3456 : scan 20 3456 384=true := by decide +kernel
private theorem row20_3840 : scan 20 3840 384=true := by decide +kernel
private theorem row20_4224 : scan 20 4224 384=true := by decide +kernel
private theorem row20_4608 : scan 20 4608 160=true := by decide +kernel
theorem labels20 (i : Nat) (hi : i<4768) : compareAt 20 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row20_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row20_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row20_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row20_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row20_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row20_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row20_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row20_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row20_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row20_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row20_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row20_4224 _ (by omega) (by omega)
  exact in_scan _ _ _ row20_4608 _ (by omega) (by omega)

private theorem row21_0 : scan 21 0 384=true := by decide +kernel
private theorem row21_384 : scan 21 384 384=true := by decide +kernel
private theorem row21_768 : scan 21 768 384=true := by decide +kernel
private theorem row21_1152 : scan 21 1152 384=true := by decide +kernel
private theorem row21_1536 : scan 21 1536 384=true := by decide +kernel
private theorem row21_1920 : scan 21 1920 384=true := by decide +kernel
private theorem row21_2304 : scan 21 2304 384=true := by decide +kernel
private theorem row21_2688 : scan 21 2688 384=true := by decide +kernel
private theorem row21_3072 : scan 21 3072 384=true := by decide +kernel
private theorem row21_3456 : scan 21 3456 384=true := by decide +kernel
private theorem row21_3840 : scan 21 3840 384=true := by decide +kernel
private theorem row21_4224 : scan 21 4224 384=true := by decide +kernel
private theorem row21_4608 : scan 21 4608 384=true := by decide +kernel
private theorem row21_4992 : scan 21 4992 16=true := by decide +kernel
theorem labels21 (i : Nat) (hi : i<5008) : compareAt 21 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row21_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row21_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row21_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row21_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row21_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row21_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row21_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row21_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row21_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row21_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row21_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row21_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row21_4608 _ (by omega) (by omega)
  exact in_scan _ _ _ row21_4992 _ (by omega) (by omega)

private theorem row22_0 : scan 22 0 384=true := by decide +kernel
private theorem row22_384 : scan 22 384 384=true := by decide +kernel
private theorem row22_768 : scan 22 768 384=true := by decide +kernel
private theorem row22_1152 : scan 22 1152 384=true := by decide +kernel
private theorem row22_1536 : scan 22 1536 384=true := by decide +kernel
private theorem row22_1920 : scan 22 1920 384=true := by decide +kernel
private theorem row22_2304 : scan 22 2304 384=true := by decide +kernel
private theorem row22_2688 : scan 22 2688 384=true := by decide +kernel
private theorem row22_3072 : scan 22 3072 384=true := by decide +kernel
private theorem row22_3456 : scan 22 3456 384=true := by decide +kernel
private theorem row22_3840 : scan 22 3840 384=true := by decide +kernel
private theorem row22_4224 : scan 22 4224 384=true := by decide +kernel
private theorem row22_4608 : scan 22 4608 384=true := by decide +kernel
private theorem row22_4992 : scan 22 4992 256=true := by decide +kernel
theorem labels22 (i : Nat) (hi : i<5248) : compareAt 22 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row22_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row22_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row22_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row22_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row22_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row22_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row22_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row22_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row22_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row22_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row22_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row22_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row22_4608 _ (by omega) (by omega)
  exact in_scan _ _ _ row22_4992 _ (by omega) (by omega)

private theorem row23_0 : scan 23 0 384=true := by decide +kernel
private theorem row23_384 : scan 23 384 384=true := by decide +kernel
private theorem row23_768 : scan 23 768 384=true := by decide +kernel
private theorem row23_1152 : scan 23 1152 384=true := by decide +kernel
private theorem row23_1536 : scan 23 1536 384=true := by decide +kernel
private theorem row23_1920 : scan 23 1920 384=true := by decide +kernel
private theorem row23_2304 : scan 23 2304 384=true := by decide +kernel
private theorem row23_2688 : scan 23 2688 384=true := by decide +kernel
private theorem row23_3072 : scan 23 3072 384=true := by decide +kernel
private theorem row23_3456 : scan 23 3456 384=true := by decide +kernel
private theorem row23_3840 : scan 23 3840 384=true := by decide +kernel
private theorem row23_4224 : scan 23 4224 384=true := by decide +kernel
private theorem row23_4608 : scan 23 4608 384=true := by decide +kernel
private theorem row23_4992 : scan 23 4992 384=true := by decide +kernel
private theorem row23_5376 : scan 23 5376 112=true := by decide +kernel
theorem labels23 (i : Nat) (hi : i<5488) : compareAt 23 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row23_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row23_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row23_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row23_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row23_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row23_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row23_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row23_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row23_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row23_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row23_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row23_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row23_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row23_4992 _ (by omega) (by omega)
  exact in_scan _ _ _ row23_5376 _ (by omega) (by omega)

private theorem row24_0 : scan 24 0 384=true := by decide +kernel
private theorem row24_384 : scan 24 384 384=true := by decide +kernel
private theorem row24_768 : scan 24 768 384=true := by decide +kernel
private theorem row24_1152 : scan 24 1152 384=true := by decide +kernel
private theorem row24_1536 : scan 24 1536 384=true := by decide +kernel
private theorem row24_1920 : scan 24 1920 384=true := by decide +kernel
private theorem row24_2304 : scan 24 2304 384=true := by decide +kernel
private theorem row24_2688 : scan 24 2688 384=true := by decide +kernel
private theorem row24_3072 : scan 24 3072 384=true := by decide +kernel
private theorem row24_3456 : scan 24 3456 384=true := by decide +kernel
private theorem row24_3840 : scan 24 3840 384=true := by decide +kernel
private theorem row24_4224 : scan 24 4224 384=true := by decide +kernel
private theorem row24_4608 : scan 24 4608 384=true := by decide +kernel
private theorem row24_4992 : scan 24 4992 384=true := by decide +kernel
private theorem row24_5376 : scan 24 5376 336=true := by decide +kernel
theorem labels24 (i : Nat) (hi : i<5712) : compareAt 24 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row24_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row24_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row24_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row24_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row24_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row24_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row24_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row24_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row24_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row24_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row24_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row24_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row24_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row24_4992 _ (by omega) (by omega)
  exact in_scan _ _ _ row24_5376 _ (by omega) (by omega)

end CommitGolfCandidate.CapB.Symbol
