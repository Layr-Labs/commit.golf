import CommitGolfCandidate.CapBScans2
namespace CommitGolfCandidate.CapB.Symbol
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
private theorem row25_0 : scan 25 0 384=true := by decide +kernel
private theorem row25_384 : scan 25 384 384=true := by decide +kernel
private theorem row25_768 : scan 25 768 384=true := by decide +kernel
private theorem row25_1152 : scan 25 1152 384=true := by decide +kernel
private theorem row25_1536 : scan 25 1536 384=true := by decide +kernel
private theorem row25_1920 : scan 25 1920 384=true := by decide +kernel
private theorem row25_2304 : scan 25 2304 384=true := by decide +kernel
private theorem row25_2688 : scan 25 2688 384=true := by decide +kernel
private theorem row25_3072 : scan 25 3072 384=true := by decide +kernel
private theorem row25_3456 : scan 25 3456 384=true := by decide +kernel
private theorem row25_3840 : scan 25 3840 384=true := by decide +kernel
private theorem row25_4224 : scan 25 4224 384=true := by decide +kernel
private theorem row25_4608 : scan 25 4608 384=true := by decide +kernel
private theorem row25_4992 : scan 25 4992 384=true := by decide +kernel
private theorem row25_5376 : scan 25 5376 384=true := by decide +kernel
private theorem row25_5760 : scan 25 5760 192=true := by decide +kernel
theorem labels25 (i : Nat) (hi : i<5952) : compareAt 25 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row25_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row25_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row25_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row25_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row25_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row25_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row25_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row25_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row25_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row25_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row25_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row25_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row25_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row25_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row25_5376 _ (by omega) (by omega)
  exact in_scan _ _ _ row25_5760 _ (by omega) (by omega)

private theorem row26_0 : scan 26 0 384=true := by decide +kernel
private theorem row26_384 : scan 26 384 384=true := by decide +kernel
private theorem row26_768 : scan 26 768 384=true := by decide +kernel
private theorem row26_1152 : scan 26 1152 384=true := by decide +kernel
private theorem row26_1536 : scan 26 1536 384=true := by decide +kernel
private theorem row26_1920 : scan 26 1920 384=true := by decide +kernel
private theorem row26_2304 : scan 26 2304 384=true := by decide +kernel
private theorem row26_2688 : scan 26 2688 384=true := by decide +kernel
private theorem row26_3072 : scan 26 3072 384=true := by decide +kernel
private theorem row26_3456 : scan 26 3456 384=true := by decide +kernel
private theorem row26_3840 : scan 26 3840 384=true := by decide +kernel
private theorem row26_4224 : scan 26 4224 384=true := by decide +kernel
private theorem row26_4608 : scan 26 4608 384=true := by decide +kernel
private theorem row26_4992 : scan 26 4992 384=true := by decide +kernel
private theorem row26_5376 : scan 26 5376 384=true := by decide +kernel
private theorem row26_5760 : scan 26 5760 384=true := by decide +kernel
private theorem row26_6144 : scan 26 6144 48=true := by decide +kernel
theorem labels26 (i : Nat) (hi : i<6192) : compareAt 26 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row26_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row26_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row26_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row26_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row26_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row26_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row26_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row26_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row26_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row26_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row26_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row26_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row26_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row26_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row26_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row26_5760 _ (by omega) (by omega)
  exact in_scan _ _ _ row26_6144 _ (by omega) (by omega)

private theorem row27_0 : scan 27 0 384=true := by decide +kernel
private theorem row27_384 : scan 27 384 384=true := by decide +kernel
private theorem row27_768 : scan 27 768 384=true := by decide +kernel
private theorem row27_1152 : scan 27 1152 384=true := by decide +kernel
private theorem row27_1536 : scan 27 1536 384=true := by decide +kernel
private theorem row27_1920 : scan 27 1920 384=true := by decide +kernel
private theorem row27_2304 : scan 27 2304 384=true := by decide +kernel
private theorem row27_2688 : scan 27 2688 384=true := by decide +kernel
private theorem row27_3072 : scan 27 3072 384=true := by decide +kernel
private theorem row27_3456 : scan 27 3456 384=true := by decide +kernel
private theorem row27_3840 : scan 27 3840 384=true := by decide +kernel
private theorem row27_4224 : scan 27 4224 384=true := by decide +kernel
private theorem row27_4608 : scan 27 4608 384=true := by decide +kernel
private theorem row27_4992 : scan 27 4992 384=true := by decide +kernel
private theorem row27_5376 : scan 27 5376 384=true := by decide +kernel
private theorem row27_5760 : scan 27 5760 384=true := by decide +kernel
private theorem row27_6144 : scan 27 6144 288=true := by decide +kernel
theorem labels27 (i : Nat) (hi : i<6432) : compareAt 27 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row27_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row27_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row27_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row27_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row27_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row27_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row27_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row27_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row27_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row27_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row27_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row27_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row27_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row27_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row27_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row27_5760 _ (by omega) (by omega)
  exact in_scan _ _ _ row27_6144 _ (by omega) (by omega)

private theorem row28_0 : scan 28 0 384=true := by decide +kernel
private theorem row28_384 : scan 28 384 384=true := by decide +kernel
private theorem row28_768 : scan 28 768 384=true := by decide +kernel
private theorem row28_1152 : scan 28 1152 384=true := by decide +kernel
private theorem row28_1536 : scan 28 1536 384=true := by decide +kernel
private theorem row28_1920 : scan 28 1920 384=true := by decide +kernel
private theorem row28_2304 : scan 28 2304 384=true := by decide +kernel
private theorem row28_2688 : scan 28 2688 384=true := by decide +kernel
private theorem row28_3072 : scan 28 3072 384=true := by decide +kernel
private theorem row28_3456 : scan 28 3456 384=true := by decide +kernel
private theorem row28_3840 : scan 28 3840 384=true := by decide +kernel
private theorem row28_4224 : scan 28 4224 384=true := by decide +kernel
private theorem row28_4608 : scan 28 4608 384=true := by decide +kernel
private theorem row28_4992 : scan 28 4992 384=true := by decide +kernel
private theorem row28_5376 : scan 28 5376 384=true := by decide +kernel
private theorem row28_5760 : scan 28 5760 384=true := by decide +kernel
private theorem row28_6144 : scan 28 6144 384=true := by decide +kernel
private theorem row28_6528 : scan 28 6528 144=true := by decide +kernel
theorem labels28 (i : Nat) (hi : i<6672) : compareAt 28 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row28_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row28_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row28_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row28_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row28_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row28_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row28_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row28_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row28_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row28_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row28_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row28_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row28_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row28_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row28_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row28_5760 _ (by omega) (by omega)
  by_cases lim6144 : i<6528
  · exact in_scan _ _ _ row28_6144 _ (by omega) (by omega)
  exact in_scan _ _ _ row28_6528 _ (by omega) (by omega)

private theorem row29_0 : scan 29 0 384=true := by decide +kernel
private theorem row29_384 : scan 29 384 384=true := by decide +kernel
private theorem row29_768 : scan 29 768 384=true := by decide +kernel
private theorem row29_1152 : scan 29 1152 384=true := by decide +kernel
private theorem row29_1536 : scan 29 1536 384=true := by decide +kernel
private theorem row29_1920 : scan 29 1920 384=true := by decide +kernel
private theorem row29_2304 : scan 29 2304 384=true := by decide +kernel
private theorem row29_2688 : scan 29 2688 384=true := by decide +kernel
private theorem row29_3072 : scan 29 3072 384=true := by decide +kernel
private theorem row29_3456 : scan 29 3456 384=true := by decide +kernel
private theorem row29_3840 : scan 29 3840 384=true := by decide +kernel
private theorem row29_4224 : scan 29 4224 384=true := by decide +kernel
private theorem row29_4608 : scan 29 4608 384=true := by decide +kernel
private theorem row29_4992 : scan 29 4992 384=true := by decide +kernel
private theorem row29_5376 : scan 29 5376 384=true := by decide +kernel
private theorem row29_5760 : scan 29 5760 384=true := by decide +kernel
private theorem row29_6144 : scan 29 6144 384=true := by decide +kernel
private theorem row29_6528 : scan 29 6528 384=true := by decide +kernel
theorem labels29 (i : Nat) (hi : i<6912) : compareAt 29 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row29_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row29_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row29_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row29_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row29_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row29_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row29_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row29_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row29_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row29_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row29_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row29_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row29_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row29_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row29_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row29_5760 _ (by omega) (by omega)
  by_cases lim6144 : i<6528
  · exact in_scan _ _ _ row29_6144 _ (by omega) (by omega)
  exact in_scan _ _ _ row29_6528 _ (by omega) (by omega)

private theorem row30_0 : scan 30 0 384=true := by decide +kernel
private theorem row30_384 : scan 30 384 384=true := by decide +kernel
private theorem row30_768 : scan 30 768 384=true := by decide +kernel
private theorem row30_1152 : scan 30 1152 384=true := by decide +kernel
private theorem row30_1536 : scan 30 1536 384=true := by decide +kernel
private theorem row30_1920 : scan 30 1920 384=true := by decide +kernel
private theorem row30_2304 : scan 30 2304 384=true := by decide +kernel
private theorem row30_2688 : scan 30 2688 384=true := by decide +kernel
private theorem row30_3072 : scan 30 3072 384=true := by decide +kernel
private theorem row30_3456 : scan 30 3456 384=true := by decide +kernel
private theorem row30_3840 : scan 30 3840 384=true := by decide +kernel
private theorem row30_4224 : scan 30 4224 384=true := by decide +kernel
private theorem row30_4608 : scan 30 4608 384=true := by decide +kernel
private theorem row30_4992 : scan 30 4992 384=true := by decide +kernel
private theorem row30_5376 : scan 30 5376 384=true := by decide +kernel
private theorem row30_5760 : scan 30 5760 384=true := by decide +kernel
private theorem row30_6144 : scan 30 6144 384=true := by decide +kernel
private theorem row30_6528 : scan 30 6528 384=true := by decide +kernel
private theorem row30_6912 : scan 30 6912 240=true := by decide +kernel
theorem labels30 (i : Nat) (hi : i<7152) : compareAt 30 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row30_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row30_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row30_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row30_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row30_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row30_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row30_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row30_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row30_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row30_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row30_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row30_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row30_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row30_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row30_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row30_5760 _ (by omega) (by omega)
  by_cases lim6144 : i<6528
  · exact in_scan _ _ _ row30_6144 _ (by omega) (by omega)
  by_cases lim6528 : i<6912
  · exact in_scan _ _ _ row30_6528 _ (by omega) (by omega)
  exact in_scan _ _ _ row30_6912 _ (by omega) (by omega)

private theorem row31_0 : scan 31 0 384=true := by decide +kernel
private theorem row31_384 : scan 31 384 384=true := by decide +kernel
private theorem row31_768 : scan 31 768 384=true := by decide +kernel
private theorem row31_1152 : scan 31 1152 384=true := by decide +kernel
private theorem row31_1536 : scan 31 1536 384=true := by decide +kernel
private theorem row31_1920 : scan 31 1920 384=true := by decide +kernel
private theorem row31_2304 : scan 31 2304 384=true := by decide +kernel
private theorem row31_2688 : scan 31 2688 384=true := by decide +kernel
private theorem row31_3072 : scan 31 3072 384=true := by decide +kernel
private theorem row31_3456 : scan 31 3456 384=true := by decide +kernel
private theorem row31_3840 : scan 31 3840 384=true := by decide +kernel
private theorem row31_4224 : scan 31 4224 384=true := by decide +kernel
private theorem row31_4608 : scan 31 4608 384=true := by decide +kernel
private theorem row31_4992 : scan 31 4992 384=true := by decide +kernel
private theorem row31_5376 : scan 31 5376 384=true := by decide +kernel
private theorem row31_5760 : scan 31 5760 384=true := by decide +kernel
private theorem row31_6144 : scan 31 6144 384=true := by decide +kernel
private theorem row31_6528 : scan 31 6528 384=true := by decide +kernel
private theorem row31_6912 : scan 31 6912 384=true := by decide +kernel
private theorem row31_7296 : scan 31 7296 96=true := by decide +kernel
theorem labels31 (i : Nat) (hi : i<7392) : compareAt 31 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row31_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row31_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row31_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row31_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row31_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row31_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row31_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row31_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row31_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row31_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row31_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row31_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row31_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row31_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row31_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row31_5760 _ (by omega) (by omega)
  by_cases lim6144 : i<6528
  · exact in_scan _ _ _ row31_6144 _ (by omega) (by omega)
  by_cases lim6528 : i<6912
  · exact in_scan _ _ _ row31_6528 _ (by omega) (by omega)
  by_cases lim6912 : i<7296
  · exact in_scan _ _ _ row31_6912 _ (by omega) (by omega)
  exact in_scan _ _ _ row31_7296 _ (by omega) (by omega)

private theorem row32_0 : scan 32 0 384=true := by decide +kernel
private theorem row32_384 : scan 32 384 384=true := by decide +kernel
private theorem row32_768 : scan 32 768 384=true := by decide +kernel
private theorem row32_1152 : scan 32 1152 384=true := by decide +kernel
private theorem row32_1536 : scan 32 1536 384=true := by decide +kernel
private theorem row32_1920 : scan 32 1920 384=true := by decide +kernel
private theorem row32_2304 : scan 32 2304 384=true := by decide +kernel
private theorem row32_2688 : scan 32 2688 384=true := by decide +kernel
private theorem row32_3072 : scan 32 3072 384=true := by decide +kernel
private theorem row32_3456 : scan 32 3456 384=true := by decide +kernel
private theorem row32_3840 : scan 32 3840 384=true := by decide +kernel
private theorem row32_4224 : scan 32 4224 384=true := by decide +kernel
private theorem row32_4608 : scan 32 4608 384=true := by decide +kernel
private theorem row32_4992 : scan 32 4992 384=true := by decide +kernel
private theorem row32_5376 : scan 32 5376 384=true := by decide +kernel
private theorem row32_5760 : scan 32 5760 384=true := by decide +kernel
private theorem row32_6144 : scan 32 6144 384=true := by decide +kernel
private theorem row32_6528 : scan 32 6528 384=true := by decide +kernel
private theorem row32_6912 : scan 32 6912 384=true := by decide +kernel
private theorem row32_7296 : scan 32 7296 320=true := by decide +kernel
theorem labels32 (i : Nat) (hi : i<7616) : compareAt 32 i=true := by
  by_cases lim0 : i<384
  · exact in_scan _ _ _ row32_0 _ (by omega) (by omega)
  by_cases lim384 : i<768
  · exact in_scan _ _ _ row32_384 _ (by omega) (by omega)
  by_cases lim768 : i<1152
  · exact in_scan _ _ _ row32_768 _ (by omega) (by omega)
  by_cases lim1152 : i<1536
  · exact in_scan _ _ _ row32_1152 _ (by omega) (by omega)
  by_cases lim1536 : i<1920
  · exact in_scan _ _ _ row32_1536 _ (by omega) (by omega)
  by_cases lim1920 : i<2304
  · exact in_scan _ _ _ row32_1920 _ (by omega) (by omega)
  by_cases lim2304 : i<2688
  · exact in_scan _ _ _ row32_2304 _ (by omega) (by omega)
  by_cases lim2688 : i<3072
  · exact in_scan _ _ _ row32_2688 _ (by omega) (by omega)
  by_cases lim3072 : i<3456
  · exact in_scan _ _ _ row32_3072 _ (by omega) (by omega)
  by_cases lim3456 : i<3840
  · exact in_scan _ _ _ row32_3456 _ (by omega) (by omega)
  by_cases lim3840 : i<4224
  · exact in_scan _ _ _ row32_3840 _ (by omega) (by omega)
  by_cases lim4224 : i<4608
  · exact in_scan _ _ _ row32_4224 _ (by omega) (by omega)
  by_cases lim4608 : i<4992
  · exact in_scan _ _ _ row32_4608 _ (by omega) (by omega)
  by_cases lim4992 : i<5376
  · exact in_scan _ _ _ row32_4992 _ (by omega) (by omega)
  by_cases lim5376 : i<5760
  · exact in_scan _ _ _ row32_5376 _ (by omega) (by omega)
  by_cases lim5760 : i<6144
  · exact in_scan _ _ _ row32_5760 _ (by omega) (by omega)
  by_cases lim6144 : i<6528
  · exact in_scan _ _ _ row32_6144 _ (by omega) (by omega)
  by_cases lim6528 : i<6912
  · exact in_scan _ _ _ row32_6528 _ (by omega) (by omega)
  by_cases lim6912 : i<7296
  · exact in_scan _ _ _ row32_6912 _ (by omega) (by omega)
  exact in_scan _ _ _ row32_7296 _ (by omega) (by omega)

end CommitGolfCandidate.CapB.Symbol
