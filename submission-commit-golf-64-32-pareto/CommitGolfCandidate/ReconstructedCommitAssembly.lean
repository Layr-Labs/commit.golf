import CommitGolfCandidate.ReconstructedCommitReceipts
import CommitGolfCandidate.ReconstructedCommitSchedule

namespace CommitGolfCandidate.Reconstruction.CommitAssembly
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitControl CommitBlocks
open CommitSetup CommitSchedule CommitReceipts
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] ArtifactEncoding.decode

-- The statement for each body is universal in the incoming loop counter.
private theorem body8 (c : Word) : Fragment im 10 10 0
    (At (addr 8) c) (At (addr 18) c) := by
  have h8 := lineWord 8 18 10 0 c (by decide) (by decide) pc8
  exact h8

private theorem reset18 : Fragment im 1 1 0 (StateAt 18 0)
    (StateAt 19 4096) := by
  apply set_counter 18 0 4096 (.LUI .x20 1) (reads_at 18 _ rfl) _ rfl
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body19 (c : Word) : Fragment im 52994 300480 8534
    (At (addr 19) c) (At (addr 53013) c) := by
  have h19 := lineWord 19 787 4364 124 c (by decide) (by decide) pc19
  have h787 := lineWord 787 1555 4335 123 c (by decide) (by decide) pc787
  have h1555 := lineWord 1555 2323 4335 123 c (by decide) (by decide) pc1555
  have h2323 := lineWord 2323 3091 4364 124 c (by decide) (by decide) pc2323
  have h3091 := lineWord 3091 3859 4364 124 c (by decide) (by decide) pc3091
  have h3859 := lineWord 3859 4627 4335 123 c (by decide) (by decide) pc3859
  have h4627 := lineWord 4627 5395 4364 124 c (by decide) (by decide) pc4627
  have h5395 := lineWord 5395 6163 4364 124 c (by decide) (by decide) pc5395
  have h6163 := lineWord 6163 6931 4335 123 c (by decide) (by decide) pc6163
  have h6931 := lineWord 6931 7699 4364 124 c (by decide) (by decide) pc6931
  have h7699 := lineWord 7699 8467 4364 124 c (by decide) (by decide) pc7699
  have h8467 := lineWord 8467 9235 4335 123 c (by decide) (by decide) pc8467
  have h9235 := lineWord 9235 10003 4364 124 c (by decide) (by decide) pc9235
  have h10003 := lineWord 10003 10771 4364 124 c (by decide) (by decide) pc10003
  have h10771 := lineWord 10771 11539 4335 123 c (by decide) (by decide) pc10771
  have h11539 := lineWord 11539 12307 4393 125 c (by decide) (by decide) pc11539
  have h12307 := lineWord 12307 13075 4335 123 c (by decide) (by decide) pc12307
  have h13075 := lineWord 13075 13843 4393 125 c (by decide) (by decide) pc13075
  have h13843 := lineWord 13843 14611 4335 123 c (by decide) (by decide) pc13843
  have h14611 := lineWord 14611 15379 4335 123 c (by decide) (by decide) pc14611
  have h15379 := lineWord 15379 16147 4364 124 c (by decide) (by decide) pc15379
  have h16147 := lineWord 16147 16915 4335 123 c (by decide) (by decide) pc16147
  have h16915 := lineWord 16915 17683 4335 123 c (by decide) (by decide) pc16915
  have h17683 := lineWord 17683 18451 4364 124 c (by decide) (by decide) pc17683
  have h18451 := lineWord 18451 19219 4364 124 c (by decide) (by decide) pc18451
  have h19219 := lineWord 19219 19987 4335 123 c (by decide) (by decide) pc19219
  have h19987 := lineWord 19987 20755 4364 124 c (by decide) (by decide) pc19987
  have h20755 := lineWord 20755 21523 4364 124 c (by decide) (by decide) pc20755
  have h21523 := lineWord 21523 22291 4364 124 c (by decide) (by decide) pc21523
  have h22291 := lineWord 22291 23059 4364 124 c (by decide) (by decide) pc22291
  have h23059 := lineWord 23059 23827 4335 123 c (by decide) (by decide) pc23059
  have h23827 := lineWord 23827 24595 4364 124 c (by decide) (by decide) pc23827
  have h24595 := lineWord 24595 25363 4364 124 c (by decide) (by decide) pc24595
  have h25363 := lineWord 25363 26131 4335 123 c (by decide) (by decide) pc25363
  have h26131 := lineWord 26131 26899 4364 124 c (by decide) (by decide) pc26131
  have h26899 := lineWord 26899 27667 4364 124 c (by decide) (by decide) pc26899
  have h27667 := lineWord 27667 28435 4364 124 c (by decide) (by decide) pc27667
  have h28435 := lineWord 28435 29203 4335 123 c (by decide) (by decide) pc28435
  have h29203 := lineWord 29203 29971 4364 124 c (by decide) (by decide) pc29203
  have h29971 := lineWord 29971 30739 4335 123 c (by decide) (by decide) pc29971
  have h30739 := lineWord 30739 31507 4364 124 c (by decide) (by decide) pc30739
  have h31507 := lineWord 31507 32275 4335 123 c (by decide) (by decide) pc31507
  have h32275 := lineWord 32275 33043 4364 124 c (by decide) (by decide) pc32275
  have h33043 := lineWord 33043 33811 4364 124 c (by decide) (by decide) pc33043
  have h33811 := lineWord 33811 34579 4335 123 c (by decide) (by decide) pc33811
  have h34579 := lineWord 34579 35347 4364 124 c (by decide) (by decide) pc34579
  have h35347 := lineWord 35347 36115 4364 124 c (by decide) (by decide) pc35347
  have h36115 := lineWord 36115 36883 4335 123 c (by decide) (by decide) pc36115
  have h36883 := lineWord 36883 37651 4364 124 c (by decide) (by decide) pc36883
  have h37651 := lineWord 37651 38419 4364 124 c (by decide) (by decide) pc37651
  have h38419 := lineWord 38419 39187 4335 123 c (by decide) (by decide) pc38419
  have h39187 := lineWord 39187 39955 4393 125 c (by decide) (by decide) pc39187
  have h39955 := lineWord 39955 40723 4335 123 c (by decide) (by decide) pc39955
  have h40723 := lineWord 40723 41491 4364 124 c (by decide) (by decide) pc40723
  have h41491 := lineWord 41491 42259 4364 124 c (by decide) (by decide) pc41491
  have h42259 := lineWord 42259 43027 4364 124 c (by decide) (by decide) pc42259
  have h43027 := lineWord 43027 43795 4335 123 c (by decide) (by decide) pc43027
  have h43795 := lineWord 43795 44563 4335 123 c (by decide) (by decide) pc43795
  have h44563 := lineWord 44563 45331 4364 124 c (by decide) (by decide) pc44563
  have h45331 := lineWord 45331 46099 4364 124 c (by decide) (by decide) pc45331
  have h46099 := lineWord 46099 46867 4335 123 c (by decide) (by decide) pc46099
  have h46867 := lineWord 46867 47635 4335 123 c (by decide) (by decide) pc46867
  have h47635 := lineWord 47635 48403 4364 124 c (by decide) (by decide) pc47635
  have h48403 := lineWord 48403 49171 4364 124 c (by decide) (by decide) pc48403
  have h49171 := lineWord 49171 49939 4335 123 c (by decide) (by decide) pc49171
  have h49939 := lineWord 49939 50707 4393 125 c (by decide) (by decide) pc49939
  have h50707 := lineWord 50707 51475 4335 123 c (by decide) (by decide) pc50707
  have h51475 := lineWord 51475 52243 4364 124 c (by decide) (by decide) pc51475
  have h52243 := lineWord 52243 53011 4393 125 c (by decide) (by decide) pc52243
  have h53011 := lineWord 53011 53013 2 0 c (by decide) (by decide) pc53011
  exact (compose (compose (compose (compose (compose (compose h19 h787) (compose h1555 h2323)) (compose (compose h3091 h3859) (compose h4627 h5395))) (compose (compose (compose h6163 h6931) (compose h7699 h8467)) (compose (compose h9235 h10003) (compose h10771 (compose h11539 h12307))))) (compose (compose (compose (compose h13075 h13843) (compose h14611 h15379)) (compose (compose h16147 h16915) (compose h17683 (compose h18451 h19219)))) (compose (compose (compose h19987 h20755) (compose h21523 h22291)) (compose (compose h23059 h23827) (compose h24595 (compose h25363 h26131)))))) (compose (compose (compose (compose (compose h26899 h27667) (compose h28435 h29203)) (compose (compose h29971 h30739) (compose h31507 h32275))) (compose (compose (compose h33043 h33811) (compose h34579 h35347)) (compose (compose h36115 h36883) (compose h37651 (compose h38419 h39187))))) (compose (compose (compose (compose h39955 h40723) (compose h41491 h42259)) (compose (compose h43027 h43795) (compose h44563 (compose h45331 h46099)))) (compose (compose (compose h46867 h47635) (compose h48403 h49171)) (compose (compose h49939 h50707) (compose h51475 (compose h52243 h53011)))))))

private theorem repeat19 : Fragment im 217075711
    1230778367 34955264 (StateAt 19 4096) (StateAt 53016 0) :=
  loop 19 53013 4095 300480 8534 (by decide) 1885168
    body19 (reads_at 53013 _ rfl) (reads_at 53014 _ rfl) (reads_at 53015 _ rfl) rfl

private theorem body53016 (c : Word) : Fragment im 8 8 0
    (At (addr 53016) c) (AtC (addr 53024) c) := by
  have h53016 := lineWord 53016 53017 1 0 c (by decide) (by decide) pc53016
  have h53017 := kind_reset im (addr 53017) c (reads_at 53017 _ rfl)
  have h53018 := lineWordC 53018 53024 6 0 c (by decide) (by decide) pc53018
  exact compose (compose h53016 h53017) h53018

private theorem reset53024 : Fragment im 1 1 0 (StateAtC 53024 0)
    (StateAtC 53025 16384) := by
  apply set_counterC 53024 0 16384 (.LUI .x20 4) (reads_at 53024 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body53025 (c : Word) : Fragment im 2 2 0
    (AtC (addr 53025) c) (AtC (addr 53027) c) := by
  have h53025 := lineWordC 53025 53027 2 0 c (by decide) (by decide) pc53025
  exact h53025

private theorem body53027 (c : Word) : Fragment im 3084 6668 512
    (AtC (addr 53027) c) (AtC (addr 56111) c) := by
  have h53027 := lineWordC 53027 53795 1664 128 c (by decide) (by decide) pc53027
  have h53795 := lineWordC 53795 54563 1657 127 c (by decide) (by decide) pc53795
  have h54563 := lineWordC 54563 55331 1664 128 c (by decide) (by decide) pc54563
  have h55331 := lineWordC 55331 56099 1657 127 c (by decide) (by decide) pc55331
  have h56099 := lineWordC 56099 56111 26 2 c (by decide) (by decide) pc56099
  exact (compose (compose h53027 h53795) (compose h54563 (compose h55331 h56099)))

private theorem repeat53027 : Fragment im 50577407
    109297663 8388608 (StateAtC 53027 16384) (StateAtC 56114 0) :=
  loopC 53027 56111 16383 6668 512 (by decide) 2084808
    body53027 (reads_at 56111 _ rfl) (reads_at 56112 _ rfl) (reads_at 56113 _ rfl) rfl

private theorem body56114 (c : Word) : Fragment im 6 6 0
    (AtC (addr 56114) c) (AtC (addr 56120) c) := by
  have h56114 := lineWordC 56114 56120 6 0 c (by decide) (by decide) pc56114
  exact h56114

private theorem reset56120 : Fragment im 1 1 0 (StateAtC 56120 0)
    (StateAtC 56121 8192) := by
  apply set_counterC 56120 0 8192 (.LUI .x20 2) (reads_at 56120 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body56121 (c : Word) : Fragment im 2 2 0
    (AtC (addr 56121) c) (AtC (addr 56123) c) := by
  have h56121 := lineWordC 56121 56123 2 0 c (by decide) (by decide) pc56121
  exact h56121

private theorem body56123 (c : Word) : Fragment im 3084 6668 512
    (AtC (addr 56123) c) (AtC (addr 59207) c) := by
  have h56123 := lineWordC 56123 56891 1664 128 c (by decide) (by decide) pc56123
  have h56891 := lineWordC 56891 57659 1657 127 c (by decide) (by decide) pc56891
  have h57659 := lineWordC 57659 58427 1664 128 c (by decide) (by decide) pc57659
  have h58427 := lineWordC 58427 59195 1657 127 c (by decide) (by decide) pc58427
  have h59195 := lineWordC 59195 59207 26 2 c (by decide) (by decide) pc59195
  exact (compose (compose h56123 h56891) (compose h57659 (compose h58427 h59195)))

private theorem repeat56123 : Fragment im 25288703
    54648831 4194304 (StateAtC 56123 8192) (StateAtC 59210 0) :=
  loopC 56123 59207 8191 6668 512 (by decide) 2084808
    body56123 (reads_at 59207 _ rfl) (reads_at 59208 _ rfl) (reads_at 59209 _ rfl) rfl

private theorem body59210 (c : Word) : Fragment im 6 6 0
    (AtC (addr 59210) c) (AtC (addr 59216) c) := by
  have h59210 := lineWordC 59210 59216 6 0 c (by decide) (by decide) pc59210
  exact h59210

private theorem reset59216 : Fragment im 1 1 0 (StateAtC 59216 0)
    (StateAtC 59217 4096) := by
  apply set_counterC 59216 0 4096 (.LUI .x20 1) (reads_at 59216 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body59217 (c : Word) : Fragment im 2 2 0
    (AtC (addr 59217) c) (AtC (addr 59219) c) := by
  have h59217 := lineWordC 59217 59219 2 0 c (by decide) (by decide) pc59217
  exact h59217

private theorem body59219 (c : Word) : Fragment im 3084 6668 512
    (AtC (addr 59219) c) (AtC (addr 62303) c) := by
  have h59219 := lineWordC 59219 59987 1664 128 c (by decide) (by decide) pc59219
  have h59987 := lineWordC 59987 60755 1657 127 c (by decide) (by decide) pc59987
  have h60755 := lineWordC 60755 61523 1664 128 c (by decide) (by decide) pc60755
  have h61523 := lineWordC 61523 62291 1657 127 c (by decide) (by decide) pc61523
  have h62291 := lineWordC 62291 62303 26 2 c (by decide) (by decide) pc62291
  exact (compose (compose h59219 h59987) (compose h60755 (compose h61523 h62291)))

private theorem repeat59219 : Fragment im 12644351
    27324415 2097152 (StateAtC 59219 4096) (StateAtC 62306 0) :=
  loopC 59219 62303 4095 6668 512 (by decide) 2084808
    body59219 (reads_at 62303 _ rfl) (reads_at 62304 _ rfl) (reads_at 62305 _ rfl) rfl

private theorem body62306 (c : Word) : Fragment im 6 6 0
    (AtC (addr 62306) c) (AtC (addr 62312) c) := by
  have h62306 := lineWordC 62306 62312 6 0 c (by decide) (by decide) pc62306
  exact h62306

private theorem reset62312 : Fragment im 1 1 0 (StateAtC 62312 0)
    (StateAtC 62313 1) := by
  apply set_counterC 62312 0 1 (.ADDI .x20 .x0 1) (reads_at 62312 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem reset62313 : Fragment im 1 1 0 (StateAtC 62313 1)
    (StateAtC 62314 2048) := by
  apply set_counterC 62313 1 2048 (.SLLI .x20 .x20 11) (reads_at 62313 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  change s.getReg .x20 <<< 11 = _
  rw [hs.2.2]; rfl

private theorem body62314 (c : Word) : Fragment im 2 2 0
    (AtC (addr 62314) c) (AtC (addr 62316) c) := by
  have h62314 := lineWordC 62314 62316 2 0 c (by decide) (by decide) pc62314
  exact h62314

private theorem body62316 (c : Word) : Fragment im 4108 11276 1024
    (AtC (addr 62316) c) (AtC (addr 66424) c) := by
  have h62316 := lineWordC 62316 63084 2112 192 c (by decide) (by decide) pc62316
  have h63084 := lineWordC 63084 63852 2112 192 c (by decide) (by decide) pc63084
  have h63852 := lineWordC 63852 64620 2098 190 c (by decide) (by decide) pc63852
  have h64620 := lineWordC 64620 65388 2112 192 c (by decide) (by decide) pc64620
  have h65388 := lineWordC 65388 66156 2112 192 c (by decide) (by decide) pc65388
  have h66156 := lineWordC 66156 66424 730 66 c (by decide) (by decide) pc66156
  exact (compose (compose h62316 (compose h63084 h63852)) (compose h64620 (compose h65388 h66156)))

private theorem repeat62316 : Fragment im 8419327
    23099391 2097152 (StateAtC 62316 2048) (StateAtC 66427 0) :=
  loopC 62316 66424 2047 11276 1024 (by decide) 2080712
    body62316 (reads_at 66424 _ rfl) (reads_at 66425 _ rfl) (reads_at 66426 _ rfl) rfl

private theorem body66427 (c : Word) : Fragment im 6 6 0
    (AtC (addr 66427) c) (AtC (addr 66433) c) := by
  have h66427 := lineWordC 66427 66433 6 0 c (by decide) (by decide) pc66427
  exact h66427

private theorem reset66433 : Fragment im 1 1 0 (StateAtC 66433 0)
    (StateAtC 66434 1024) := by
  apply set_counterC 66433 0 1024 (.ADDI .x20 .x0 1024) (reads_at 66433 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body66434 (c : Word) : Fragment im 3 3 0
    (AtC (addr 66434) c) (AtC (addr 66437) c) := by
  have h66434 := lineWordC 66434 66437 3 0 c (by decide) (by decide) pc66434
  exact h66434

private theorem body66437 (c : Word) : Fragment im 4620 16908 1536
    (AtC (addr 66437) c) (AtC (addr 71057) c) := by
  have h66437 := lineWordC 66437 67205 2808 255 c (by decide) (by decide) pc66437
  have h67205 := lineWordC 67205 67973 2815 256 c (by decide) (by decide) pc67205
  have h67973 := lineWordC 67973 68741 2815 256 c (by decide) (by decide) pc67973
  have h68741 := lineWordC 68741 69509 2808 255 c (by decide) (by decide) pc68741
  have h69509 := lineWordC 69509 70277 2815 256 c (by decide) (by decide) pc69509
  have h70277 := lineWordC 70277 71045 2811 255 c (by decide) (by decide) pc70277
  have h71045 := lineWordC 71045 71057 36 3 c (by decide) (by decide) pc71045
  exact (compose (compose h66437 (compose h67205 h67973)) (compose (compose h68741 h69509) (compose h70277 h71045)))

private theorem repeat66437 : Fragment im 4733951
    17316863 1572864 (StateAtC 66437 1024) (StateAtC 71060 0) :=
  loopC 66437 71057 1023 16908 1536 (by decide) 2078664
    body66437 (reads_at 71057 _ rfl) (reads_at 71058 _ rfl) (reads_at 71059 _ rfl) rfl

private theorem body71060 (c : Word) : Fragment im 6 6 0
    (AtC (addr 71060) c) (AtC (addr 71066) c) := by
  have h71060 := lineWordC 71060 71066 6 0 c (by decide) (by decide) pc71060
  exact h71060

private theorem reset71066 : Fragment im 1 1 0 (StateAtC 71066 0)
    (StateAtC 71067 512) := by
  apply set_counterC 71066 0 512 (.ADDI .x20 .x0 512) (reads_at 71066 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body71067 (c : Word) : Fragment im 4 4 0
    (AtC (addr 71067) c) (AtC (addr 71071) c) := by
  have h71067 := lineWordC 71067 71071 4 0 c (by decide) (by decide) pc71067
  exact h71067

private theorem body71071 (c : Word) : Fragment im 5644 21516 2048
    (AtC (addr 71071) c) (AtC (addr 76715) c) := by
  have h71071 := lineWordC 71071 71839 2935 280 c (by decide) (by decide) pc71071
  have h71839 := lineWordC 71839 72607 2917 277 c (by decide) (by decide) pc71839
  have h72607 := lineWordC 72607 73375 2931 279 c (by decide) (by decide) pc72607
  have h73375 := lineWordC 73375 74143 2935 280 c (by decide) (by decide) pc73375
  have h74143 := lineWordC 74143 74911 2917 277 c (by decide) (by decide) pc74143
  have h74911 := lineWordC 74911 75679 2931 279 c (by decide) (by decide) pc74911
  have h75679 := lineWordC 75679 76447 2935 280 c (by decide) (by decide) pc75679
  have h76447 := lineWordC 76447 76715 1015 96 c (by decide) (by decide) pc76447
  exact (compose (compose (compose h71071 h71839) (compose h72607 h73375)) (compose (compose h74143 h74911) (compose h75679 h76447)))

private theorem repeat71071 : Fragment im 2891263
    11017727 1048576 (StateAtC 71071 512) (StateAtC 76718 0) :=
  loopC 71071 76715 511 21516 2048 (by decide) 2074568
    body71071 (reads_at 76715 _ rfl) (reads_at 76716 _ rfl) (reads_at 76717 _ rfl) rfl

private theorem body76718 (c : Word) : Fragment im 6 6 0
    (AtC (addr 76718) c) (AtC (addr 76724) c) := by
  have h76718 := lineWordC 76718 76724 6 0 c (by decide) (by decide) pc76718
  exact h76718

private theorem reset76724 : Fragment im 1 1 0 (StateAtC 76724 0)
    (StateAtC 76725 256) := by
  apply set_counterC 76724 0 256 (.ADDI .x20 .x0 256) (reads_at 76724 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body76725 (c : Word) : Fragment im 4 4 0
    (AtC (addr 76725) c) (AtC (addr 76729) c) := by
  have h76725 := lineWordC 76725 76729 4 0 c (by decide) (by decide) pc76725
  exact h76725

private theorem body76729 (c : Word) : Fragment im 6668 29708 3072
    (AtC (addr 76729) c) (AtC (addr 83397) c) := by
  have h76729 := lineWordC 76729 77497 3423 354 c (by decide) (by decide) pc76729
  have h77497 := lineWordC 77497 78265 3423 354 c (by decide) (by decide) pc77497
  have h78265 := lineWordC 78265 79033 3423 354 c (by decide) (by decide) pc78265
  have h79033 := lineWordC 79033 79801 3423 354 c (by decide) (by decide) pc79033
  have h79801 := lineWordC 79801 80569 3423 354 c (by decide) (by decide) pc79801
  have h80569 := lineWordC 80569 81337 3423 354 c (by decide) (by decide) pc80569
  have h81337 := lineWordC 81337 82105 3420 354 c (by decide) (by decide) pc81337
  have h82105 := lineWordC 82105 82873 3423 354 c (by decide) (by decide) pc82105
  have h82873 := lineWordC 82873 83397 2327 240 c (by decide) (by decide) pc82873
  exact (compose (compose (compose h76729 h77497) (compose h78265 h79033)) (compose (compose h79801 h80569) (compose h81337 (compose h82105 h82873))))

private theorem repeat76729 : Fragment im 1707775
    7606015 786432 (StateAtC 76729 256) (StateAtC 83400 0) :=
  loopC 76729 83397 255 29708 3072 (by decide) 2070472
    body76729 (reads_at 83397 _ rfl) (reads_at 83398 _ rfl) (reads_at 83399 _ rfl) rfl

private theorem body83400 (c : Word) : Fragment im 6 6 0
    (AtC (addr 83400) c) (AtC (addr 83406) c) := by
  have h83400 := lineWordC 83400 83406 6 0 c (by decide) (by decide) pc83400
  exact h83400

private theorem reset83406 : Fragment im 1 1 0 (StateAtC 83406 0)
    (StateAtC 83407 128) := by
  apply set_counterC 83406 0 128 (.ADDI .x20 .x0 128) (reads_at 83406 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body83407 (c : Word) : Fragment im 4 4 0
    (AtC (addr 83407) c) (AtC (addr 83411) c) := by
  have h83407 := lineWordC 83407 83411 4 0 c (by decide) (by decide) pc83407
  exact h83407

private theorem body83411 (c : Word) : Fragment im 6668 29708 3072
    (AtC (addr 83411) c) (AtC (addr 90079) c) := by
  have h83411 := lineWordC 83411 84179 3423 354 c (by decide) (by decide) pc83411
  have h84179 := lineWordC 84179 84947 3423 354 c (by decide) (by decide) pc84179
  have h84947 := lineWordC 84947 85715 3423 354 c (by decide) (by decide) pc84947
  have h85715 := lineWordC 85715 86483 3423 354 c (by decide) (by decide) pc85715
  have h86483 := lineWordC 86483 87251 3423 354 c (by decide) (by decide) pc86483
  have h87251 := lineWordC 87251 88019 3423 354 c (by decide) (by decide) pc87251
  have h88019 := lineWordC 88019 88787 3420 354 c (by decide) (by decide) pc88019
  have h88787 := lineWordC 88787 89555 3423 354 c (by decide) (by decide) pc88787
  have h89555 := lineWordC 89555 90079 2327 240 c (by decide) (by decide) pc89555
  exact (compose (compose (compose h83411 h84179) (compose h84947 h85715)) (compose (compose h86483 h87251) (compose h88019 (compose h88787 h89555))))

private theorem repeat83411 : Fragment im 853887
    3803007 393216 (StateAtC 83411 128) (StateAtC 90082 0) :=
  loopC 83411 90079 127 29708 3072 (by decide) 2070472
    body83411 (reads_at 90079 _ rfl) (reads_at 90080 _ rfl) (reads_at 90081 _ rfl) rfl

private theorem body90082 (c : Word) : Fragment im 6 6 0
    (AtC (addr 90082) c) (AtC (addr 90088) c) := by
  have h90082 := lineWordC 90082 90088 6 0 c (by decide) (by decide) pc90082
  exact h90082

private theorem reset90088 : Fragment im 1 1 0 (StateAtC 90088 0)
    (StateAtC 90089 64) := by
  apply set_counterC 90088 0 64 (.ADDI .x20 .x0 64) (reads_at 90088 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body90089 (c : Word) : Fragment im 4 4 0
    (AtC (addr 90089) c) (AtC (addr 90093) c) := by
  have h90089 := lineWordC 90089 90093 4 0 c (by decide) (by decide) pc90089
  exact h90089

private theorem body90093 (c : Word) : Fragment im 7180 33804 3584
    (AtC (addr 90093) c) (AtC (addr 97273) c) := by
  have h90093 := lineWordC 90093 90861 3625 385 c (by decide) (by decide) pc90093
  have h90861 := lineWordC 90861 91629 3614 383 c (by decide) (by decide) pc90861
  have h91629 := lineWordC 91629 92397 3600 381 c (by decide) (by decide) pc91629
  have h92397 := lineWordC 92397 93165 3621 384 c (by decide) (by decide) pc92397
  have h93165 := lineWordC 93165 93933 3625 385 c (by decide) (by decide) pc93165
  have h93933 := lineWordC 93933 94701 3614 383 c (by decide) (by decide) pc93933
  have h94701 := lineWordC 94701 95469 3614 383 c (by decide) (by decide) pc94701
  have h95469 := lineWordC 95469 96237 3607 382 c (by decide) (by decide) pc95469
  have h96237 := lineWordC 96237 97005 3628 385 c (by decide) (by decide) pc96237
  have h97005 := lineWordC 97005 97273 1256 133 c (by decide) (by decide) pc97005
  exact (compose (compose (compose h90093 h90861) (compose h91629 (compose h92397 h93165))) (compose (compose h93933 h94701) (compose h95469 (compose h96237 h97005))))

private theorem repeat90093 : Fragment im 459711
    2163647 229376 (StateAtC 90093 64) (StateAtC 97276 0) :=
  loopC 90093 97273 63 33804 3584 (by decide) 2068424
    body90093 (reads_at 97273 _ rfl) (reads_at 97274 _ rfl) (reads_at 97275 _ rfl) rfl

private theorem body97276 (c : Word) : Fragment im 6 6 0
    (AtC (addr 97276) c) (AtC (addr 97282) c) := by
  have h97276 := lineWordC 97276 97282 6 0 c (by decide) (by decide) pc97276
  exact h97276

private theorem reset97282 : Fragment im 1 1 0 (StateAtC 97282 0)
    (StateAtC 97283 32) := by
  apply set_counterC 97282 0 32 (.ADDI .x20 .x0 32) (reads_at 97282 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body97283 (c : Word) : Fragment im 4 4 0
    (AtC (addr 97283) c) (AtC (addr 97287) c) := by
  have h97283 := lineWordC 97283 97287 4 0 c (by decide) (by decide) pc97283
  exact h97283

private theorem body97287 (c : Word) : Fragment im 7692 37900 4096
    (AtC (addr 97287) c) (AtC (addr 104979) c) := by
  have h97287 := lineWordC 97287 98055 3777 408 c (by decide) (by decide) pc97287
  have h98055 := lineWordC 98055 98823 3784 409 c (by decide) (by decide) pc98055
  have h98823 := lineWordC 98823 99591 3784 409 c (by decide) (by decide) pc98823
  have h99591 := lineWordC 99591 100359 3791 410 c (by decide) (by decide) pc99591
  have h100359 := lineWordC 100359 101127 3798 411 c (by decide) (by decide) pc100359
  have h101127 := lineWordC 101127 101895 3784 409 c (by decide) (by decide) pc101127
  have h101895 := lineWordC 101895 102663 3780 408 c (by decide) (by decide) pc101895
  have h102663 := lineWordC 102663 103431 3777 408 c (by decide) (by decide) pc102663
  have h103431 := lineWordC 103431 104199 3777 408 c (by decide) (by decide) pc103431
  have h104199 := lineWordC 104199 104967 3784 409 c (by decide) (by decide) pc104199
  have h104967 := lineWordC 104967 104979 64 7 c (by decide) (by decide) pc104967
  exact (compose (compose (compose h97287 h98055) (compose h98823 (compose h99591 h100359))) (compose (compose h101127 (compose h101895 h102663)) (compose h103431 (compose h104199 h104967))))

private theorem repeat97287 : Fragment im 246239
    1212895 131072 (StateAtC 97287 32) (StateAtC 104982 0) :=
  loopC 97287 104979 31 37900 4096 (by decide) 2066376
    body97287 (reads_at 104979 _ rfl) (reads_at 104980 _ rfl) (reads_at 104981 _ rfl) rfl

private theorem body104982 (c : Word) : Fragment im 6 6 0
    (AtC (addr 104982) c) (AtC (addr 104988) c) := by
  have h104982 := lineWordC 104982 104988 6 0 c (by decide) (by decide) pc104982
  exact h104982

private theorem reset104988 : Fragment im 1 1 0 (StateAtC 104988 0)
    (StateAtC 104989 16) := by
  apply set_counterC 104988 0 16 (.ADDI .x20 .x0 16) (reads_at 104988 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body104989 (c : Word) : Fragment im 4 4 0
    (AtC (addr 104989) c) (AtC (addr 104993) c) := by
  have h104989 := lineWordC 104989 104993 4 0 c (by decide) (by decide) pc104989
  exact h104989

private theorem body104993 (c : Word) : Fragment im 7692 37900 4096
    (AtC (addr 104993) c) (AtC (addr 112685) c) := by
  have h104993 := lineWordC 104993 105761 3777 408 c (by decide) (by decide) pc104993
  have h105761 := lineWordC 105761 106529 3784 409 c (by decide) (by decide) pc105761
  have h106529 := lineWordC 106529 107297 3784 409 c (by decide) (by decide) pc106529
  have h107297 := lineWordC 107297 108065 3791 410 c (by decide) (by decide) pc107297
  have h108065 := lineWordC 108065 108833 3798 411 c (by decide) (by decide) pc108065
  have h108833 := lineWordC 108833 109601 3784 409 c (by decide) (by decide) pc108833
  have h109601 := lineWordC 109601 110369 3780 408 c (by decide) (by decide) pc109601
  have h110369 := lineWordC 110369 111137 3777 408 c (by decide) (by decide) pc110369
  have h111137 := lineWordC 111137 111905 3777 408 c (by decide) (by decide) pc111137
  have h111905 := lineWordC 111905 112673 3784 409 c (by decide) (by decide) pc111905
  have h112673 := lineWordC 112673 112685 64 7 c (by decide) (by decide) pc112673
  exact (compose (compose (compose h104993 h105761) (compose h106529 (compose h107297 h108065))) (compose (compose h108833 (compose h109601 h110369)) (compose h111137 (compose h111905 h112673))))

private theorem repeat104993 : Fragment im 123119
    606447 65536 (StateAtC 104993 16) (StateAtC 112688 0) :=
  loopC 104993 112685 15 37900 4096 (by decide) 2066376
    body104993 (reads_at 112685 _ rfl) (reads_at 112686 _ rfl) (reads_at 112687 _ rfl) rfl

private theorem body112688 (c : Word) : Fragment im 6 6 0
    (AtC (addr 112688) c) (AtC (addr 112694) c) := by
  have h112688 := lineWordC 112688 112694 6 0 c (by decide) (by decide) pc112688
  exact h112688

private theorem reset112694 : Fragment im 1 1 0 (StateAtC 112694 0)
    (StateAtC 112695 8) := by
  apply set_counterC 112694 0 8 (.ADDI .x20 .x0 8) (reads_at 112694 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body112695 (c : Word) : Fragment im 4 4 0
    (AtC (addr 112695) c) (AtC (addr 112699) c) := by
  have h112695 := lineWordC 112695 112699 4 0 c (by decide) (by decide) pc112695
  exact h112695

private theorem body112699 (c : Word) : Fragment im 8204 41996 4608
    (AtC (addr 112699) c) (AtC (addr 120903) c) := by
  have h112699 := lineWordC 112699 113467 3936 432 c (by decide) (by decide) pc112699
  have h113467 := lineWordC 113467 114235 3936 432 c (by decide) (by decide) pc113467
  have h114235 := lineWordC 114235 115003 3933 432 c (by decide) (by decide) pc114235
  have h115003 := lineWordC 115003 115771 3936 432 c (by decide) (by decide) pc115003
  have h115771 := lineWordC 115771 116539 3929 431 c (by decide) (by decide) pc115771
  have h116539 := lineWordC 116539 117307 3922 430 c (by decide) (by decide) pc116539
  have h117307 := lineWordC 117307 118075 3929 431 c (by decide) (by decide) pc117307
  have h118075 := lineWordC 118075 118843 3936 432 c (by decide) (by decide) pc118075
  have h118843 := lineWordC 118843 119611 3922 430 c (by decide) (by decide) pc118843
  have h119611 := lineWordC 119611 120379 3929 431 c (by decide) (by decide) pc119611
  have h120379 := lineWordC 120379 120903 2688 295 c (by decide) (by decide) pc120379
  exact (compose (compose (compose h112699 h113467) (compose h114235 (compose h115003 h115771))) (compose (compose h116539 (compose h117307 h118075)) (compose h118843 (compose h119611 h120379))))

private theorem repeat112699 : Fragment im 65655
    335991 36864 (StateAtC 112699 8) (StateAtC 120906 0) :=
  loopC 112699 120903 7 41996 4608 (by decide) 2064328
    body112699 (reads_at 120903 _ rfl) (reads_at 120904 _ rfl) (reads_at 120905 _ rfl) rfl

private theorem body120906 (c : Word) : Fragment im 6 6 0
    (AtC (addr 120906) c) (AtC (addr 120912) c) := by
  have h120906 := lineWordC 120906 120912 6 0 c (by decide) (by decide) pc120906
  exact h120906

private theorem reset120912 : Fragment im 1 1 0 (StateAtC 120912 0)
    (StateAtC 120913 4) := by
  apply set_counterC 120912 0 4 (.ADDI .x20 .x0 4) (reads_at 120912 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body120913 (c : Word) : Fragment im 4 4 0
    (AtC (addr 120913) c) (AtC (addr 120917) c) := by
  have h120913 := lineWordC 120913 120917 4 0 c (by decide) (by decide) pc120913
  exact h120913

private theorem body120917 (c : Word) : Fragment im 8204 41996 4608
    (AtC (addr 120917) c) (AtC (addr 129121) c) := by
  have h120917 := lineWordC 120917 121685 3936 432 c (by decide) (by decide) pc120917
  have h121685 := lineWordC 121685 122453 3936 432 c (by decide) (by decide) pc121685
  have h122453 := lineWordC 122453 123221 3933 432 c (by decide) (by decide) pc122453
  have h123221 := lineWordC 123221 123989 3936 432 c (by decide) (by decide) pc123221
  have h123989 := lineWordC 123989 124757 3929 431 c (by decide) (by decide) pc123989
  have h124757 := lineWordC 124757 125525 3922 430 c (by decide) (by decide) pc124757
  have h125525 := lineWordC 125525 126293 3929 431 c (by decide) (by decide) pc125525
  have h126293 := lineWordC 126293 127061 3936 432 c (by decide) (by decide) pc126293
  have h127061 := lineWordC 127061 127829 3922 430 c (by decide) (by decide) pc127061
  have h127829 := lineWordC 127829 128597 3929 431 c (by decide) (by decide) pc127829
  have h128597 := lineWordC 128597 129121 2688 295 c (by decide) (by decide) pc128597
  exact (compose (compose (compose h120917 h121685) (compose h122453 (compose h123221 h123989))) (compose (compose h124757 (compose h125525 h126293)) (compose h127061 (compose h127829 h128597))))

private theorem repeat120917 : Fragment im 32827
    167995 18432 (StateAtC 120917 4) (StateAtC 129124 0) :=
  loopC 120917 129121 3 41996 4608 (by decide) 2064328
    body120917 (reads_at 129121 _ rfl) (reads_at 129122 _ rfl) (reads_at 129123 _ rfl) rfl

private theorem body129124 (c : Word) : Fragment im 6 6 0
    (AtC (addr 129124) c) (AtC (addr 129130) c) := by
  have h129124 := lineWordC 129124 129130 6 0 c (by decide) (by decide) pc129124
  exact h129124

private theorem reset129130 : Fragment im 1 1 0 (StateAtC 129130 0)
    (StateAtC 129131 2) := by
  apply set_counterC 129130 0 2 (.ADDI .x20 .x0 2) (reads_at 129130 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body129131 (c : Word) : Fragment im 4 4 0
    (AtC (addr 129131) c) (AtC (addr 129135) c) := by
  have h129131 := lineWordC 129131 129135 4 0 c (by decide) (by decide) pc129131
  exact h129131

private theorem body129135 (c : Word) : Fragment im 8204 41996 4608
    (AtC (addr 129135) c) (AtC (addr 137339) c) := by
  have h129135 := lineWordC 129135 129903 3936 432 c (by decide) (by decide) pc129135
  have h129903 := lineWordC 129903 130671 3936 432 c (by decide) (by decide) pc129903
  have h130671 := lineWordC 130671 131439 3933 432 c (by decide) (by decide) pc130671
  have h131439 := lineWordC 131439 132207 3936 432 c (by decide) (by decide) pc131439
  have h132207 := lineWordC 132207 132975 3929 431 c (by decide) (by decide) pc132207
  have h132975 := lineWordC 132975 133743 3922 430 c (by decide) (by decide) pc132975
  have h133743 := lineWordC 133743 134511 3929 431 c (by decide) (by decide) pc133743
  have h134511 := lineWordC 134511 135279 3936 432 c (by decide) (by decide) pc134511
  have h135279 := lineWordC 135279 136047 3922 430 c (by decide) (by decide) pc135279
  have h136047 := lineWordC 136047 136815 3929 431 c (by decide) (by decide) pc136047
  have h136815 := lineWordC 136815 137339 2688 295 c (by decide) (by decide) pc136815
  exact (compose (compose (compose h129135 h129903) (compose h130671 (compose h131439 h132207))) (compose (compose h132975 (compose h133743 h134511)) (compose h135279 (compose h136047 h136815))))

private theorem repeat129135 : Fragment im 16413
    83997 9216 (StateAtC 129135 2) (StateAtC 137342 0) :=
  loopC 129135 137339 1 41996 4608 (by decide) 2064328
    body129135 (reads_at 137339 _ rfl) (reads_at 137340 _ rfl) (reads_at 137341 _ rfl) rfl

private theorem body137342 (c : Word) : Fragment im 6 6 0
    (AtC (addr 137342) c) (AtC (addr 137348) c) := by
  have h137342 := lineWordC 137342 137348 6 0 c (by decide) (by decide) pc137342
  exact h137342

private theorem reset137348 : Fragment im 1 1 0 (StateAtC 137348 0)
    (StateAtC 137349 1) := by
  apply set_counterC 137348 0 1 (.ADDI .x20 .x0 1) (reads_at 137348 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body137349 (c : Word) : Fragment im 7700 37908 4096
    (AtC (addr 137349) c) (AtC (addr 145049) c) := by
  have h137349 := lineWordC 137349 138117 3777 408 c (by decide) (by decide) pc137349
  have h138117 := lineWordC 138117 138885 3777 408 c (by decide) (by decide) pc138117
  have h138885 := lineWordC 138885 139653 3777 408 c (by decide) (by decide) pc138885
  have h139653 := lineWordC 139653 140421 3784 409 c (by decide) (by decide) pc139653
  have h140421 := lineWordC 140421 141189 3791 410 c (by decide) (by decide) pc140421
  have h141189 := lineWordC 141189 141957 3784 409 c (by decide) (by decide) pc141189
  have h141957 := lineWordC 141957 142725 3791 410 c (by decide) (by decide) pc141957
  have h142725 := lineWordC 142725 143493 3784 409 c (by decide) (by decide) pc142725
  have h143493 := lineWordC 143493 144261 3784 409 c (by decide) (by decide) pc143493
  have h144261 := lineWordC 144261 145029 3780 408 c (by decide) (by decide) pc144261
  have h145029 := lineWordC 145029 145049 79 8 c (by decide) (by decide) pc145029
  exact (compose (compose (compose h137349 h138117) (compose h138885 (compose h139653 h140421))) (compose (compose h141189 (compose h141957 h142725)) (compose h143493 (compose h144261 h145029))))

private theorem reset145049 : Fragment im 1 1 0 (StateAtC 145049 1)
    (StateAtC 145050 1) := by
  apply set_counterC 145049 1 1 (.ADDI .x20 .x0 1) (reads_at 145049 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body145050 (c : Word) : Fragment im 3854 18958 2048
    (AtC (addr 145050) c) (AtC (addr 148904) c) := by
  have h145050 := lineWordC 145050 145818 3777 408 c (by decide) (by decide) pc145050
  have h145818 := lineWordC 145818 146586 3777 408 c (by decide) (by decide) pc145818
  have h146586 := lineWordC 146586 147354 3777 408 c (by decide) (by decide) pc146586
  have h147354 := lineWordC 147354 148122 3784 409 c (by decide) (by decide) pc147354
  have h148122 := lineWordC 148122 148890 3791 410 c (by decide) (by decide) pc148122
  have h148890 := lineWordC 148890 148904 52 5 c (by decide) (by decide) pc148890
  exact (compose (compose h145050 (compose h145818 h146586)) (compose h147354 (compose h148122 h148890)))

private theorem reset148904 : Fragment im 1 1 0 (StateAtC 148904 1)
    (StateAtC 148905 1) := by
  apply set_counterC 148904 1 1 (.ADDI .x20 .x0 1) (reads_at 148904 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body148905 (c : Word) : Fragment im 650 1546 128
    (AtC (addr 148905) c) (AtC (addr 149555) c) := by
  have h148905 := lineWordC 148905 149555 1546 128 c (by decide) (by decide) pc148905
  exact h148905

private theorem reset149555 : Fragment im 1 1 0 (StateAtC 149555 1)
    (StateAtC 149556 1) := by
  apply set_counterC 149555 1 1 (.ADDI .x20 .x0 1) (reads_at 149555 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body149556 (c : Word) : Fragment im 264 712 64
    (AtC (addr 149556) c) (AtC (addr 149820) c) := by
  have h149556 := lineWordC 149556 149820 712 64 c (by decide) (by decide) pc149556
  exact h149556

private theorem reset149820 : Fragment im 1 1 0 (StateAtC 149820 1)
    (StateAtC 149821 1) := by
  apply set_counterC 149820 1 1 (.ADDI .x20 .x0 1) (reads_at 149820 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body149821 (c : Word) : Fragment im 136 360 32
    (AtC (addr 149821) c) (AtC (addr 149957) c) := by
  have h149821 := lineWordC 149821 149957 360 32 c (by decide) (by decide) pc149821
  exact h149821

private theorem reset149957 : Fragment im 1 1 0 (StateAtC 149957 1)
    (StateAtC 149958 1) := by
  apply set_counterC 149957 1 1 (.ADDI .x20 .x0 1) (reads_at 149957 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body149958 (c : Word) : Fragment im 72 184 16
    (AtC (addr 149958) c) (AtC (addr 150030) c) := by
  have h149958 := lineWordC 149958 150030 184 16 c (by decide) (by decide) pc149958
  exact h149958

private theorem reset150030 : Fragment im 1 1 0 (StateAtC 150030 1)
    (StateAtC 150031 1) := by
  apply set_counterC 150030 1 1 (.ADDI .x20 .x0 1) (reads_at 150030 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body150031 (c : Word) : Fragment im 40 96 8
    (AtC (addr 150031) c) (AtC (addr 150071) c) := by
  have h150031 := lineWordC 150031 150071 96 8 c (by decide) (by decide) pc150031
  exact h150031

private theorem reset150071 : Fragment im 1 1 0 (StateAtC 150071 1)
    (StateAtC 150072 1) := by
  apply set_counterC 150071 1 1 (.ADDI .x20 .x0 1) (reads_at 150071 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body150072 (c : Word) : Fragment im 24 52 4
    (AtC (addr 150072) c) (AtC (addr 150096) c) := by
  have h150072 := lineWordC 150072 150096 52 4 c (by decide) (by decide) pc150072
  exact h150072

private theorem reset150096 : Fragment im 1 1 0 (StateAtC 150096 1)
    (StateAtC 150097 1) := by
  apply set_counterC 150096 1 1 (.ADDI .x20 .x0 1) (reads_at 150096 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body150097 (c : Word) : Fragment im 16 30 2
    (AtC (addr 150097) c) (AtC (addr 150113) c) := by
  have h150097 := lineWordC 150097 150113 30 2 c (by decide) (by decide) pc150097
  exact h150097

private theorem reset150113 : Fragment im 1 1 0 (StateAtC 150113 1)
    (StateAtC 150114 1) := by
  apply set_counterC 150113 1 1 (.ADDI .x20 .x0 1) (reads_at 150113 _ rfl) _ rfl (fun _ => rfl)
  intro s hs
  refine ⟨rfl,congrArg (·+4) hs.1,hs.2.1,?_⟩
  rfl

private theorem body150114 (c : Word) : Fragment im 15 22 1
    (AtC (addr 150114) c) (AtC (addr 150129) c) := by
  have h150114 := lineWordC 150114 150129 22 1 c (by decide) (by decide) pc150114
  exact h150114

/-- Every supported execution from the public-call entry to the halt setup,
including executions stopped early by an invalid access. -/
theorem main_body : Fragment im 325149285 1489523294 56030463
    (StateAt 8 0) (StateAt 150129 1) := by
  exact weaken (compose (compose (compose (compose (compose (compose (body8 0) reset18) (compose repeat19 (compose (body53016 0) reset53024))) (compose (compose (body53025 16384) repeat53027) (compose (body56114 0) (compose reset56120 (body56121 8192))))) (compose (compose (compose repeat56123 (body59210 0)) (compose reset59216 (compose (body59217 4096) repeat59219))) (compose (compose (body62306 0) reset62312) (compose reset62313 (compose (body62314 2048) repeat62316))))) (compose (compose (compose (compose (body66427 0) reset66433) (compose (body66434 1024) (compose repeat66437 (body71060 0)))) (compose (compose reset71066 (body71067 512)) (compose repeat71071 (compose (body76718 0) reset76724)))) (compose (compose (compose (body76725 256) repeat76729) (compose (body83400 0) (compose reset83406 (body83407 128)))) (compose (compose repeat83411 (body90082 0)) (compose reset90088 (compose (body90089 64) repeat90093)))))) (compose (compose (compose (compose (compose (body97276 0) reset97282) (compose (body97283 32) (compose repeat97287 (body104982 0)))) (compose (compose reset104988 (body104989 16)) (compose repeat104993 (compose (body112688 0) reset112694)))) (compose (compose (compose (body112695 8) repeat112699) (compose (body120906 0) (compose reset120912 (body120913 4)))) (compose (compose repeat120917 (body129124 0)) (compose reset129130 (compose (body129131 2) repeat129135))))) (compose (compose (compose (compose (body137342 0) reset137348) (compose (body137349 1) (compose reset145049 (body145050 1)))) (compose (compose reset148904 (body148905 1)) (compose reset149555 (compose (body149556 1) reset149820)))) (compose (compose (compose (body149821 1) reset149957) (compose (body149958 1) (compose reset150030 (body150031 1)))) (compose (compose reset150071 (compose (body150072 1) reset150096)) (compose (body150097 1) (compose reset150113 (body150114 1)))))))) (fun _ h => h.1)

end CommitGolfCandidate.Reconstruction.CommitAssembly
