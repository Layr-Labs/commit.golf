import CommitGolfCandidate.QuadCommitWalk_node0
import CommitGolfCandidate.QuadCommitWalk_node1
import CommitGolfCandidate.QuadCommitWalk_node2
import CommitGolfCandidate.QuadCommitWalk_node3
import CommitGolfCandidate.QuadCommitWalk_node4
import CommitGolfCandidate.QuadCommitWalk_node5
import CommitGolfCandidate.QuadCommitWalk_node6
import CommitGolfCandidate.QuadCommitWalk_node7
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem walk_range_join (g : Nat → List (BitVec 32)) (i j k s m c : Nat)
    (first : walk 32 Artifact.commitCode g i (List.range' s m) = some j)
    (rest : walk 32 Artifact.commitCode g j (List.range' (s + m) c) = some k) :
    walk 32 Artifact.commitCode g i (List.range' s (m + c)) = some k := by
  rw [range'_split]; exact walk_append 32 _ g _ _ i j k first rest

private theorem prefixMatches_ofFn_aux {n : Nat} (p : CommitGolf.ArtifactEncoding.Packed n) :
    ∀ (m base : Nat) (h : base + m ≤ n),
      prefixMatches 32 p base (List.ofFn fun i : Fin m => p.get 32 ⟨base + i.val, by omega⟩) = true
  | 0, _, _ => rfl
  | m + 1, base, h => by
      rw [List.ofFn_succ]
      simp only [prefixMatches, show base < n by omega, dite_true, beq_self_eq_true, Bool.true_and, Nat.add_zero]
      have h' := prefixMatches_ofFn_aux p m (base + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1] using h'

private theorem walk_ofFn {n : Nat} (p : CommitGolf.ArtifactEncoding.Packed n)
    (base m : Nat) (h : base + m ≤ n) :
    walk 32 p id base [List.ofFn fun i : Fin m => p.get 32 ⟨base + i.val, by omega⟩] = some (base + m) := by
  simp only [walk, id, prefixMatches_ofFn_aux p m base h, if_true, List.length_ofFn]
theorem n1s_from_29184 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 132778 (List.range' 29184 246) = some 133516 :=
  n1s_block_29184
theorem n1s_from_28672 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 131242 (List.range' 28672 758) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 131242 132778 133516 28672 512 246 n1s_block_28672 n1s_from_29184
theorem n1s_from_28160 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 129706 (List.range' 28160 1270) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 129706 131242 133516 28160 512 758 n1s_block_28160 n1s_from_28672
theorem n1s_from_27648 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 128170 (List.range' 27648 1782) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 128170 129706 133516 27648 512 1270 n1s_block_27648 n1s_from_28160
theorem n1s_from_27136 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 126634 (List.range' 27136 2294) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 126634 128170 133516 27136 512 1782 n1s_block_27136 n1s_from_27648
theorem n1s_from_26624 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 125098 (List.range' 26624 2806) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 125098 126634 133516 26624 512 2294 n1s_block_26624 n1s_from_27136
theorem n1s_from_26112 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 123562 (List.range' 26112 3318) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 123562 125098 133516 26112 512 2806 n1s_block_26112 n1s_from_26624
theorem n1s_from_25600 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 122026 (List.range' 25600 3830) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 122026 123562 133516 25600 512 3318 n1s_block_25600 n1s_from_26112
theorem n1s_from_25088 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 120490 (List.range' 25088 4342) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 120490 122026 133516 25088 512 3830 n1s_block_25088 n1s_from_25600
theorem n1s_from_24576 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 118954 (List.range' 24576 4854) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 118954 120490 133516 24576 512 4342 n1s_block_24576 n1s_from_25088
theorem n1s_from_24064 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 117418 (List.range' 24064 5366) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 117418 118954 133516 24064 512 4854 n1s_block_24064 n1s_from_24576
theorem n1s_from_23552 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 115882 (List.range' 23552 5878) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 115882 117418 133516 23552 512 5366 n1s_block_23552 n1s_from_24064
theorem n1s_from_23040 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 114346 (List.range' 23040 6390) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 114346 115882 133516 23040 512 5878 n1s_block_23040 n1s_from_23552
theorem n1s_from_22528 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 112810 (List.range' 22528 6902) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 112810 114346 133516 22528 512 6390 n1s_block_22528 n1s_from_23040
theorem n1s_from_22016 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 111274 (List.range' 22016 7414) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 111274 112810 133516 22016 512 6902 n1s_block_22016 n1s_from_22528
theorem n1s_from_21504 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 109738 (List.range' 21504 7926) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 109738 111274 133516 21504 512 7414 n1s_block_21504 n1s_from_22016
theorem n1s_from_20992 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 108202 (List.range' 20992 8438) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 108202 109738 133516 20992 512 7926 n1s_block_20992 n1s_from_21504
theorem n1s_from_20480 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 106666 (List.range' 20480 8950) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 106666 108202 133516 20480 512 8438 n1s_block_20480 n1s_from_20992
theorem n1s_from_19968 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 105130 (List.range' 19968 9462) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 105130 106666 133516 19968 512 8950 n1s_block_19968 n1s_from_20480
theorem n1s_from_19456 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 103594 (List.range' 19456 9974) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 103594 105130 133516 19456 512 9462 n1s_block_19456 n1s_from_19968
theorem n1s_from_18944 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 102058 (List.range' 18944 10486) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 102058 103594 133516 18944 512 9974 n1s_block_18944 n1s_from_19456
theorem n1s_from_18432 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 100522 (List.range' 18432 10998) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 100522 102058 133516 18432 512 10486 n1s_block_18432 n1s_from_18944
theorem n1s_from_17920 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 98986 (List.range' 17920 11510) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 98986 100522 133516 17920 512 10998 n1s_block_17920 n1s_from_18432
theorem n1s_from_17408 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 97450 (List.range' 17408 12022) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 97450 98986 133516 17408 512 11510 n1s_block_17408 n1s_from_17920
theorem n1s_from_16896 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 95914 (List.range' 16896 12534) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 95914 97450 133516 16896 512 12022 n1s_block_16896 n1s_from_17408
theorem n1s_from_16384 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 94378 (List.range' 16384 13046) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 94378 95914 133516 16384 512 12534 n1s_block_16384 n1s_from_16896
theorem n1s_from_15872 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 92842 (List.range' 15872 13558) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 92842 94378 133516 15872 512 13046 n1s_block_15872 n1s_from_16384
theorem n1s_from_15360 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 91306 (List.range' 15360 14070) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 91306 92842 133516 15360 512 13558 n1s_block_15360 n1s_from_15872
theorem n1s_from_14848 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 89770 (List.range' 14848 14582) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 89770 91306 133516 14848 512 14070 n1s_block_14848 n1s_from_15360
theorem n1s_from_14336 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 88234 (List.range' 14336 15094) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 88234 89770 133516 14336 512 14582 n1s_block_14336 n1s_from_14848
theorem n1s_from_13824 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 86698 (List.range' 13824 15606) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 86698 88234 133516 13824 512 15094 n1s_block_13824 n1s_from_14336
theorem n1s_from_13312 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 85162 (List.range' 13312 16118) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 85162 86698 133516 13312 512 15606 n1s_block_13312 n1s_from_13824
theorem n1s_from_12800 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 83626 (List.range' 12800 16630) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 83626 85162 133516 12800 512 16118 n1s_block_12800 n1s_from_13312
theorem n1s_from_12288 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 82090 (List.range' 12288 17142) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 82090 83626 133516 12288 512 16630 n1s_block_12288 n1s_from_12800
theorem n1s_from_11776 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 80554 (List.range' 11776 17654) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 80554 82090 133516 11776 512 17142 n1s_block_11776 n1s_from_12288
theorem n1s_from_11264 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 79018 (List.range' 11264 18166) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 79018 80554 133516 11264 512 17654 n1s_block_11264 n1s_from_11776
theorem n1s_from_10752 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 77482 (List.range' 10752 18678) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 77482 79018 133516 10752 512 18166 n1s_block_10752 n1s_from_11264
theorem n1s_from_10240 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 75946 (List.range' 10240 19190) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 75946 77482 133516 10240 512 18678 n1s_block_10240 n1s_from_10752
theorem n1s_from_9728 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 74410 (List.range' 9728 19702) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 74410 75946 133516 9728 512 19190 n1s_block_9728 n1s_from_10240
theorem n1s_from_9216 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 72874 (List.range' 9216 20214) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 72874 74410 133516 9216 512 19702 n1s_block_9216 n1s_from_9728
theorem n1s_from_8704 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 71338 (List.range' 8704 20726) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 71338 72874 133516 8704 512 20214 n1s_block_8704 n1s_from_9216
theorem n1s_from_8192 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 69802 (List.range' 8192 21238) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 69802 71338 133516 8192 512 20726 n1s_block_8192 n1s_from_8704
theorem n1s_from_7680 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 68266 (List.range' 7680 21750) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 68266 69802 133516 7680 512 21238 n1s_block_7680 n1s_from_8192
theorem n1s_from_7168 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 66730 (List.range' 7168 22262) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 66730 68266 133516 7168 512 21750 n1s_block_7168 n1s_from_7680
theorem n1s_from_6656 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 65194 (List.range' 6656 22774) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 65194 66730 133516 6656 512 22262 n1s_block_6656 n1s_from_7168
theorem n1s_from_6144 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 63658 (List.range' 6144 23286) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 63658 65194 133516 6144 512 22774 n1s_block_6144 n1s_from_6656
theorem n1s_from_5632 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 62122 (List.range' 5632 23798) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 62122 63658 133516 5632 512 23286 n1s_block_5632 n1s_from_6144
theorem n1s_from_5120 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 60586 (List.range' 5120 24310) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 60586 62122 133516 5120 512 23798 n1s_block_5120 n1s_from_5632
theorem n1s_from_4608 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 59050 (List.range' 4608 24822) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 59050 60586 133516 4608 512 24310 n1s_block_4608 n1s_from_5120
theorem n1s_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 57514 (List.range' 4096 25334) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 57514 59050 133516 4096 512 24822 n1s_block_4096 n1s_from_4608
theorem n1s_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 55978 (List.range' 3584 25846) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 55978 57514 133516 3584 512 25334 n1s_block_3584 n1s_from_4096
theorem n1s_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 54442 (List.range' 3072 26358) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 54442 55978 133516 3072 512 25846 n1s_block_3072 n1s_from_3584
theorem n1s_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 52906 (List.range' 2560 26870) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 52906 54442 133516 2560 512 26358 n1s_block_2560 n1s_from_3072
theorem n1s_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 51370 (List.range' 2048 27382) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 51370 52906 133516 2048 512 26870 n1s_block_2048 n1s_from_2560
theorem n1s_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 49834 (List.range' 1536 27894) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 49834 51370 133516 1536 512 27382 n1s_block_1536 n1s_from_2048
theorem n1s_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 48298 (List.range' 1024 28406) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 48298 49834 133516 1024 512 27894 n1s_block_1024 n1s_from_1536
theorem n1s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 46762 (List.range' 512 28918) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 46762 48298 133516 512 512 28406 n1s_block_512 n1s_from_1024
theorem n1s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 45226 (List.range' 0 29430) = some 133516 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 45226 46762 133516 0 512 28918 n1s_block_0 n1s_from_512
theorem n1r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 133518 (List.range' 0 424) = some 134790 :=
  n1r_block_0
theorem n2s_from_14336 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 177811 (List.range' 14336 249) = some 178558 :=
  n2s_block_14336
theorem n2s_from_13824 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 176275 (List.range' 13824 761) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 176275 177811 178558 13824 512 249 n2s_block_13824 n2s_from_14336
theorem n2s_from_13312 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 174739 (List.range' 13312 1273) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 174739 176275 178558 13312 512 761 n2s_block_13312 n2s_from_13824
theorem n2s_from_12800 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 173203 (List.range' 12800 1785) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 173203 174739 178558 12800 512 1273 n2s_block_12800 n2s_from_13312
theorem n2s_from_12288 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 171667 (List.range' 12288 2297) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 171667 173203 178558 12288 512 1785 n2s_block_12288 n2s_from_12800
theorem n2s_from_11776 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 170131 (List.range' 11776 2809) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 170131 171667 178558 11776 512 2297 n2s_block_11776 n2s_from_12288
theorem n2s_from_11264 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 168595 (List.range' 11264 3321) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 168595 170131 178558 11264 512 2809 n2s_block_11264 n2s_from_11776
theorem n2s_from_10752 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 167059 (List.range' 10752 3833) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 167059 168595 178558 10752 512 3321 n2s_block_10752 n2s_from_11264
theorem n2s_from_10240 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 165523 (List.range' 10240 4345) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 165523 167059 178558 10240 512 3833 n2s_block_10240 n2s_from_10752
theorem n2s_from_9728 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 163987 (List.range' 9728 4857) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 163987 165523 178558 9728 512 4345 n2s_block_9728 n2s_from_10240
theorem n2s_from_9216 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 162451 (List.range' 9216 5369) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 162451 163987 178558 9216 512 4857 n2s_block_9216 n2s_from_9728
theorem n2s_from_8704 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 160915 (List.range' 8704 5881) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 160915 162451 178558 8704 512 5369 n2s_block_8704 n2s_from_9216
theorem n2s_from_8192 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 159379 (List.range' 8192 6393) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 159379 160915 178558 8192 512 5881 n2s_block_8192 n2s_from_8704
theorem n2s_from_7680 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 157843 (List.range' 7680 6905) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 157843 159379 178558 7680 512 6393 n2s_block_7680 n2s_from_8192
theorem n2s_from_7168 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 156307 (List.range' 7168 7417) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 156307 157843 178558 7168 512 6905 n2s_block_7168 n2s_from_7680
theorem n2s_from_6656 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 154771 (List.range' 6656 7929) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 154771 156307 178558 6656 512 7417 n2s_block_6656 n2s_from_7168
theorem n2s_from_6144 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 153235 (List.range' 6144 8441) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 153235 154771 178558 6144 512 7929 n2s_block_6144 n2s_from_6656
theorem n2s_from_5632 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 151699 (List.range' 5632 8953) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 151699 153235 178558 5632 512 8441 n2s_block_5632 n2s_from_6144
theorem n2s_from_5120 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 150163 (List.range' 5120 9465) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 150163 151699 178558 5120 512 8953 n2s_block_5120 n2s_from_5632
theorem n2s_from_4608 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 148627 (List.range' 4608 9977) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 148627 150163 178558 4608 512 9465 n2s_block_4608 n2s_from_5120
theorem n2s_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 147091 (List.range' 4096 10489) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 147091 148627 178558 4096 512 9977 n2s_block_4096 n2s_from_4608
theorem n2s_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 145555 (List.range' 3584 11001) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 145555 147091 178558 3584 512 10489 n2s_block_3584 n2s_from_4096
theorem n2s_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 144019 (List.range' 3072 11513) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 144019 145555 178558 3072 512 11001 n2s_block_3072 n2s_from_3584
theorem n2s_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 142483 (List.range' 2560 12025) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 142483 144019 178558 2560 512 11513 n2s_block_2560 n2s_from_3072
theorem n2s_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 140947 (List.range' 2048 12537) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 140947 142483 178558 2048 512 12025 n2s_block_2048 n2s_from_2560
theorem n2s_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 139411 (List.range' 1536 13049) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 139411 140947 178558 1536 512 12537 n2s_block_1536 n2s_from_2048
theorem n2s_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 137875 (List.range' 1024 13561) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 137875 139411 178558 1024 512 13049 n2s_block_1024 n2s_from_1536
theorem n2s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 136339 (List.range' 512 14073) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 136339 137875 178558 512 512 13561 n2s_block_512 n2s_from_1024
theorem n2s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 134803 (List.range' 0 14585) = some 178558 :=
  walk_range_join (fun p => nodeWordsR 5 (p % 5)) 134803 136339 178558 0 512 14073 n2s_block_0 n2s_from_512
theorem n2r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 178560 (List.range' 0 179) = some 179097 :=
  n2r_block_0
theorem n3s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 180646 (List.range' 512 488) = some 182110 :=
  n3s_block_512
theorem n3s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 179110 (List.range' 0 1000) = some 182110 :=
  walk_range_join (fun p => nodeWordsR 4 (p % 4)) 179110 180646 182110 0 512 488 n3s_block_0 n3s_from_512
theorem n3r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 4 (p % 4)) 182112 (List.range' 0 218) = some 182766 :=
  n3r_block_0
theorem n4s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 184319 (List.range' 512 488) = some 185783 :=
  n4s_block_512
theorem n4s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 182783 (List.range' 0 1000) = some 185783 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 182783 184319 185783 0 512 488 n4s_block_0 n4s_from_512
theorem n4r_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 187321 (List.range' 512 43) = some 187450 :=
  n4r_block_512
theorem n4r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 185785 (List.range' 0 555) = some 187450 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 185785 187321 187450 0 512 43 n4r_block_0 n4r_from_512
theorem n5s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 188999 (List.range' 512 488) = some 190463 :=
  n5s_block_512
theorem n5s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 187463 (List.range' 0 1000) = some 190463 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 187463 188999 190463 0 512 488 n5s_block_0 n5s_from_512
theorem n5r_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192001 (List.range' 512 266) = some 192799 :=
  n5r_block_512
theorem n5r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 190465 (List.range' 0 778) = some 192799 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 190465 192001 192799 0 512 266 n5r_block_0 n5r_from_512
theorem n6s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 194344 (List.range' 512 488) = some 195808 :=
  n6s_block_512
theorem n6s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 192808 (List.range' 0 1000) = some 195808 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 192808 194344 195808 0 512 488 n6s_block_0 n6s_from_512
theorem n6r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 195810 (List.range' 0 389) = some 196977 :=
  n6r_block_0
theorem n7s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 198526 (List.range' 512 488) = some 199990 :=
  n7s_block_512
theorem n7s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 196990 (List.range' 0 1000) = some 199990 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 196990 198526 199990 0 512 488 n7s_block_0 n7s_from_512
theorem n7r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 199992 (List.range' 0 195) = some 200577 :=
  n7r_block_0
theorem n8s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 202126 (List.range' 512 488) = some 203590 :=
  n8s_block_512
theorem n8s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 200590 (List.range' 0 1000) = some 203590 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 200590 202126 203590 0 512 488 n8s_block_0 n8s_from_512
theorem n8r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203592 (List.range' 0 98) = some 203886 :=
  n8r_block_0
theorem n9r_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 206967 (List.range' 1024 25) = some 207042 :=
  n9r_block_1024
theorem n9r_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 205431 (List.range' 512 537) = some 207042 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 205431 206967 207042 512 512 25 n9r_block_512 n9r_from_1024
theorem n9r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 203895 (List.range' 0 1049) = some 207042 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 203895 205431 207042 0 512 537 n9r_block_0 n9r_from_512
theorem n10r_from_512 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 208591 (List.range' 512 13) = some 208630 :=
  n10r_block_512
theorem n10r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 207055 (List.range' 0 525) = some 208630 :=
  walk_range_join (fun p => nodeWordsR 2 (p % 2)) 207055 208591 208630 0 512 13 n10r_block_0 n10r_from_512
theorem n11r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 2 (p % 2)) 208643 (List.range' 0 263) = some 209432 :=
  n11r_block_0
theorem n12r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 209445 (List.range' 0 132) = some 209841 :=
  n12r_block_0
theorem n13r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 209862 (List.range' 0 27) = some 209943 :=
  n13r_block_0
theorem n14r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 209964 (List.range' 0 6) = some 209982 :=
  n14r_block_0
theorem n15r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWordsR 5 (p % 5)) 210007 (List.range' 0 2) = some 210013 :=
  n15r_block_0
theorem seg_0 : walk 32 Artifact.commitCode id 0 [setupWords] = some 19 := by
  simpa only [setupWords, Nat.zero_add] using walk_ofFn Artifact.commitCode 0 19 (by omega)
theorem seg_1 : walk 32 Artifact.commitCode id 19 [leafCode] = some 45183 := by
  simpa only [leafCode] using walk_ofFn Artifact.commitCode 19 45164 (by omega)
theorem seg_2 : walk 32 Artifact.commitCode id 45183 [leafLatchWords] = some 45201 := by
  simpa only [leafLatchWords] using walk_ofFn Artifact.commitCode 45183 18 (by omega)
theorem seg_3 : walk 32 Artifact.commitCode id 45201 [leafZeroWords] = some 45217 := by decide +kernel
theorem seg_4 : walk 32 Artifact.commitCode id 45217 [levelSetupWords 1] = some 45226 := by decide +kernel
theorem seg_5 : walk 32 Artifact.commitCode id 45226 [nodeCodeR 5 (levelS 1)] = some 133516 := by
  rw [show nodeCodeR 5 (levelS 1) = (List.range' 0 29430).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelS 1 = 29430 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 45226 133516 n1s_from_0
theorem seg_6 : walk 32 Artifact.commitCode id 133516 [levelLatchWords 1] = some 133518 := by decide +kernel
theorem seg_7 : walk 32 Artifact.commitCode id 133518 [nodeCodeR 5 (levelR 1)] = some 134790 := by
  rw [show nodeCodeR 5 (levelR 1) = (List.range' 0 424).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelR 1 = 424 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 133518 134790 n1r_from_0
theorem seg_8 : walk 32 Artifact.commitCode id 134790 [levelZeroWords 1] = some 134794 := by decide +kernel
theorem seg_9 : walk 32 Artifact.commitCode id 134794 [levelSetupWords 2] = some 134803 := by decide +kernel
theorem seg_10 : walk 32 Artifact.commitCode id 134803 [nodeCodeR 5 (levelS 2)] = some 178558 := by
  rw [show nodeCodeR 5 (levelS 2) = (List.range' 0 14585).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelS 2 = 14585 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 134803 178558 n2s_from_0
theorem seg_11 : walk 32 Artifact.commitCode id 178558 [levelLatchWords 2] = some 178560 := by decide +kernel
theorem seg_12 : walk 32 Artifact.commitCode id 178560 [nodeCodeR 5 (levelR 2)] = some 179097 := by
  rw [show nodeCodeR 5 (levelR 2) = (List.range' 0 179).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelR 2 = 179 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 178560 179097 n2r_from_0
theorem seg_13 : walk 32 Artifact.commitCode id 179097 [levelZeroWords 2] = some 179101 := by decide +kernel
theorem seg_14 : walk 32 Artifact.commitCode id 179101 [levelSetupWords 3] = some 179110 := by decide +kernel
theorem seg_15 : walk 32 Artifact.commitCode id 179110 [nodeCodeR 4 (levelS 3)] = some 182110 := by
  rw [show nodeCodeR 4 (levelS 3) = (List.range' 0 1000).flatMap (fun p => nodeWordsR 4 (p % 4)) by
    rw [show levelS 3 = 1000 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 179110 182110 n3s_from_0
theorem seg_16 : walk 32 Artifact.commitCode id 182110 [levelLatchWords 3] = some 182112 := by decide +kernel
theorem seg_17 : walk 32 Artifact.commitCode id 182112 [nodeCodeR 4 (levelR 3)] = some 182766 := by
  rw [show nodeCodeR 4 (levelR 3) = (List.range' 0 218).flatMap (fun p => nodeWordsR 4 (p % 4)) by
    rw [show levelR 3 = 218 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 182112 182766 n3r_from_0
theorem seg_18 : walk 32 Artifact.commitCode id 182766 [levelZeroWords 3] = some 182774 := by decide +kernel
theorem seg_19 : walk 32 Artifact.commitCode id 182774 [levelSetupWords 4] = some 182783 := by decide +kernel
theorem seg_20 : walk 32 Artifact.commitCode id 182783 [nodeCodeR 2 (levelS 4)] = some 185783 := by
  rw [show nodeCodeR 2 (levelS 4) = (List.range' 0 1000).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelS 4 = 1000 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 182783 185783 n4s_from_0
theorem seg_21 : walk 32 Artifact.commitCode id 185783 [levelLatchWords 4] = some 185785 := by decide +kernel
theorem seg_22 : walk 32 Artifact.commitCode id 185785 [nodeCodeR 2 (levelR 4)] = some 187450 := by
  rw [show nodeCodeR 2 (levelR 4) = (List.range' 0 555).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 4 = 555 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 185785 187450 n4r_from_0
theorem seg_23 : walk 32 Artifact.commitCode id 187450 [levelZeroWords 4] = some 187454 := by decide +kernel
theorem seg_24 : walk 32 Artifact.commitCode id 187454 [levelSetupWords 5] = some 187463 := by decide +kernel
theorem seg_25 : walk 32 Artifact.commitCode id 187463 [nodeCodeR 2 (levelS 5)] = some 190463 := by
  rw [show nodeCodeR 2 (levelS 5) = (List.range' 0 1000).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelS 5 = 1000 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 187463 190463 n5s_from_0
theorem seg_26 : walk 32 Artifact.commitCode id 190463 [levelLatchWords 5] = some 190465 := by decide +kernel
theorem seg_27 : walk 32 Artifact.commitCode id 190465 [nodeCodeR 2 (levelR 5)] = some 192799 := by
  rw [show nodeCodeR 2 (levelR 5) = (List.range' 0 778).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 5 = 778 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 190465 192799 n5r_from_0
theorem seg_28 : walk 32 Artifact.commitCode id 192799 [levelZeroWords 5] = some 192799 := by decide +kernel
theorem seg_29 : walk 32 Artifact.commitCode id 192799 [levelSetupWords 6] = some 192808 := by decide +kernel
theorem seg_30 : walk 32 Artifact.commitCode id 192808 [nodeCodeR 2 (levelS 6)] = some 195808 := by
  rw [show nodeCodeR 2 (levelS 6) = (List.range' 0 1000).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelS 6 = 1000 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 192808 195808 n6s_from_0
theorem seg_31 : walk 32 Artifact.commitCode id 195808 [levelLatchWords 6] = some 195810 := by decide +kernel
theorem seg_32 : walk 32 Artifact.commitCode id 195810 [nodeCodeR 2 (levelR 6)] = some 196977 := by
  rw [show nodeCodeR 2 (levelR 6) = (List.range' 0 389).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 6 = 389 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 195810 196977 n6r_from_0
theorem seg_33 : walk 32 Artifact.commitCode id 196977 [levelZeroWords 6] = some 196981 := by decide +kernel
theorem seg_34 : walk 32 Artifact.commitCode id 196981 [levelSetupWords 7] = some 196990 := by decide +kernel
theorem seg_35 : walk 32 Artifact.commitCode id 196990 [nodeCodeR 2 (levelS 7)] = some 199990 := by
  rw [show nodeCodeR 2 (levelS 7) = (List.range' 0 1000).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelS 7 = 1000 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 196990 199990 n7s_from_0
theorem seg_36 : walk 32 Artifact.commitCode id 199990 [levelLatchWords 7] = some 199992 := by decide +kernel
theorem seg_37 : walk 32 Artifact.commitCode id 199992 [nodeCodeR 2 (levelR 7)] = some 200577 := by
  rw [show nodeCodeR 2 (levelR 7) = (List.range' 0 195).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 7 = 195 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 199992 200577 n7r_from_0
theorem seg_38 : walk 32 Artifact.commitCode id 200577 [levelZeroWords 7] = some 200581 := by decide +kernel
theorem seg_39 : walk 32 Artifact.commitCode id 200581 [levelSetupWords 8] = some 200590 := by decide +kernel
theorem seg_40 : walk 32 Artifact.commitCode id 200590 [nodeCodeR 2 (levelS 8)] = some 203590 := by
  rw [show nodeCodeR 2 (levelS 8) = (List.range' 0 1000).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelS 8 = 1000 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 200590 203590 n8s_from_0
theorem seg_41 : walk 32 Artifact.commitCode id 203590 [levelLatchWords 8] = some 203592 := by decide +kernel
theorem seg_42 : walk 32 Artifact.commitCode id 203592 [nodeCodeR 2 (levelR 8)] = some 203886 := by
  rw [show nodeCodeR 2 (levelR 8) = (List.range' 0 98).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 8 = 98 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 203592 203886 n8r_from_0
theorem seg_43 : walk 32 Artifact.commitCode id 203886 [levelZeroWords 8] = some 203886 := by decide +kernel
theorem seg_44 : walk 32 Artifact.commitCode id 203886 [levelSetupWords 9] = some 203895 := by decide +kernel
theorem seg_45 : walk 32 Artifact.commitCode id 203895 [nodeCodeR 2 (levelR 9)] = some 207042 := by
  rw [show nodeCodeR 2 (levelR 9) = (List.range' 0 1049).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 9 = 1049 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 203895 207042 n9r_from_0
theorem seg_46 : walk 32 Artifact.commitCode id 207042 [levelZeroWords 9] = some 207046 := by decide +kernel
theorem seg_47 : walk 32 Artifact.commitCode id 207046 [levelSetupWords 10] = some 207055 := by decide +kernel
theorem seg_48 : walk 32 Artifact.commitCode id 207055 [nodeCodeR 2 (levelR 10)] = some 208630 := by
  rw [show nodeCodeR 2 (levelR 10) = (List.range' 0 525).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 10 = 525 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 207055 208630 n10r_from_0
theorem seg_49 : walk 32 Artifact.commitCode id 208630 [levelZeroWords 10] = some 208634 := by decide +kernel
theorem seg_50 : walk 32 Artifact.commitCode id 208634 [levelSetupWords 11] = some 208643 := by decide +kernel
theorem seg_51 : walk 32 Artifact.commitCode id 208643 [nodeCodeR 2 (levelR 11)] = some 209432 := by
  rw [show nodeCodeR 2 (levelR 11) = (List.range' 0 263).flatMap (fun p => nodeWordsR 2 (p % 2)) by
    rw [show levelR 11 = 263 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 208643 209432 n11r_from_0
theorem seg_52 : walk 32 Artifact.commitCode id 209432 [levelZeroWords 11] = some 209436 := by decide +kernel
theorem seg_53 : walk 32 Artifact.commitCode id 209436 [levelSetupWords 12] = some 209445 := by decide +kernel
theorem seg_54 : walk 32 Artifact.commitCode id 209445 [nodeCodeR 5 (levelR 12)] = some 209841 := by
  rw [show nodeCodeR 5 (levelR 12) = (List.range' 0 132).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelR 12 = 132 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 209445 209841 n12r_from_0
theorem seg_55 : walk 32 Artifact.commitCode id 209841 [levelZeroWords 12] = some 209853 := by decide +kernel
theorem seg_56 : walk 32 Artifact.commitCode id 209853 [levelSetupWords 13] = some 209862 := by decide +kernel
theorem seg_57 : walk 32 Artifact.commitCode id 209862 [nodeCodeR 5 (levelR 13)] = some 209943 := by
  rw [show nodeCodeR 5 (levelR 13) = (List.range' 0 27).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelR 13 = 27 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 209862 209943 n13r_from_0
theorem seg_58 : walk 32 Artifact.commitCode id 209943 [levelZeroWords 13] = some 209955 := by decide +kernel
theorem seg_59 : walk 32 Artifact.commitCode id 209955 [levelSetupWords 14] = some 209964 := by decide +kernel
theorem seg_60 : walk 32 Artifact.commitCode id 209964 [nodeCodeR 5 (levelR 14)] = some 209982 := by
  rw [show nodeCodeR 5 (levelR 14) = (List.range' 0 6).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelR 14 = 6 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 209964 209982 n14r_from_0
theorem seg_61 : walk 32 Artifact.commitCode id 209982 [levelZeroWords 14] = some 209998 := by decide +kernel
theorem seg_62 : walk 32 Artifact.commitCode id 209998 [levelSetupWords 15] = some 210007 := by decide +kernel
theorem seg_63 : walk 32 Artifact.commitCode id 210007 [nodeCodeR 5 (levelR 15)] = some 210013 := by
  rw [show nodeCodeR 5 (levelR 15) = (List.range' 0 2).flatMap (fun p => nodeWordsR 5 (p % 5)) by
    rw [show levelR 15 = 2 from rfl, nodeCodeR, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 210007 210013 n15r_from_0
theorem seg_64 : walk 32 Artifact.commitCode id 210013 [levelZeroWords 15] = some 210025 := by decide +kernel
theorem seg_65 : walk 32 Artifact.commitCode id 210025 [rootSetupWords] = some 210030 := by decide +kernel
theorem seg_66 : walk 32 Artifact.commitCode id 210030 [rootWords] = some 210913 := by decide +kernel
theorem tail_66 : walk 32 Artifact.commitCode id 210030 [rootWords] = some 210913 := seg_66
theorem tail_65 : walk 32 Artifact.commitCode id 210025 ([rootSetupWords] ++ ([rootWords])) = some 210913 :=
  walk_append 32 _ id _ _ 210025 210030 210913 seg_65 tail_66
theorem tail_64 : walk 32 Artifact.commitCode id 210013 ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))) = some 210913 :=
  walk_append 32 _ id _ _ 210013 210025 210913 seg_64 tail_65
theorem tail_63 : walk 32 Artifact.commitCode id 210007 ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))) = some 210913 :=
  walk_append 32 _ id _ _ 210007 210013 210913 seg_63 tail_64
theorem tail_62 : walk 32 Artifact.commitCode id 209998 ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))) = some 210913 :=
  walk_append 32 _ id _ _ 209998 210007 210913 seg_62 tail_63
theorem tail_61 : walk 32 Artifact.commitCode id 209982 ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))) = some 210913 :=
  walk_append 32 _ id _ _ 209982 209998 210913 seg_61 tail_62
theorem tail_60 : walk 32 Artifact.commitCode id 209964 ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209964 209982 210913 seg_60 tail_61
theorem tail_59 : walk 32 Artifact.commitCode id 209955 ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209955 209964 210913 seg_59 tail_60
theorem tail_58 : walk 32 Artifact.commitCode id 209943 ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209943 209955 210913 seg_58 tail_59
theorem tail_57 : walk 32 Artifact.commitCode id 209862 ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209862 209943 210913 seg_57 tail_58
theorem tail_56 : walk 32 Artifact.commitCode id 209853 ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209853 209862 210913 seg_56 tail_57
theorem tail_55 : walk 32 Artifact.commitCode id 209841 ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209841 209853 210913 seg_55 tail_56
theorem tail_54 : walk 32 Artifact.commitCode id 209445 ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209445 209841 210913 seg_54 tail_55
theorem tail_53 : walk 32 Artifact.commitCode id 209436 ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209436 209445 210913 seg_53 tail_54
theorem tail_52 : walk 32 Artifact.commitCode id 209432 ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 209432 209436 210913 seg_52 tail_53
theorem tail_51 : walk 32 Artifact.commitCode id 208643 ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 208643 209432 210913 seg_51 tail_52
theorem tail_50 : walk 32 Artifact.commitCode id 208634 ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 208634 208643 210913 seg_50 tail_51
theorem tail_49 : walk 32 Artifact.commitCode id 208630 ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 208630 208634 210913 seg_49 tail_50
theorem tail_48 : walk 32 Artifact.commitCode id 207055 ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 207055 208630 210913 seg_48 tail_49
theorem tail_47 : walk 32 Artifact.commitCode id 207046 ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 207046 207055 210913 seg_47 tail_48
theorem tail_46 : walk 32 Artifact.commitCode id 207042 ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 207042 207046 210913 seg_46 tail_47
theorem tail_45 : walk 32 Artifact.commitCode id 203895 ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 203895 207042 210913 seg_45 tail_46
theorem tail_44 : walk 32 Artifact.commitCode id 203886 ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 203886 203895 210913 seg_44 tail_45
theorem tail_43 : walk 32 Artifact.commitCode id 203886 ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 203886 203886 210913 seg_43 tail_44
theorem tail_42 : walk 32 Artifact.commitCode id 203592 ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 203592 203886 210913 seg_42 tail_43
theorem tail_41 : walk 32 Artifact.commitCode id 203590 ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 203590 203592 210913 seg_41 tail_42
theorem tail_40 : walk 32 Artifact.commitCode id 200590 ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 200590 203590 210913 seg_40 tail_41
theorem tail_39 : walk 32 Artifact.commitCode id 200581 ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 200581 200590 210913 seg_39 tail_40
theorem tail_38 : walk 32 Artifact.commitCode id 200577 ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 200577 200581 210913 seg_38 tail_39
theorem tail_37 : walk 32 Artifact.commitCode id 199992 ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 199992 200577 210913 seg_37 tail_38
theorem tail_36 : walk 32 Artifact.commitCode id 199990 ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 199990 199992 210913 seg_36 tail_37
theorem tail_35 : walk 32 Artifact.commitCode id 196990 ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 196990 199990 210913 seg_35 tail_36
theorem tail_34 : walk 32 Artifact.commitCode id 196981 ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 196981 196990 210913 seg_34 tail_35
theorem tail_33 : walk 32 Artifact.commitCode id 196977 ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 196977 196981 210913 seg_33 tail_34
theorem tail_32 : walk 32 Artifact.commitCode id 195810 ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 195810 196977 210913 seg_32 tail_33
theorem tail_31 : walk 32 Artifact.commitCode id 195808 ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 195808 195810 210913 seg_31 tail_32
theorem tail_30 : walk 32 Artifact.commitCode id 192808 ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 192808 195808 210913 seg_30 tail_31
theorem tail_29 : walk 32 Artifact.commitCode id 192799 ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 192799 192808 210913 seg_29 tail_30
theorem tail_28 : walk 32 Artifact.commitCode id 192799 ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 192799 192799 210913 seg_28 tail_29
theorem tail_27 : walk 32 Artifact.commitCode id 190465 ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 190465 192799 210913 seg_27 tail_28
theorem tail_26 : walk 32 Artifact.commitCode id 190463 ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 190463 190465 210913 seg_26 tail_27
theorem tail_25 : walk 32 Artifact.commitCode id 187463 ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 187463 190463 210913 seg_25 tail_26
theorem tail_24 : walk 32 Artifact.commitCode id 187454 ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 187454 187463 210913 seg_24 tail_25
theorem tail_23 : walk 32 Artifact.commitCode id 187450 ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 187450 187454 210913 seg_23 tail_24
theorem tail_22 : walk 32 Artifact.commitCode id 185785 ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 185785 187450 210913 seg_22 tail_23
theorem tail_21 : walk 32 Artifact.commitCode id 185783 ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 185783 185785 210913 seg_21 tail_22
theorem tail_20 : walk 32 Artifact.commitCode id 182783 ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 182783 185783 210913 seg_20 tail_21
theorem tail_19 : walk 32 Artifact.commitCode id 182774 ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 182774 182783 210913 seg_19 tail_20
theorem tail_18 : walk 32 Artifact.commitCode id 182766 ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 182766 182774 210913 seg_18 tail_19
theorem tail_17 : walk 32 Artifact.commitCode id 182112 ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 182112 182766 210913 seg_17 tail_18
theorem tail_16 : walk 32 Artifact.commitCode id 182110 ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 182110 182112 210913 seg_16 tail_17
theorem tail_15 : walk 32 Artifact.commitCode id 179110 ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 179110 182110 210913 seg_15 tail_16
theorem tail_14 : walk 32 Artifact.commitCode id 179101 ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 179101 179110 210913 seg_14 tail_15
theorem tail_13 : walk 32 Artifact.commitCode id 179097 ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 179097 179101 210913 seg_13 tail_14
theorem tail_12 : walk 32 Artifact.commitCode id 178560 ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 178560 179097 210913 seg_12 tail_13
theorem tail_11 : walk 32 Artifact.commitCode id 178558 ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 178558 178560 210913 seg_11 tail_12
theorem tail_10 : walk 32 Artifact.commitCode id 134803 ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 134803 178558 210913 seg_10 tail_11
theorem tail_9 : walk 32 Artifact.commitCode id 134794 ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 134794 134803 210913 seg_9 tail_10
theorem tail_8 : walk 32 Artifact.commitCode id 134790 ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 134790 134794 210913 seg_8 tail_9
theorem tail_7 : walk 32 Artifact.commitCode id 133518 ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 133518 134790 210913 seg_7 tail_8
theorem tail_6 : walk 32 Artifact.commitCode id 133516 ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 133516 133518 210913 seg_6 tail_7
theorem tail_5 : walk 32 Artifact.commitCode id 45226 ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 45226 133516 210913 seg_5 tail_6
theorem tail_4 : walk 32 Artifact.commitCode id 45217 ([levelSetupWords 1] ++ ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 45217 45226 210913 seg_4 tail_5
theorem tail_3 : walk 32 Artifact.commitCode id 45201 ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 45201 45217 210913 seg_3 tail_4
theorem tail_2 : walk 32 Artifact.commitCode id 45183 ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 45183 45201 210913 seg_2 tail_3
theorem tail_1 : walk 32 Artifact.commitCode id 19 ([leafCode] ++ ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 19 45183 210913 seg_1 tail_2
theorem tail_0 : walk 32 Artifact.commitCode id 0 ([setupWords] ++ ([leafCode] ++ ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = some 210913 :=
  walk_append 32 _ id _ _ 0 19 210913 seg_0 tail_1
theorem level_code_1 : levelCode 1 = levelSetupWords 1 ++ (nodeCodeR 5 (levelS 1) ++
    (levelLatchWords 1 ++ (nodeCodeR 5 (levelR 1) ++ levelZeroWords 1))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 1 = 5 from rfl]
theorem level_code_2 : levelCode 2 = levelSetupWords 2 ++ (nodeCodeR 5 (levelS 2) ++
    (levelLatchWords 2 ++ (nodeCodeR 5 (levelR 2) ++ levelZeroWords 2))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 2 = 5 from rfl]
theorem level_code_3 : levelCode 3 = levelSetupWords 3 ++ (nodeCodeR 4 (levelS 3) ++
    (levelLatchWords 3 ++ (nodeCodeR 4 (levelR 3) ++ levelZeroWords 3))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 3 = 4 from rfl]
theorem level_code_4 : levelCode 4 = levelSetupWords 4 ++ (nodeCodeR 2 (levelS 4) ++
    (levelLatchWords 4 ++ (nodeCodeR 2 (levelR 4) ++ levelZeroWords 4))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 4 = 2 from rfl]
theorem level_code_5 : levelCode 5 = levelSetupWords 5 ++ (nodeCodeR 2 (levelS 5) ++
    (levelLatchWords 5 ++ (nodeCodeR 2 (levelR 5) ++ levelZeroWords 5))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 5 = 2 from rfl]
theorem level_code_6 : levelCode 6 = levelSetupWords 6 ++ (nodeCodeR 2 (levelS 6) ++
    (levelLatchWords 6 ++ (nodeCodeR 2 (levelR 6) ++ levelZeroWords 6))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 6 = 2 from rfl]
theorem level_code_7 : levelCode 7 = levelSetupWords 7 ++ (nodeCodeR 2 (levelS 7) ++
    (levelLatchWords 7 ++ (nodeCodeR 2 (levelR 7) ++ levelZeroWords 7))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 7 = 2 from rfl]
theorem level_code_8 : levelCode 8 = levelSetupWords 8 ++ (nodeCodeR 2 (levelS 8) ++
    (levelLatchWords 8 ++ (nodeCodeR 2 (levelR 8) ++ levelZeroWords 8))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc, show levelRadix 8 = 2 from rfl]
theorem level_code_9 : levelCode 9 = levelSetupWords 9 ++ (nodeCodeR 2 (levelR 9) ++ levelZeroWords 9) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 9 = 2 from rfl]
theorem level_code_10 : levelCode 10 = levelSetupWords 10 ++ (nodeCodeR 2 (levelR 10) ++ levelZeroWords 10) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 10 = 2 from rfl]
theorem level_code_11 : levelCode 11 = levelSetupWords 11 ++ (nodeCodeR 2 (levelR 11) ++ levelZeroWords 11) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 11 = 2 from rfl]
theorem level_code_12 : levelCode 12 = levelSetupWords 12 ++ (nodeCodeR 5 (levelR 12) ++ levelZeroWords 12) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 12 = 5 from rfl]
theorem level_code_13 : levelCode 13 = levelSetupWords 13 ++ (nodeCodeR 5 (levelR 13) ++ levelZeroWords 13) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 13 = 5 from rfl]
theorem level_code_14 : levelCode 14 = levelSetupWords 14 ++ (nodeCodeR 5 (levelR 14) ++ levelZeroWords 14) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 14 = 5 from rfl]
theorem level_code_15 : levelCode 15 = levelSetupWords 15 ++ (nodeCodeR 5 (levelR 15) ++ levelZeroWords 15) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc, show levelRadix 15 = 5 from rfl]

theorem commit_code_matches : matchesFrom 32 Artifact.commitCode 0 image.code = true := by
  obtain ⟨ok, len⟩ := walk_sound 32 _ id _ 0 210913 tail_0
  have code : image.code = (([setupWords] ++ ([leafCode] ++ ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCodeR 5 (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCodeR 5 (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCodeR 5 (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCodeR 5 (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCodeR 4 (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCodeR 4 (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCodeR 2 (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCodeR 2 (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCodeR 2 (levelS 5)] ++ ([levelLatchWords 5] ++ ([nodeCodeR 2 (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCodeR 2 (levelS 6)] ++ ([levelLatchWords 6] ++ ([nodeCodeR 2 (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCodeR 2 (levelS 7)] ++ ([levelLatchWords 7] ++ ([nodeCodeR 2 (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCodeR 2 (levelS 8)] ++ ([levelLatchWords 8] ++ ([nodeCodeR 2 (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCodeR 2 (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCodeR 2 (levelR 10)] ++ ([levelZeroWords 10] ++ ([levelSetupWords 11] ++ ([nodeCodeR 2 (levelR 11)] ++ ([levelZeroWords 11] ++ ([levelSetupWords 12] ++ ([nodeCodeR 5 (levelR 12)] ++ ([levelZeroWords 12] ++ ([levelSetupWords 13] ++ ([nodeCodeR 5 (levelR 13)] ++ ([levelZeroWords 13] ++ ([levelSetupWords 14] ++ ([nodeCodeR 5 (levelR 14)] ++ ([levelZeroWords 14] ++ ([levelSetupWords 15] ++ ([nodeCodeR 5 (levelR 15)] ++ ([levelZeroWords 15] ++ ([rootSetupWords] ++ ([rootWords]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).flatMap id) := by
    simp only [image, levelsCode, level_code_1, level_code_2, level_code_3, level_code_4, level_code_5, level_code_6, level_code_7, level_code_8, level_code_9, level_code_10, level_code_11, level_code_12, level_code_13, level_code_14, level_code_15,
      List.append_assoc, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, id, List.append_nil]
  rw [code]
  exact matches_of_prefix 32 _ _ 0 ok len

theorem quad_commit_image : Artifact.submission.image .commit = image := by
  simp only [Artifact.submission]
  rw [decode_of_matches 32 _ _ commit_code_matches]
  rfl

end TwoPermutationPrototype.ArtifactMatchB
