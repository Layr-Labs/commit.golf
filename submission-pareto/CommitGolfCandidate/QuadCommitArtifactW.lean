import CommitGolfCandidate.QuadCommitWalk_leaf0
import CommitGolfCandidate.QuadCommitWalk_leaf1
import CommitGolfCandidate.QuadCommitWalk_leaf2
import CommitGolfCandidate.QuadCommitWalk_leaf3
import CommitGolfCandidate.QuadCommitWalk_quad0
import CommitGolfCandidate.QuadCommitWalk_quad1
import CommitGolfCandidate.QuadCommitWalk_quad2
import CommitGolfCandidate.QuadCommitWalk_quad3
import CommitGolfCandidate.QuadCommitWalk_qtwo0
import CommitGolfCandidate.QuadCommitWalk_qtwo1
import CommitGolfCandidate.QuadCommitWalk_qtwo2
import CommitGolfCandidate.QuadCommitWalk_qtwo3
import CommitGolfCandidate.QuadCommitWalk_qthree0
import CommitGolfCandidate.QuadCommitWalk_qthree1
import CommitGolfCandidate.QuadCommitWalk_qthree2
import CommitGolfCandidate.QuadCommitWalk_qthree3
import CommitGolfCandidate.QuadCommitWalk_parent0
import CommitGolfCandidate.QuadCommitWalk_parent1
import CommitGolfCandidate.QuadCommitWalk_parent2
import CommitGolfCandidate.QuadCommitWalk_parent3
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem walk_range_join (g : Nat → List (BitVec 32)) (i j k s m c : Nat)
    (first : walk 32 Artifact.commitCode g i (List.range' s m) = some j)
    (rest : walk 32 Artifact.commitCode g j (List.range' (s + m) c) = some k) :
    walk 32 Artifact.commitCode g i (List.range' s (m + c)) = some k := by
  rw [range'_split]; exact walk_append 32 _ g _ _ i j k first rest

theorem leaf_from_3968 : walk 32 Artifact.commitCode leafWords 43788 (List.range' 3968 128) = some 45201 :=
  leaf_block_3968
theorem leaf_from_3840 : walk 32 Artifact.commitCode leafWords 42376 (List.range' 3840 256) = some 45201 :=
  walk_range_join leafWords 42376 43788 45201 3840 128 128 leaf_block_3840 leaf_from_3968
theorem leaf_from_3712 : walk 32 Artifact.commitCode leafWords 40964 (List.range' 3712 384) = some 45201 :=
  walk_range_join leafWords 40964 42376 45201 3712 128 256 leaf_block_3712 leaf_from_3840
theorem leaf_from_3584 : walk 32 Artifact.commitCode leafWords 39552 (List.range' 3584 512) = some 45201 :=
  walk_range_join leafWords 39552 40964 45201 3584 128 384 leaf_block_3584 leaf_from_3712
theorem leaf_from_3456 : walk 32 Artifact.commitCode leafWords 38140 (List.range' 3456 640) = some 45201 :=
  walk_range_join leafWords 38140 39552 45201 3456 128 512 leaf_block_3456 leaf_from_3584
theorem leaf_from_3328 : walk 32 Artifact.commitCode leafWords 36728 (List.range' 3328 768) = some 45201 :=
  walk_range_join leafWords 36728 38140 45201 3328 128 640 leaf_block_3328 leaf_from_3456
theorem leaf_from_3200 : walk 32 Artifact.commitCode leafWords 35316 (List.range' 3200 896) = some 45201 :=
  walk_range_join leafWords 35316 36728 45201 3200 128 768 leaf_block_3200 leaf_from_3328
theorem leaf_from_3072 : walk 32 Artifact.commitCode leafWords 33904 (List.range' 3072 1024) = some 45201 :=
  walk_range_join leafWords 33904 35316 45201 3072 128 896 leaf_block_3072 leaf_from_3200
theorem leaf_from_2944 : walk 32 Artifact.commitCode leafWords 32492 (List.range' 2944 1152) = some 45201 :=
  walk_range_join leafWords 32492 33904 45201 2944 128 1024 leaf_block_2944 leaf_from_3072
theorem leaf_from_2816 : walk 32 Artifact.commitCode leafWords 31081 (List.range' 2816 1280) = some 45201 :=
  walk_range_join leafWords 31081 32492 45201 2816 128 1152 leaf_block_2816 leaf_from_2944
theorem leaf_from_2688 : walk 32 Artifact.commitCode leafWords 29669 (List.range' 2688 1408) = some 45201 :=
  walk_range_join leafWords 29669 31081 45201 2688 128 1280 leaf_block_2688 leaf_from_2816
theorem leaf_from_2560 : walk 32 Artifact.commitCode leafWords 28257 (List.range' 2560 1536) = some 45201 :=
  walk_range_join leafWords 28257 29669 45201 2560 128 1408 leaf_block_2560 leaf_from_2688
theorem leaf_from_2432 : walk 32 Artifact.commitCode leafWords 26845 (List.range' 2432 1664) = some 45201 :=
  walk_range_join leafWords 26845 28257 45201 2432 128 1536 leaf_block_2432 leaf_from_2560
theorem leaf_from_2304 : walk 32 Artifact.commitCode leafWords 25433 (List.range' 2304 1792) = some 45201 :=
  walk_range_join leafWords 25433 26845 45201 2304 128 1664 leaf_block_2304 leaf_from_2432
theorem leaf_from_2176 : walk 32 Artifact.commitCode leafWords 24021 (List.range' 2176 1920) = some 45201 :=
  walk_range_join leafWords 24021 25433 45201 2176 128 1792 leaf_block_2176 leaf_from_2304
theorem leaf_from_2048 : walk 32 Artifact.commitCode leafWords 22609 (List.range' 2048 2048) = some 45201 :=
  walk_range_join leafWords 22609 24021 45201 2048 128 1920 leaf_block_2048 leaf_from_2176
theorem leaf_from_1920 : walk 32 Artifact.commitCode leafWords 21197 (List.range' 1920 2176) = some 45201 :=
  walk_range_join leafWords 21197 22609 45201 1920 128 2048 leaf_block_1920 leaf_from_2048
theorem leaf_from_1792 : walk 32 Artifact.commitCode leafWords 19785 (List.range' 1792 2304) = some 45201 :=
  walk_range_join leafWords 19785 21197 45201 1792 128 2176 leaf_block_1792 leaf_from_1920
theorem leaf_from_1664 : walk 32 Artifact.commitCode leafWords 18373 (List.range' 1664 2432) = some 45201 :=
  walk_range_join leafWords 18373 19785 45201 1664 128 2304 leaf_block_1664 leaf_from_1792
theorem leaf_from_1536 : walk 32 Artifact.commitCode leafWords 16961 (List.range' 1536 2560) = some 45201 :=
  walk_range_join leafWords 16961 18373 45201 1536 128 2432 leaf_block_1536 leaf_from_1664
theorem leaf_from_1408 : walk 32 Artifact.commitCode leafWords 15550 (List.range' 1408 2688) = some 45201 :=
  walk_range_join leafWords 15550 16961 45201 1408 128 2560 leaf_block_1408 leaf_from_1536
theorem leaf_from_1280 : walk 32 Artifact.commitCode leafWords 14138 (List.range' 1280 2816) = some 45201 :=
  walk_range_join leafWords 14138 15550 45201 1280 128 2688 leaf_block_1280 leaf_from_1408
theorem leaf_from_1152 : walk 32 Artifact.commitCode leafWords 12726 (List.range' 1152 2944) = some 45201 :=
  walk_range_join leafWords 12726 14138 45201 1152 128 2816 leaf_block_1152 leaf_from_1280
theorem leaf_from_1024 : walk 32 Artifact.commitCode leafWords 11314 (List.range' 1024 3072) = some 45201 :=
  walk_range_join leafWords 11314 12726 45201 1024 128 2944 leaf_block_1024 leaf_from_1152
theorem leaf_from_896 : walk 32 Artifact.commitCode leafWords 9902 (List.range' 896 3200) = some 45201 :=
  walk_range_join leafWords 9902 11314 45201 896 128 3072 leaf_block_896 leaf_from_1024
theorem leaf_from_768 : walk 32 Artifact.commitCode leafWords 8490 (List.range' 768 3328) = some 45201 :=
  walk_range_join leafWords 8490 9902 45201 768 128 3200 leaf_block_768 leaf_from_896
theorem leaf_from_640 : walk 32 Artifact.commitCode leafWords 7078 (List.range' 640 3456) = some 45201 :=
  walk_range_join leafWords 7078 8490 45201 640 128 3328 leaf_block_640 leaf_from_768
theorem leaf_from_512 : walk 32 Artifact.commitCode leafWords 5666 (List.range' 512 3584) = some 45201 :=
  walk_range_join leafWords 5666 7078 45201 512 128 3456 leaf_block_512 leaf_from_640
theorem leaf_from_384 : walk 32 Artifact.commitCode leafWords 4254 (List.range' 384 3712) = some 45201 :=
  walk_range_join leafWords 4254 5666 45201 384 128 3584 leaf_block_384 leaf_from_512
theorem leaf_from_256 : walk 32 Artifact.commitCode leafWords 2842 (List.range' 256 3840) = some 45201 :=
  walk_range_join leafWords 2842 4254 45201 256 128 3712 leaf_block_256 leaf_from_384
theorem leaf_from_128 : walk 32 Artifact.commitCode leafWords 1430 (List.range' 128 3968) = some 45201 :=
  walk_range_join leafWords 1430 2842 45201 128 128 3840 leaf_block_128 leaf_from_256
theorem leaf_from_0 : walk 32 Artifact.commitCode leafWords 19 (List.range' 0 4096) = some 45201 :=
  walk_range_join leafWords 19 1430 45201 0 128 3968 leaf_block_0 leaf_from_128
theorem quad_from_3968 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 92828 (List.range' 3968 128) = some 94364 :=
  quad_block_3968
theorem quad_from_3840 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 91292 (List.range' 3840 256) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 91292 92828 94364 3840 128 128 quad_block_3840 quad_from_3968
theorem quad_from_3712 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 89756 (List.range' 3712 384) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 89756 91292 94364 3712 128 256 quad_block_3712 quad_from_3840
theorem quad_from_3584 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 88220 (List.range' 3584 512) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 88220 89756 94364 3584 128 384 quad_block_3584 quad_from_3712
theorem quad_from_3456 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 86684 (List.range' 3456 640) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 86684 88220 94364 3456 128 512 quad_block_3456 quad_from_3584
theorem quad_from_3328 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 85148 (List.range' 3328 768) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 85148 86684 94364 3328 128 640 quad_block_3328 quad_from_3456
theorem quad_from_3200 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 83612 (List.range' 3200 896) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 83612 85148 94364 3200 128 768 quad_block_3200 quad_from_3328
theorem quad_from_3072 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 82076 (List.range' 3072 1024) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 82076 83612 94364 3072 128 896 quad_block_3072 quad_from_3200
theorem quad_from_2944 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 80540 (List.range' 2944 1152) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 80540 82076 94364 2944 128 1024 quad_block_2944 quad_from_3072
theorem quad_from_2816 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 79004 (List.range' 2816 1280) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 79004 80540 94364 2816 128 1152 quad_block_2816 quad_from_2944
theorem quad_from_2688 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 77468 (List.range' 2688 1408) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 77468 79004 94364 2688 128 1280 quad_block_2688 quad_from_2816
theorem quad_from_2560 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 75932 (List.range' 2560 1536) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 75932 77468 94364 2560 128 1408 quad_block_2560 quad_from_2688
theorem quad_from_2432 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 74396 (List.range' 2432 1664) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 74396 75932 94364 2432 128 1536 quad_block_2432 quad_from_2560
theorem quad_from_2304 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 72860 (List.range' 2304 1792) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 72860 74396 94364 2304 128 1664 quad_block_2304 quad_from_2432
theorem quad_from_2176 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 71324 (List.range' 2176 1920) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 71324 72860 94364 2176 128 1792 quad_block_2176 quad_from_2304
theorem quad_from_2048 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 69788 (List.range' 2048 2048) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 69788 71324 94364 2048 128 1920 quad_block_2048 quad_from_2176
theorem quad_from_1920 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 68252 (List.range' 1920 2176) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 68252 69788 94364 1920 128 2048 quad_block_1920 quad_from_2048
theorem quad_from_1792 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 66716 (List.range' 1792 2304) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 66716 68252 94364 1792 128 2176 quad_block_1792 quad_from_1920
theorem quad_from_1664 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 65180 (List.range' 1664 2432) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 65180 66716 94364 1664 128 2304 quad_block_1664 quad_from_1792
theorem quad_from_1536 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 63644 (List.range' 1536 2560) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 63644 65180 94364 1536 128 2432 quad_block_1536 quad_from_1664
theorem quad_from_1408 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 62108 (List.range' 1408 2688) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 62108 63644 94364 1408 128 2560 quad_block_1408 quad_from_1536
theorem quad_from_1280 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 60572 (List.range' 1280 2816) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 60572 62108 94364 1280 128 2688 quad_block_1280 quad_from_1408
theorem quad_from_1152 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 59036 (List.range' 1152 2944) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 59036 60572 94364 1152 128 2816 quad_block_1152 quad_from_1280
theorem quad_from_1024 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 57500 (List.range' 1024 3072) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 57500 59036 94364 1024 128 2944 quad_block_1024 quad_from_1152
theorem quad_from_896 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 55964 (List.range' 896 3200) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 55964 57500 94364 896 128 3072 quad_block_896 quad_from_1024
theorem quad_from_768 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 54428 (List.range' 768 3328) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 54428 55964 94364 768 128 3200 quad_block_768 quad_from_896
theorem quad_from_640 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 52892 (List.range' 640 3456) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 52892 54428 94364 640 128 3328 quad_block_640 quad_from_768
theorem quad_from_512 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 51356 (List.range' 512 3584) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 51356 52892 94364 512 128 3456 quad_block_512 quad_from_640
theorem quad_from_384 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 49820 (List.range' 384 3712) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 49820 51356 94364 384 128 3584 quad_block_384 quad_from_512
theorem quad_from_256 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 48284 (List.range' 256 3840) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 48284 49820 94364 256 128 3712 quad_block_256 quad_from_384
theorem quad_from_128 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 46748 (List.range' 128 3968) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 46748 48284 94364 128 128 3840 quad_block_128 quad_from_256
theorem quad_from_0 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 45212 (List.range' 0 4096) = some 94364 :=
  walk_range_join (fun _ => quadGroupWords) 45212 46748 94364 0 128 3968 quad_block_0 quad_from_128
theorem qtwo_from_3968 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 141991 (List.range' 3968 128) = some 143527 :=
  qtwo_block_3968
theorem qtwo_from_3840 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 140455 (List.range' 3840 256) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 140455 141991 143527 3840 128 128 qtwo_block_3840 qtwo_from_3968
theorem qtwo_from_3712 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 138919 (List.range' 3712 384) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 138919 140455 143527 3712 128 256 qtwo_block_3712 qtwo_from_3840
theorem qtwo_from_3584 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 137383 (List.range' 3584 512) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 137383 138919 143527 3584 128 384 qtwo_block_3584 qtwo_from_3712
theorem qtwo_from_3456 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 135847 (List.range' 3456 640) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 135847 137383 143527 3456 128 512 qtwo_block_3456 qtwo_from_3584
theorem qtwo_from_3328 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 134311 (List.range' 3328 768) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 134311 135847 143527 3328 128 640 qtwo_block_3328 qtwo_from_3456
theorem qtwo_from_3200 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 132775 (List.range' 3200 896) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 132775 134311 143527 3200 128 768 qtwo_block_3200 qtwo_from_3328
theorem qtwo_from_3072 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 131239 (List.range' 3072 1024) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 131239 132775 143527 3072 128 896 qtwo_block_3072 qtwo_from_3200
theorem qtwo_from_2944 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 129703 (List.range' 2944 1152) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 129703 131239 143527 2944 128 1024 qtwo_block_2944 qtwo_from_3072
theorem qtwo_from_2816 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 128167 (List.range' 2816 1280) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 128167 129703 143527 2816 128 1152 qtwo_block_2816 qtwo_from_2944
theorem qtwo_from_2688 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 126631 (List.range' 2688 1408) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 126631 128167 143527 2688 128 1280 qtwo_block_2688 qtwo_from_2816
theorem qtwo_from_2560 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 125095 (List.range' 2560 1536) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 125095 126631 143527 2560 128 1408 qtwo_block_2560 qtwo_from_2688
theorem qtwo_from_2432 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 123559 (List.range' 2432 1664) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 123559 125095 143527 2432 128 1536 qtwo_block_2432 qtwo_from_2560
theorem qtwo_from_2304 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 122023 (List.range' 2304 1792) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 122023 123559 143527 2304 128 1664 qtwo_block_2304 qtwo_from_2432
theorem qtwo_from_2176 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 120487 (List.range' 2176 1920) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 120487 122023 143527 2176 128 1792 qtwo_block_2176 qtwo_from_2304
theorem qtwo_from_2048 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 118951 (List.range' 2048 2048) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 118951 120487 143527 2048 128 1920 qtwo_block_2048 qtwo_from_2176
theorem qtwo_from_1920 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 117415 (List.range' 1920 2176) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 117415 118951 143527 1920 128 2048 qtwo_block_1920 qtwo_from_2048
theorem qtwo_from_1792 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 115879 (List.range' 1792 2304) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 115879 117415 143527 1792 128 2176 qtwo_block_1792 qtwo_from_1920
theorem qtwo_from_1664 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 114343 (List.range' 1664 2432) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 114343 115879 143527 1664 128 2304 qtwo_block_1664 qtwo_from_1792
theorem qtwo_from_1536 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 112807 (List.range' 1536 2560) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 112807 114343 143527 1536 128 2432 qtwo_block_1536 qtwo_from_1664
theorem qtwo_from_1408 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 111271 (List.range' 1408 2688) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 111271 112807 143527 1408 128 2560 qtwo_block_1408 qtwo_from_1536
theorem qtwo_from_1280 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 109735 (List.range' 1280 2816) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 109735 111271 143527 1280 128 2688 qtwo_block_1280 qtwo_from_1408
theorem qtwo_from_1152 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 108199 (List.range' 1152 2944) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 108199 109735 143527 1152 128 2816 qtwo_block_1152 qtwo_from_1280
theorem qtwo_from_1024 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 106663 (List.range' 1024 3072) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 106663 108199 143527 1024 128 2944 qtwo_block_1024 qtwo_from_1152
theorem qtwo_from_896 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 105127 (List.range' 896 3200) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 105127 106663 143527 896 128 3072 qtwo_block_896 qtwo_from_1024
theorem qtwo_from_768 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 103591 (List.range' 768 3328) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 103591 105127 143527 768 128 3200 qtwo_block_768 qtwo_from_896
theorem qtwo_from_640 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 102055 (List.range' 640 3456) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 102055 103591 143527 640 128 3328 qtwo_block_640 qtwo_from_768
theorem qtwo_from_512 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 100519 (List.range' 512 3584) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 100519 102055 143527 512 128 3456 qtwo_block_512 qtwo_from_640
theorem qtwo_from_384 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 98983 (List.range' 384 3712) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 98983 100519 143527 384 128 3584 qtwo_block_384 qtwo_from_512
theorem qtwo_from_256 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 97447 (List.range' 256 3840) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 97447 98983 143527 256 128 3712 qtwo_block_256 qtwo_from_384
theorem qtwo_from_128 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 95911 (List.range' 128 3968) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 95911 97447 143527 128 128 3840 qtwo_block_128 qtwo_from_256
theorem qtwo_from_0 : walk 32 Artifact.commitCode (fun _ => quadGroupWords) 94375 (List.range' 0 4096) = some 143527 :=
  walk_range_join (fun _ => quadGroupWords) 94375 95911 143527 0 128 3968 qtwo_block_0 qtwo_from_128
theorem qthree_from_15872 : walk 32 Artifact.commitCode (fun _ => quadWords) 191154 (List.range' 15872 512) = some 192690 :=
  qthree_block_15872
theorem qthree_from_15360 : walk 32 Artifact.commitCode (fun _ => quadWords) 189618 (List.range' 15360 1024) = some 192690 :=
  walk_range_join (fun _ => quadWords) 189618 191154 192690 15360 512 512 qthree_block_15360 qthree_from_15872
theorem qthree_from_14848 : walk 32 Artifact.commitCode (fun _ => quadWords) 188082 (List.range' 14848 1536) = some 192690 :=
  walk_range_join (fun _ => quadWords) 188082 189618 192690 14848 512 1024 qthree_block_14848 qthree_from_15360
theorem qthree_from_14336 : walk 32 Artifact.commitCode (fun _ => quadWords) 186546 (List.range' 14336 2048) = some 192690 :=
  walk_range_join (fun _ => quadWords) 186546 188082 192690 14336 512 1536 qthree_block_14336 qthree_from_14848
theorem qthree_from_13824 : walk 32 Artifact.commitCode (fun _ => quadWords) 185010 (List.range' 13824 2560) = some 192690 :=
  walk_range_join (fun _ => quadWords) 185010 186546 192690 13824 512 2048 qthree_block_13824 qthree_from_14336
theorem qthree_from_13312 : walk 32 Artifact.commitCode (fun _ => quadWords) 183474 (List.range' 13312 3072) = some 192690 :=
  walk_range_join (fun _ => quadWords) 183474 185010 192690 13312 512 2560 qthree_block_13312 qthree_from_13824
theorem qthree_from_12800 : walk 32 Artifact.commitCode (fun _ => quadWords) 181938 (List.range' 12800 3584) = some 192690 :=
  walk_range_join (fun _ => quadWords) 181938 183474 192690 12800 512 3072 qthree_block_12800 qthree_from_13312
theorem qthree_from_12288 : walk 32 Artifact.commitCode (fun _ => quadWords) 180402 (List.range' 12288 4096) = some 192690 :=
  walk_range_join (fun _ => quadWords) 180402 181938 192690 12288 512 3584 qthree_block_12288 qthree_from_12800
theorem qthree_from_11776 : walk 32 Artifact.commitCode (fun _ => quadWords) 178866 (List.range' 11776 4608) = some 192690 :=
  walk_range_join (fun _ => quadWords) 178866 180402 192690 11776 512 4096 qthree_block_11776 qthree_from_12288
theorem qthree_from_11264 : walk 32 Artifact.commitCode (fun _ => quadWords) 177330 (List.range' 11264 5120) = some 192690 :=
  walk_range_join (fun _ => quadWords) 177330 178866 192690 11264 512 4608 qthree_block_11264 qthree_from_11776
theorem qthree_from_10752 : walk 32 Artifact.commitCode (fun _ => quadWords) 175794 (List.range' 10752 5632) = some 192690 :=
  walk_range_join (fun _ => quadWords) 175794 177330 192690 10752 512 5120 qthree_block_10752 qthree_from_11264
theorem qthree_from_10240 : walk 32 Artifact.commitCode (fun _ => quadWords) 174258 (List.range' 10240 6144) = some 192690 :=
  walk_range_join (fun _ => quadWords) 174258 175794 192690 10240 512 5632 qthree_block_10240 qthree_from_10752
theorem qthree_from_9728 : walk 32 Artifact.commitCode (fun _ => quadWords) 172722 (List.range' 9728 6656) = some 192690 :=
  walk_range_join (fun _ => quadWords) 172722 174258 192690 9728 512 6144 qthree_block_9728 qthree_from_10240
theorem qthree_from_9216 : walk 32 Artifact.commitCode (fun _ => quadWords) 171186 (List.range' 9216 7168) = some 192690 :=
  walk_range_join (fun _ => quadWords) 171186 172722 192690 9216 512 6656 qthree_block_9216 qthree_from_9728
theorem qthree_from_8704 : walk 32 Artifact.commitCode (fun _ => quadWords) 169650 (List.range' 8704 7680) = some 192690 :=
  walk_range_join (fun _ => quadWords) 169650 171186 192690 8704 512 7168 qthree_block_8704 qthree_from_9216
theorem qthree_from_8192 : walk 32 Artifact.commitCode (fun _ => quadWords) 168114 (List.range' 8192 8192) = some 192690 :=
  walk_range_join (fun _ => quadWords) 168114 169650 192690 8192 512 7680 qthree_block_8192 qthree_from_8704
theorem qthree_from_7680 : walk 32 Artifact.commitCode (fun _ => quadWords) 166578 (List.range' 7680 8704) = some 192690 :=
  walk_range_join (fun _ => quadWords) 166578 168114 192690 7680 512 8192 qthree_block_7680 qthree_from_8192
theorem qthree_from_7168 : walk 32 Artifact.commitCode (fun _ => quadWords) 165042 (List.range' 7168 9216) = some 192690 :=
  walk_range_join (fun _ => quadWords) 165042 166578 192690 7168 512 8704 qthree_block_7168 qthree_from_7680
theorem qthree_from_6656 : walk 32 Artifact.commitCode (fun _ => quadWords) 163506 (List.range' 6656 9728) = some 192690 :=
  walk_range_join (fun _ => quadWords) 163506 165042 192690 6656 512 9216 qthree_block_6656 qthree_from_7168
theorem qthree_from_6144 : walk 32 Artifact.commitCode (fun _ => quadWords) 161970 (List.range' 6144 10240) = some 192690 :=
  walk_range_join (fun _ => quadWords) 161970 163506 192690 6144 512 9728 qthree_block_6144 qthree_from_6656
theorem qthree_from_5632 : walk 32 Artifact.commitCode (fun _ => quadWords) 160434 (List.range' 5632 10752) = some 192690 :=
  walk_range_join (fun _ => quadWords) 160434 161970 192690 5632 512 10240 qthree_block_5632 qthree_from_6144
theorem qthree_from_5120 : walk 32 Artifact.commitCode (fun _ => quadWords) 158898 (List.range' 5120 11264) = some 192690 :=
  walk_range_join (fun _ => quadWords) 158898 160434 192690 5120 512 10752 qthree_block_5120 qthree_from_5632
theorem qthree_from_4608 : walk 32 Artifact.commitCode (fun _ => quadWords) 157362 (List.range' 4608 11776) = some 192690 :=
  walk_range_join (fun _ => quadWords) 157362 158898 192690 4608 512 11264 qthree_block_4608 qthree_from_5120
theorem qthree_from_4096 : walk 32 Artifact.commitCode (fun _ => quadWords) 155826 (List.range' 4096 12288) = some 192690 :=
  walk_range_join (fun _ => quadWords) 155826 157362 192690 4096 512 11776 qthree_block_4096 qthree_from_4608
theorem qthree_from_3584 : walk 32 Artifact.commitCode (fun _ => quadWords) 154290 (List.range' 3584 12800) = some 192690 :=
  walk_range_join (fun _ => quadWords) 154290 155826 192690 3584 512 12288 qthree_block_3584 qthree_from_4096
theorem qthree_from_3072 : walk 32 Artifact.commitCode (fun _ => quadWords) 152754 (List.range' 3072 13312) = some 192690 :=
  walk_range_join (fun _ => quadWords) 152754 154290 192690 3072 512 12800 qthree_block_3072 qthree_from_3584
theorem qthree_from_2560 : walk 32 Artifact.commitCode (fun _ => quadWords) 151218 (List.range' 2560 13824) = some 192690 :=
  walk_range_join (fun _ => quadWords) 151218 152754 192690 2560 512 13312 qthree_block_2560 qthree_from_3072
theorem qthree_from_2048 : walk 32 Artifact.commitCode (fun _ => quadWords) 149682 (List.range' 2048 14336) = some 192690 :=
  walk_range_join (fun _ => quadWords) 149682 151218 192690 2048 512 13824 qthree_block_2048 qthree_from_2560
theorem qthree_from_1536 : walk 32 Artifact.commitCode (fun _ => quadWords) 148146 (List.range' 1536 14848) = some 192690 :=
  walk_range_join (fun _ => quadWords) 148146 149682 192690 1536 512 14336 qthree_block_1536 qthree_from_2048
theorem qthree_from_1024 : walk 32 Artifact.commitCode (fun _ => quadWords) 146610 (List.range' 1024 15360) = some 192690 :=
  walk_range_join (fun _ => quadWords) 146610 148146 192690 1024 512 14848 qthree_block_1024 qthree_from_1536
theorem qthree_from_512 : walk 32 Artifact.commitCode (fun _ => quadWords) 145074 (List.range' 512 15872) = some 192690 :=
  walk_range_join (fun _ => quadWords) 145074 146610 192690 512 512 15360 qthree_block_512 qthree_from_1024
theorem qthree_from_0 : walk 32 Artifact.commitCode (fun _ => quadWords) 143538 (List.range' 0 16384) = some 192690 :=
  walk_range_join (fun _ => quadWords) 143538 145074 192690 0 512 15872 qthree_block_0 qthree_from_512
theorem parent_from_13312 : walk 32 Artifact.commitCode (fun _ => parentWords) 245949 (List.range' 13312 485) = some 247889 :=
  parent_block_13312
theorem parent_from_12800 : walk 32 Artifact.commitCode (fun _ => parentWords) 243901 (List.range' 12800 997) = some 247889 :=
  walk_range_join (fun _ => parentWords) 243901 245949 247889 12800 512 485 parent_block_12800 parent_from_13312
theorem parent_from_12288 : walk 32 Artifact.commitCode (fun _ => parentWords) 241853 (List.range' 12288 1509) = some 247889 :=
  walk_range_join (fun _ => parentWords) 241853 243901 247889 12288 512 997 parent_block_12288 parent_from_12800
theorem parent_from_11776 : walk 32 Artifact.commitCode (fun _ => parentWords) 239805 (List.range' 11776 2021) = some 247889 :=
  walk_range_join (fun _ => parentWords) 239805 241853 247889 11776 512 1509 parent_block_11776 parent_from_12288
theorem parent_from_11264 : walk 32 Artifact.commitCode (fun _ => parentWords) 237757 (List.range' 11264 2533) = some 247889 :=
  walk_range_join (fun _ => parentWords) 237757 239805 247889 11264 512 2021 parent_block_11264 parent_from_11776
theorem parent_from_10752 : walk 32 Artifact.commitCode (fun _ => parentWords) 235709 (List.range' 10752 3045) = some 247889 :=
  walk_range_join (fun _ => parentWords) 235709 237757 247889 10752 512 2533 parent_block_10752 parent_from_11264
theorem parent_from_10240 : walk 32 Artifact.commitCode (fun _ => parentWords) 233661 (List.range' 10240 3557) = some 247889 :=
  walk_range_join (fun _ => parentWords) 233661 235709 247889 10240 512 3045 parent_block_10240 parent_from_10752
theorem parent_from_9728 : walk 32 Artifact.commitCode (fun _ => parentWords) 231613 (List.range' 9728 4069) = some 247889 :=
  walk_range_join (fun _ => parentWords) 231613 233661 247889 9728 512 3557 parent_block_9728 parent_from_10240
theorem parent_from_9216 : walk 32 Artifact.commitCode (fun _ => parentWords) 229565 (List.range' 9216 4581) = some 247889 :=
  walk_range_join (fun _ => parentWords) 229565 231613 247889 9216 512 4069 parent_block_9216 parent_from_9728
theorem parent_from_8704 : walk 32 Artifact.commitCode (fun _ => parentWords) 227517 (List.range' 8704 5093) = some 247889 :=
  walk_range_join (fun _ => parentWords) 227517 229565 247889 8704 512 4581 parent_block_8704 parent_from_9216
theorem parent_from_8192 : walk 32 Artifact.commitCode (fun _ => parentWords) 225469 (List.range' 8192 5605) = some 247889 :=
  walk_range_join (fun _ => parentWords) 225469 227517 247889 8192 512 5093 parent_block_8192 parent_from_8704
theorem parent_from_7680 : walk 32 Artifact.commitCode (fun _ => parentWords) 223421 (List.range' 7680 6117) = some 247889 :=
  walk_range_join (fun _ => parentWords) 223421 225469 247889 7680 512 5605 parent_block_7680 parent_from_8192
theorem parent_from_7168 : walk 32 Artifact.commitCode (fun _ => parentWords) 221373 (List.range' 7168 6629) = some 247889 :=
  walk_range_join (fun _ => parentWords) 221373 223421 247889 7168 512 6117 parent_block_7168 parent_from_7680
theorem parent_from_6656 : walk 32 Artifact.commitCode (fun _ => parentWords) 219325 (List.range' 6656 7141) = some 247889 :=
  walk_range_join (fun _ => parentWords) 219325 221373 247889 6656 512 6629 parent_block_6656 parent_from_7168
theorem parent_from_6144 : walk 32 Artifact.commitCode (fun _ => parentWords) 217277 (List.range' 6144 7653) = some 247889 :=
  walk_range_join (fun _ => parentWords) 217277 219325 247889 6144 512 7141 parent_block_6144 parent_from_6656
theorem parent_from_5632 : walk 32 Artifact.commitCode (fun _ => parentWords) 215229 (List.range' 5632 8165) = some 247889 :=
  walk_range_join (fun _ => parentWords) 215229 217277 247889 5632 512 7653 parent_block_5632 parent_from_6144
theorem parent_from_5120 : walk 32 Artifact.commitCode (fun _ => parentWords) 213181 (List.range' 5120 8677) = some 247889 :=
  walk_range_join (fun _ => parentWords) 213181 215229 247889 5120 512 8165 parent_block_5120 parent_from_5632
theorem parent_from_4608 : walk 32 Artifact.commitCode (fun _ => parentWords) 211133 (List.range' 4608 9189) = some 247889 :=
  walk_range_join (fun _ => parentWords) 211133 213181 247889 4608 512 8677 parent_block_4608 parent_from_5120
theorem parent_from_4096 : walk 32 Artifact.commitCode (fun _ => parentWords) 209085 (List.range' 4096 9701) = some 247889 :=
  walk_range_join (fun _ => parentWords) 209085 211133 247889 4096 512 9189 parent_block_4096 parent_from_4608
theorem parent_from_3584 : walk 32 Artifact.commitCode (fun _ => parentWords) 207037 (List.range' 3584 10213) = some 247889 :=
  walk_range_join (fun _ => parentWords) 207037 209085 247889 3584 512 9701 parent_block_3584 parent_from_4096
theorem parent_from_3072 : walk 32 Artifact.commitCode (fun _ => parentWords) 204989 (List.range' 3072 10725) = some 247889 :=
  walk_range_join (fun _ => parentWords) 204989 207037 247889 3072 512 10213 parent_block_3072 parent_from_3584
theorem parent_from_2560 : walk 32 Artifact.commitCode (fun _ => parentWords) 202941 (List.range' 2560 11237) = some 247889 :=
  walk_range_join (fun _ => parentWords) 202941 204989 247889 2560 512 10725 parent_block_2560 parent_from_3072
theorem parent_from_2048 : walk 32 Artifact.commitCode (fun _ => parentWords) 200893 (List.range' 2048 11749) = some 247889 :=
  walk_range_join (fun _ => parentWords) 200893 202941 247889 2048 512 11237 parent_block_2048 parent_from_2560
theorem parent_from_1536 : walk 32 Artifact.commitCode (fun _ => parentWords) 198845 (List.range' 1536 12261) = some 247889 :=
  walk_range_join (fun _ => parentWords) 198845 200893 247889 1536 512 11749 parent_block_1536 parent_from_2048
theorem parent_from_1024 : walk 32 Artifact.commitCode (fun _ => parentWords) 196797 (List.range' 1024 12773) = some 247889 :=
  walk_range_join (fun _ => parentWords) 196797 198845 247889 1024 512 12261 parent_block_1024 parent_from_1536
theorem parent_from_512 : walk 32 Artifact.commitCode (fun _ => parentWords) 194749 (List.range' 512 13285) = some 247889 :=
  walk_range_join (fun _ => parentWords) 194749 196797 247889 512 512 12773 parent_block_512 parent_from_1024
theorem parent_from_0 : walk 32 Artifact.commitCode (fun _ => parentWords) 192701 (List.range' 0 13797) = some 247889 :=
  walk_range_join (fun _ => parentWords) 192701 194749 247889 0 512 13285 parent_block_0 parent_from_512
theorem seg_0_setupWords : walk 32 Artifact.commitCode id 0 [setupWords] = some 19 := by decide +kernel
theorem seg_1_leafCode : walk 32 Artifact.commitCode id 19 [leafCode] = some 45201 := by
  rw [show leafCode = (List.range' 0 4096).flatMap leafWords by rw [leafCode, List.range_eq_range']]
  exact walk_flatten 32 _ leafWords _ 19 45201 leaf_from_0
theorem seg_2_leafLatchWords : walk 32 Artifact.commitCode id 45201 [leafLatchWords] = some 45203 := by decide +kernel
theorem seg_3_quadSetupWords : walk 32 Artifact.commitCode id 45203 [quadSetupWords] = some 45212 := by decide +kernel
theorem seg_4_quadCode : walk 32 Artifact.commitCode id 45212 [quadCode] = some 94364 := by
  rw [show quadCode = (List.range' 0 4096).flatMap (fun _ => quadGroupWords) by rw [quadCode, replicate_flatten_eq]]
  exact walk_flatten 32 _ _ _ 45212 94364 quad_from_0
theorem seg_5_quadLatchWords : walk 32 Artifact.commitCode id 94364 [quadLatchWords] = some 94366 := by decide +kernel
theorem seg_6_quad2SetupWords : walk 32 Artifact.commitCode id 94366 [quad2SetupWords] = some 94375 := by decide +kernel
theorem seg_7_quad2Code : walk 32 Artifact.commitCode id 94375 [quad2Code] = some 143527 := by
  rw [show quad2Code = (List.range' 0 4096).flatMap (fun _ => quadGroupWords) by rw [quad2Code, replicate_flatten_eq]]
  exact walk_flatten 32 _ _ _ 94375 143527 qtwo_from_0
theorem seg_8_quadLatchWords : walk 32 Artifact.commitCode id 143527 [quadLatchWords] = some 143529 := by decide +kernel
theorem seg_9_quad3SetupWords : walk 32 Artifact.commitCode id 143529 [quad3SetupWords] = some 143538 := by decide +kernel
theorem seg_10_quad3Code : walk 32 Artifact.commitCode id 143538 [quad3Code] = some 192690 := by
  rw [show quad3Code = (List.range' 0 16384).flatMap (fun _ => quadWords) by rw [quad3Code, replicate_flatten_eq]]
  exact walk_flatten 32 _ _ _ 143538 192690 qthree_from_0
theorem seg_11_quadLatchWords : walk 32 Artifact.commitCode id 192690 [quadLatchWords] = some 192692 := by decide +kernel
theorem seg_12_parentSetupWords : walk 32 Artifact.commitCode id 192692 [parentSetupWords] = some 192701 := by decide +kernel
theorem seg_13_parentCode : walk 32 Artifact.commitCode id 192701 [parentCode] = some 247889 := by
  rw [show parentCode = (List.range' 0 13797).flatMap (fun _ => parentWords) by rw [parentCode, replicate_flatten_eq]]
  exact walk_flatten 32 _ _ _ 192701 247889 parent_from_0
theorem seg_14_parentLatchWords : walk 32 Artifact.commitCode id 247889 [parentLatchWords] = some 247891 := by decide +kernel
theorem seg_15_rootWords : walk 32 Artifact.commitCode id 247891 [rootWords] = some 248102 := by decide +kernel

theorem code_walk : walk 32 Artifact.commitCode id 0 [setupWords, leafCode, leafLatchWords, quadSetupWords, quadCode, quadLatchWords, quad2SetupWords, quad2Code, quadLatchWords, quad3SetupWords, quad3Code, quadLatchWords, parentSetupWords, parentCode, parentLatchWords, rootWords] = some 248102 := by
  exact (walk_append 32 _ id [setupWords] ([leafCode] ++ ([leafLatchWords] ++ ([quadSetupWords] ++ ([quadCode] ++ ([quadLatchWords] ++ ([quad2SetupWords] ++ ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))))))))))) 0 19 248102 seg_0_setupWords (walk_append 32 _ id [leafCode] ([leafLatchWords] ++ ([quadSetupWords] ++ ([quadCode] ++ ([quadLatchWords] ++ ([quad2SetupWords] ++ ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))))))))))) 19 45201 248102 seg_1_leafCode (walk_append 32 _ id [leafLatchWords] ([quadSetupWords] ++ ([quadCode] ++ ([quadLatchWords] ++ ([quad2SetupWords] ++ ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))))))))) 45201 45203 248102 seg_2_leafLatchWords (walk_append 32 _ id [quadSetupWords] ([quadCode] ++ ([quadLatchWords] ++ ([quad2SetupWords] ++ ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))))))))) 45203 45212 248102 seg_3_quadSetupWords (walk_append 32 _ id [quadCode] ([quadLatchWords] ++ ([quad2SetupWords] ++ ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))))))) 45212 94364 248102 seg_4_quadCode (walk_append 32 _ id [quadLatchWords] ([quad2SetupWords] ++ ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))))))) 94364 94366 248102 seg_5_quadLatchWords (walk_append 32 _ id [quad2SetupWords] ([quad2Code] ++ ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))))) 94366 94375 248102 seg_6_quad2SetupWords (walk_append 32 _ id [quad2Code] ([quadLatchWords] ++ ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))))) 94375 143527 248102 seg_7_quad2Code (walk_append 32 _ id [quadLatchWords] ([quad3SetupWords] ++ ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))) 143527 143529 248102 seg_8_quadLatchWords (walk_append 32 _ id [quad3SetupWords] ([quad3Code] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))) 143529 143538 248102 seg_9_quad3SetupWords (walk_append 32 _ id [quad3Code] ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))) 143538 192690 248102 seg_10_quad3Code (walk_append 32 _ id [quadLatchWords] ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))) 192690 192692 248102 seg_11_quadLatchWords (walk_append 32 _ id [parentSetupWords] ([parentCode] ++ ([parentLatchWords] ++ [rootWords])) 192692 192701 248102 seg_12_parentSetupWords (walk_append 32 _ id [parentCode] ([parentLatchWords] ++ [rootWords]) 192701 247889 248102 seg_13_parentCode (walk_append 32 _ id [parentLatchWords] [rootWords] 247889 247891 248102 seg_14_parentLatchWords seg_15_rootWords)))))))))))))))

theorem commit_code_matches : matchesFrom 32 Artifact.commitCode 0 image.code = true := by
  obtain ⟨ok, len⟩ := walk_sound 32 _ id _ 0 248102 code_walk
  have code : image.code = [setupWords, leafCode, leafLatchWords, quadSetupWords, quadCode, quadLatchWords, quad2SetupWords, quad2Code, quadLatchWords, quad3SetupWords, quad3Code, quadLatchWords, parentSetupWords, parentCode, parentLatchWords, rootWords].flatMap id := by
    simp only [image, List.flatMap_cons, List.flatMap_nil, id, List.append_nil, List.append_assoc]
  rw [code]
  exact matches_of_prefix 32 _ _ 0 ok len

theorem quad_commit_image : Artifact.submission.image .commit = image := by
  simp only [Artifact.submission]
  rw [decode_of_matches 32 _ _ commit_code_matches]
  rfl

end TwoPermutationPrototype.ArtifactMatchB
