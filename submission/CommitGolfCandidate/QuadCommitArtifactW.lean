import CommitGolfCandidate.QuadCommitWalk_leaf0
import CommitGolfCandidate.QuadCommitWalk_leaf1
import CommitGolfCandidate.QuadCommitWalk_leaf2
import CommitGolfCandidate.QuadCommitWalk_leaf3
import CommitGolfCandidate.QuadCommitWalk_quad0
import CommitGolfCandidate.QuadCommitWalk_quad1
import CommitGolfCandidate.QuadCommitWalk_quad2
import CommitGolfCandidate.QuadCommitWalk_quad3
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
theorem quad_from_15872 : walk 32 Artifact.commitCode (fun _ => quadWords) 92828 (List.range' 15872 512) = some 94364 :=
  quad_block_15872
theorem quad_from_15360 : walk 32 Artifact.commitCode (fun _ => quadWords) 91292 (List.range' 15360 1024) = some 94364 :=
  walk_range_join (fun _ => quadWords) 91292 92828 94364 15360 512 512 quad_block_15360 quad_from_15872
theorem quad_from_14848 : walk 32 Artifact.commitCode (fun _ => quadWords) 89756 (List.range' 14848 1536) = some 94364 :=
  walk_range_join (fun _ => quadWords) 89756 91292 94364 14848 512 1024 quad_block_14848 quad_from_15360
theorem quad_from_14336 : walk 32 Artifact.commitCode (fun _ => quadWords) 88220 (List.range' 14336 2048) = some 94364 :=
  walk_range_join (fun _ => quadWords) 88220 89756 94364 14336 512 1536 quad_block_14336 quad_from_14848
theorem quad_from_13824 : walk 32 Artifact.commitCode (fun _ => quadWords) 86684 (List.range' 13824 2560) = some 94364 :=
  walk_range_join (fun _ => quadWords) 86684 88220 94364 13824 512 2048 quad_block_13824 quad_from_14336
theorem quad_from_13312 : walk 32 Artifact.commitCode (fun _ => quadWords) 85148 (List.range' 13312 3072) = some 94364 :=
  walk_range_join (fun _ => quadWords) 85148 86684 94364 13312 512 2560 quad_block_13312 quad_from_13824
theorem quad_from_12800 : walk 32 Artifact.commitCode (fun _ => quadWords) 83612 (List.range' 12800 3584) = some 94364 :=
  walk_range_join (fun _ => quadWords) 83612 85148 94364 12800 512 3072 quad_block_12800 quad_from_13312
theorem quad_from_12288 : walk 32 Artifact.commitCode (fun _ => quadWords) 82076 (List.range' 12288 4096) = some 94364 :=
  walk_range_join (fun _ => quadWords) 82076 83612 94364 12288 512 3584 quad_block_12288 quad_from_12800
theorem quad_from_11776 : walk 32 Artifact.commitCode (fun _ => quadWords) 80540 (List.range' 11776 4608) = some 94364 :=
  walk_range_join (fun _ => quadWords) 80540 82076 94364 11776 512 4096 quad_block_11776 quad_from_12288
theorem quad_from_11264 : walk 32 Artifact.commitCode (fun _ => quadWords) 79004 (List.range' 11264 5120) = some 94364 :=
  walk_range_join (fun _ => quadWords) 79004 80540 94364 11264 512 4608 quad_block_11264 quad_from_11776
theorem quad_from_10752 : walk 32 Artifact.commitCode (fun _ => quadWords) 77468 (List.range' 10752 5632) = some 94364 :=
  walk_range_join (fun _ => quadWords) 77468 79004 94364 10752 512 5120 quad_block_10752 quad_from_11264
theorem quad_from_10240 : walk 32 Artifact.commitCode (fun _ => quadWords) 75932 (List.range' 10240 6144) = some 94364 :=
  walk_range_join (fun _ => quadWords) 75932 77468 94364 10240 512 5632 quad_block_10240 quad_from_10752
theorem quad_from_9728 : walk 32 Artifact.commitCode (fun _ => quadWords) 74396 (List.range' 9728 6656) = some 94364 :=
  walk_range_join (fun _ => quadWords) 74396 75932 94364 9728 512 6144 quad_block_9728 quad_from_10240
theorem quad_from_9216 : walk 32 Artifact.commitCode (fun _ => quadWords) 72860 (List.range' 9216 7168) = some 94364 :=
  walk_range_join (fun _ => quadWords) 72860 74396 94364 9216 512 6656 quad_block_9216 quad_from_9728
theorem quad_from_8704 : walk 32 Artifact.commitCode (fun _ => quadWords) 71324 (List.range' 8704 7680) = some 94364 :=
  walk_range_join (fun _ => quadWords) 71324 72860 94364 8704 512 7168 quad_block_8704 quad_from_9216
theorem quad_from_8192 : walk 32 Artifact.commitCode (fun _ => quadWords) 69788 (List.range' 8192 8192) = some 94364 :=
  walk_range_join (fun _ => quadWords) 69788 71324 94364 8192 512 7680 quad_block_8192 quad_from_8704
theorem quad_from_7680 : walk 32 Artifact.commitCode (fun _ => quadWords) 68252 (List.range' 7680 8704) = some 94364 :=
  walk_range_join (fun _ => quadWords) 68252 69788 94364 7680 512 8192 quad_block_7680 quad_from_8192
theorem quad_from_7168 : walk 32 Artifact.commitCode (fun _ => quadWords) 66716 (List.range' 7168 9216) = some 94364 :=
  walk_range_join (fun _ => quadWords) 66716 68252 94364 7168 512 8704 quad_block_7168 quad_from_7680
theorem quad_from_6656 : walk 32 Artifact.commitCode (fun _ => quadWords) 65180 (List.range' 6656 9728) = some 94364 :=
  walk_range_join (fun _ => quadWords) 65180 66716 94364 6656 512 9216 quad_block_6656 quad_from_7168
theorem quad_from_6144 : walk 32 Artifact.commitCode (fun _ => quadWords) 63644 (List.range' 6144 10240) = some 94364 :=
  walk_range_join (fun _ => quadWords) 63644 65180 94364 6144 512 9728 quad_block_6144 quad_from_6656
theorem quad_from_5632 : walk 32 Artifact.commitCode (fun _ => quadWords) 62108 (List.range' 5632 10752) = some 94364 :=
  walk_range_join (fun _ => quadWords) 62108 63644 94364 5632 512 10240 quad_block_5632 quad_from_6144
theorem quad_from_5120 : walk 32 Artifact.commitCode (fun _ => quadWords) 60572 (List.range' 5120 11264) = some 94364 :=
  walk_range_join (fun _ => quadWords) 60572 62108 94364 5120 512 10752 quad_block_5120 quad_from_5632
theorem quad_from_4608 : walk 32 Artifact.commitCode (fun _ => quadWords) 59036 (List.range' 4608 11776) = some 94364 :=
  walk_range_join (fun _ => quadWords) 59036 60572 94364 4608 512 11264 quad_block_4608 quad_from_5120
theorem quad_from_4096 : walk 32 Artifact.commitCode (fun _ => quadWords) 57500 (List.range' 4096 12288) = some 94364 :=
  walk_range_join (fun _ => quadWords) 57500 59036 94364 4096 512 11776 quad_block_4096 quad_from_4608
theorem quad_from_3584 : walk 32 Artifact.commitCode (fun _ => quadWords) 55964 (List.range' 3584 12800) = some 94364 :=
  walk_range_join (fun _ => quadWords) 55964 57500 94364 3584 512 12288 quad_block_3584 quad_from_4096
theorem quad_from_3072 : walk 32 Artifact.commitCode (fun _ => quadWords) 54428 (List.range' 3072 13312) = some 94364 :=
  walk_range_join (fun _ => quadWords) 54428 55964 94364 3072 512 12800 quad_block_3072 quad_from_3584
theorem quad_from_2560 : walk 32 Artifact.commitCode (fun _ => quadWords) 52892 (List.range' 2560 13824) = some 94364 :=
  walk_range_join (fun _ => quadWords) 52892 54428 94364 2560 512 13312 quad_block_2560 quad_from_3072
theorem quad_from_2048 : walk 32 Artifact.commitCode (fun _ => quadWords) 51356 (List.range' 2048 14336) = some 94364 :=
  walk_range_join (fun _ => quadWords) 51356 52892 94364 2048 512 13824 quad_block_2048 quad_from_2560
theorem quad_from_1536 : walk 32 Artifact.commitCode (fun _ => quadWords) 49820 (List.range' 1536 14848) = some 94364 :=
  walk_range_join (fun _ => quadWords) 49820 51356 94364 1536 512 14336 quad_block_1536 quad_from_2048
theorem quad_from_1024 : walk 32 Artifact.commitCode (fun _ => quadWords) 48284 (List.range' 1024 15360) = some 94364 :=
  walk_range_join (fun _ => quadWords) 48284 49820 94364 1024 512 14848 quad_block_1024 quad_from_1536
theorem quad_from_512 : walk 32 Artifact.commitCode (fun _ => quadWords) 46748 (List.range' 512 15872) = some 94364 :=
  walk_range_join (fun _ => quadWords) 46748 48284 94364 512 512 15360 quad_block_512 quad_from_1024
theorem quad_from_0 : walk 32 Artifact.commitCode (fun _ => quadWords) 45212 (List.range' 0 16384) = some 94364 :=
  walk_range_join (fun _ => quadWords) 45212 46748 94364 0 512 15872 quad_block_0 quad_from_512
theorem parent_from_15360 : walk 32 Artifact.commitCode (fun _ => parentWords) 155815 (List.range' 15360 349) = some 157211 :=
  parent_block_15360
theorem parent_from_14848 : walk 32 Artifact.commitCode (fun _ => parentWords) 153767 (List.range' 14848 861) = some 157211 :=
  walk_range_join (fun _ => parentWords) 153767 155815 157211 14848 512 349 parent_block_14848 parent_from_15360
theorem parent_from_14336 : walk 32 Artifact.commitCode (fun _ => parentWords) 151719 (List.range' 14336 1373) = some 157211 :=
  walk_range_join (fun _ => parentWords) 151719 153767 157211 14336 512 861 parent_block_14336 parent_from_14848
theorem parent_from_13824 : walk 32 Artifact.commitCode (fun _ => parentWords) 149671 (List.range' 13824 1885) = some 157211 :=
  walk_range_join (fun _ => parentWords) 149671 151719 157211 13824 512 1373 parent_block_13824 parent_from_14336
theorem parent_from_13312 : walk 32 Artifact.commitCode (fun _ => parentWords) 147623 (List.range' 13312 2397) = some 157211 :=
  walk_range_join (fun _ => parentWords) 147623 149671 157211 13312 512 1885 parent_block_13312 parent_from_13824
theorem parent_from_12800 : walk 32 Artifact.commitCode (fun _ => parentWords) 145575 (List.range' 12800 2909) = some 157211 :=
  walk_range_join (fun _ => parentWords) 145575 147623 157211 12800 512 2397 parent_block_12800 parent_from_13312
theorem parent_from_12288 : walk 32 Artifact.commitCode (fun _ => parentWords) 143527 (List.range' 12288 3421) = some 157211 :=
  walk_range_join (fun _ => parentWords) 143527 145575 157211 12288 512 2909 parent_block_12288 parent_from_12800
theorem parent_from_11776 : walk 32 Artifact.commitCode (fun _ => parentWords) 141479 (List.range' 11776 3933) = some 157211 :=
  walk_range_join (fun _ => parentWords) 141479 143527 157211 11776 512 3421 parent_block_11776 parent_from_12288
theorem parent_from_11264 : walk 32 Artifact.commitCode (fun _ => parentWords) 139431 (List.range' 11264 4445) = some 157211 :=
  walk_range_join (fun _ => parentWords) 139431 141479 157211 11264 512 3933 parent_block_11264 parent_from_11776
theorem parent_from_10752 : walk 32 Artifact.commitCode (fun _ => parentWords) 137383 (List.range' 10752 4957) = some 157211 :=
  walk_range_join (fun _ => parentWords) 137383 139431 157211 10752 512 4445 parent_block_10752 parent_from_11264
theorem parent_from_10240 : walk 32 Artifact.commitCode (fun _ => parentWords) 135335 (List.range' 10240 5469) = some 157211 :=
  walk_range_join (fun _ => parentWords) 135335 137383 157211 10240 512 4957 parent_block_10240 parent_from_10752
theorem parent_from_9728 : walk 32 Artifact.commitCode (fun _ => parentWords) 133287 (List.range' 9728 5981) = some 157211 :=
  walk_range_join (fun _ => parentWords) 133287 135335 157211 9728 512 5469 parent_block_9728 parent_from_10240
theorem parent_from_9216 : walk 32 Artifact.commitCode (fun _ => parentWords) 131239 (List.range' 9216 6493) = some 157211 :=
  walk_range_join (fun _ => parentWords) 131239 133287 157211 9216 512 5981 parent_block_9216 parent_from_9728
theorem parent_from_8704 : walk 32 Artifact.commitCode (fun _ => parentWords) 129191 (List.range' 8704 7005) = some 157211 :=
  walk_range_join (fun _ => parentWords) 129191 131239 157211 8704 512 6493 parent_block_8704 parent_from_9216
theorem parent_from_8192 : walk 32 Artifact.commitCode (fun _ => parentWords) 127143 (List.range' 8192 7517) = some 157211 :=
  walk_range_join (fun _ => parentWords) 127143 129191 157211 8192 512 7005 parent_block_8192 parent_from_8704
theorem parent_from_7680 : walk 32 Artifact.commitCode (fun _ => parentWords) 125095 (List.range' 7680 8029) = some 157211 :=
  walk_range_join (fun _ => parentWords) 125095 127143 157211 7680 512 7517 parent_block_7680 parent_from_8192
theorem parent_from_7168 : walk 32 Artifact.commitCode (fun _ => parentWords) 123047 (List.range' 7168 8541) = some 157211 :=
  walk_range_join (fun _ => parentWords) 123047 125095 157211 7168 512 8029 parent_block_7168 parent_from_7680
theorem parent_from_6656 : walk 32 Artifact.commitCode (fun _ => parentWords) 120999 (List.range' 6656 9053) = some 157211 :=
  walk_range_join (fun _ => parentWords) 120999 123047 157211 6656 512 8541 parent_block_6656 parent_from_7168
theorem parent_from_6144 : walk 32 Artifact.commitCode (fun _ => parentWords) 118951 (List.range' 6144 9565) = some 157211 :=
  walk_range_join (fun _ => parentWords) 118951 120999 157211 6144 512 9053 parent_block_6144 parent_from_6656
theorem parent_from_5632 : walk 32 Artifact.commitCode (fun _ => parentWords) 116903 (List.range' 5632 10077) = some 157211 :=
  walk_range_join (fun _ => parentWords) 116903 118951 157211 5632 512 9565 parent_block_5632 parent_from_6144
theorem parent_from_5120 : walk 32 Artifact.commitCode (fun _ => parentWords) 114855 (List.range' 5120 10589) = some 157211 :=
  walk_range_join (fun _ => parentWords) 114855 116903 157211 5120 512 10077 parent_block_5120 parent_from_5632
theorem parent_from_4608 : walk 32 Artifact.commitCode (fun _ => parentWords) 112807 (List.range' 4608 11101) = some 157211 :=
  walk_range_join (fun _ => parentWords) 112807 114855 157211 4608 512 10589 parent_block_4608 parent_from_5120
theorem parent_from_4096 : walk 32 Artifact.commitCode (fun _ => parentWords) 110759 (List.range' 4096 11613) = some 157211 :=
  walk_range_join (fun _ => parentWords) 110759 112807 157211 4096 512 11101 parent_block_4096 parent_from_4608
theorem parent_from_3584 : walk 32 Artifact.commitCode (fun _ => parentWords) 108711 (List.range' 3584 12125) = some 157211 :=
  walk_range_join (fun _ => parentWords) 108711 110759 157211 3584 512 11613 parent_block_3584 parent_from_4096
theorem parent_from_3072 : walk 32 Artifact.commitCode (fun _ => parentWords) 106663 (List.range' 3072 12637) = some 157211 :=
  walk_range_join (fun _ => parentWords) 106663 108711 157211 3072 512 12125 parent_block_3072 parent_from_3584
theorem parent_from_2560 : walk 32 Artifact.commitCode (fun _ => parentWords) 104615 (List.range' 2560 13149) = some 157211 :=
  walk_range_join (fun _ => parentWords) 104615 106663 157211 2560 512 12637 parent_block_2560 parent_from_3072
theorem parent_from_2048 : walk 32 Artifact.commitCode (fun _ => parentWords) 102567 (List.range' 2048 13661) = some 157211 :=
  walk_range_join (fun _ => parentWords) 102567 104615 157211 2048 512 13149 parent_block_2048 parent_from_2560
theorem parent_from_1536 : walk 32 Artifact.commitCode (fun _ => parentWords) 100519 (List.range' 1536 14173) = some 157211 :=
  walk_range_join (fun _ => parentWords) 100519 102567 157211 1536 512 13661 parent_block_1536 parent_from_2048
theorem parent_from_1024 : walk 32 Artifact.commitCode (fun _ => parentWords) 98471 (List.range' 1024 14685) = some 157211 :=
  walk_range_join (fun _ => parentWords) 98471 100519 157211 1024 512 14173 parent_block_1024 parent_from_1536
theorem parent_from_512 : walk 32 Artifact.commitCode (fun _ => parentWords) 96423 (List.range' 512 15197) = some 157211 :=
  walk_range_join (fun _ => parentWords) 96423 98471 157211 512 512 14685 parent_block_512 parent_from_1024
theorem parent_from_0 : walk 32 Artifact.commitCode (fun _ => parentWords) 94375 (List.range' 0 15709) = some 157211 :=
  walk_range_join (fun _ => parentWords) 94375 96423 157211 0 512 15197 parent_block_0 parent_from_512
theorem seg_setupWords : walk 32 Artifact.commitCode id 0 [setupWords] = some 19 := by decide +kernel
theorem seg_leafCode : walk 32 Artifact.commitCode id 19 [leafCode] = some 45201 := by
  rw [show leafCode = (List.range' 0 4096).flatMap leafWords by rw [leafCode, List.range_eq_range']]
  exact walk_flatten 32 _ leafWords _ 19 45201 leaf_from_0
theorem seg_leafLatchWords : walk 32 Artifact.commitCode id 45201 [leafLatchWords] = some 45203 := by decide +kernel
theorem seg_quadSetupWords : walk 32 Artifact.commitCode id 45203 [quadSetupWords] = some 45212 := by decide +kernel
theorem seg_quadCode : walk 32 Artifact.commitCode id 45212 [quadCode] = some 94364 := by
  rw [show quadCode = (List.range' 0 16384).flatMap (fun _ => quadWords) by rw [quadCode, replicate_flatten_eq]]
  exact walk_flatten 32 _ _ _ 45212 94364 quad_from_0
theorem seg_quadLatchWords : walk 32 Artifact.commitCode id 94364 [quadLatchWords] = some 94366 := by decide +kernel
theorem seg_parentSetupWords : walk 32 Artifact.commitCode id 94366 [parentSetupWords] = some 94375 := by decide +kernel
theorem seg_parentCode : walk 32 Artifact.commitCode id 94375 [parentCode] = some 157211 := by
  rw [show parentCode = (List.range' 0 15709).flatMap (fun _ => parentWords) by rw [parentCode, replicate_flatten_eq]]
  exact walk_flatten 32 _ _ _ 94375 157211 parent_from_0
theorem seg_parentLatchWords : walk 32 Artifact.commitCode id 157211 [parentLatchWords] = some 157213 := by decide +kernel
theorem seg_rootWords : walk 32 Artifact.commitCode id 157213 [rootWords] = some 157424 := by decide +kernel

theorem code_walk : walk 32 Artifact.commitCode id 0 [setupWords, leafCode, leafLatchWords, quadSetupWords, quadCode, quadLatchWords, parentSetupWords, parentCode, parentLatchWords, rootWords] = some 157424 := by
  exact (walk_append 32 _ id [setupWords] ([leafCode] ++ ([leafLatchWords] ++ ([quadSetupWords] ++ ([quadCode] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))))) 0 19 157424 seg_setupWords (walk_append 32 _ id [leafCode] ([leafLatchWords] ++ ([quadSetupWords] ++ ([quadCode] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))))) 19 45201 157424 seg_leafCode (walk_append 32 _ id [leafLatchWords] ([quadSetupWords] ++ ([quadCode] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))))) 45201 45203 157424 seg_leafLatchWords (walk_append 32 _ id [quadSetupWords] ([quadCode] ++ ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))))) 45203 45212 157424 seg_quadSetupWords (walk_append 32 _ id [quadCode] ([quadLatchWords] ++ ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords])))) 45212 94364 157424 seg_quadCode (walk_append 32 _ id [quadLatchWords] ([parentSetupWords] ++ ([parentCode] ++ ([parentLatchWords] ++ [rootWords]))) 94364 94366 157424 seg_quadLatchWords (walk_append 32 _ id [parentSetupWords] ([parentCode] ++ ([parentLatchWords] ++ [rootWords])) 94366 94375 157424 seg_parentSetupWords (walk_append 32 _ id [parentCode] ([parentLatchWords] ++ [rootWords]) 94375 157211 157424 seg_parentCode (walk_append 32 _ id [parentLatchWords] [rootWords] 157211 157213 157424 seg_parentLatchWords seg_rootWords)))))))))

theorem commit_code_matches : matchesFrom 32 Artifact.commitCode 0 image.code = true := by
  obtain ⟨ok, len⟩ := walk_sound 32 _ id _ 0 157424 code_walk
  have code : image.code = [setupWords, leafCode, leafLatchWords, quadSetupWords, quadCode, quadLatchWords, parentSetupWords, parentCode, parentLatchWords, rootWords].flatMap id := by
    simp only [image, List.flatMap_cons, List.flatMap_nil, id, List.append_nil, List.append_assoc]
  rw [code]
  exact matches_of_prefix 32 _ _ 0 ok len

theorem quad_commit_image : Artifact.submission.image .commit = image := by
  simp only [Artifact.submission]
  rw [decode_of_matches 32 _ _ commit_code_matches]
  rfl

end TwoPermutationPrototype.ArtifactMatchB
