import CommitGolf.Artifact
import CommitGolfCandidate.MixedWidthParentControl
import CommitGolfCandidate.TwoPermutationPackedParentControl
import CommitGolfCandidate.TwoPermutationCommitRun

/-! Exact mixed-width parent bridge for the chain composition. The parent/root
range ends before unused padding; the P4 grouped leaf body ends at word 45,494; the chain generator is gone. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

private def fullWord (i : Nat) : BitVec 32 :=
  if i%3=0 then 0x73 else if i%3=1 then 0xfc050513 else 0xfe060613
private def projectedWord (i : Nat) : BitVec 32 :=
  if i%4=0 then 0x73 else if i%4=1 then 0x00061f23 else if i%4=2 then 0xfc050513 else 0xfe060613
private def rootWords : List (BitVec 32) :=
  [0x0204bf83,0x01f43023,0x0284bf83,0x01f43423,0x0304bf83,0x01f43823,0x0384bf83,0x01f43c23,0x00100293,0x00000513,0x00000073]
private def expectedWord (index : Nat) : BitVec 32 :=
  if index=45677 then 0x80008b7 else
  if index=45678 then 0x011488b3 else
  if index=45679 then 0xfe088893 else
  if index<143984 then fullWord (index-45680) else
  if index=143984 then 18220131 else
  if index=143985 then 4292472943 else
  if index<206822 then projectedWord (index-143986) else
  if index=206822 then 9831523 else
  if index=206823 then 2732335215 else
  rootWords.getD (index-206824) 0

private def RangeMatches {count : Nat} (packed : ArtifactEncoding.Packed count) (offset : Nat) : Prop :=
  ∀ i : Fin count, 45677≤offset+i.val → offset+i.val<206835 → packed.get 32 i=expectedWord (offset+i.val)

private theorem range_join {a b : Nat} (left : ArtifactEncoding.Packed a) (right : ArtifactEncoding.Packed b)
    (offset : Nat) (first : RangeMatches left offset) (last : RangeMatches right (offset+a)) :
    RangeMatches (.join left right) offset := by
  intro i lower upper
  by_cases inside : i.val<a
  · rw [ArtifactEncoding.get_join_left 32 left right i inside]
    exact first ⟨i.val,inside⟩ lower upper
  · rw [ArtifactEncoding.get_join_right 32 left right i inside]
    have pos : offset+a+(i.val-a)=offset+i.val := by omega
    have eq := last ⟨i.val-a,by omega⟩ (by simpa only [pos] using lower) (by simpa only [pos] using upper)
    simpa only [pos] using eq

private theorem full_decode_1 (i : Fin 512) :
  Artifact.commitCode_0_90.get 32 i=fullWord (1+i.val) := by
  fin_cases i <;> rfl

private theorem full_decode_0 (i : Fin 512) :
  Artifact.commitCode_0_91.get 32 i=fullWord (0+i.val) := by
  fin_cases i <;> rfl

private theorem full_decode_2 (i : Fin 512) :
  Artifact.commitCode_0_92.get 32 i=fullWord (2+i.val) := by
  fin_cases i <;> rfl

private theorem full_window (packed : ArtifactEncoding.Packed 512) (offset phase : Nat)
    (alignment : (offset-45680)%3=phase%3)
    (inside : 45680≤offset) (ends : offset+512≤143984)
    (decode : ∀ i : Fin 512, packed.get 32 i=fullWord (phase+i.val)) : RangeMatches packed offset := by
  intro i _ _
  have lim := i.isLt
  have actual : expectedWord (offset+i.val)=fullWord (offset+i.val-45680) := by
    simp only [expectedWord]
    simp only [if_neg (by omega : offset+i.val≠45677),if_neg (by omega : offset+i.val≠45678),
      if_neg (by omega : offset+i.val≠45679)]
    rw [if_pos (by omega)]
  rw [actual,decode]
  simp only [fullWord]
  have same : (phase+i.val)%3=(offset+i.val-45680)%3 := by omega
  rw [same]

private theorem projected_decode_2 (i : Fin 512) :
  Artifact.commitCode_0_282.get 32 i=projectedWord (2+i.val) := by
  fin_cases i <;> rfl

private theorem projected_window (packed : ArtifactEncoding.Packed 512) (offset phase : Nat)
    (alignment : (offset-143986)%4=phase%4)
    (inside : 143986≤offset) (ends : offset+512≤206822)
    (decode : ∀ i : Fin 512, packed.get 32 i=projectedWord (phase+i.val)) : RangeMatches packed offset := by
  intro i _ _
  have lim := i.isLt
  have actual : expectedWord (offset+i.val)=projectedWord (offset+i.val-143986) := by
    simp only [expectedWord]
    simp only [if_neg (by omega : offset+i.val≠45677),if_neg (by omega : offset+i.val≠45678),
      if_neg (by omega : offset+i.val≠45679)]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  rw [actual,decode]
  simp only [projectedWord]
  have same : (phase+i.val)%4=(offset+i.val-143986)%4 := by omega
  rw [same]

private theorem window_0 : RangeMatches Artifact.commitCode_0_0 0 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_1 : RangeMatches Artifact.commitCode_0_1 512 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_2 : RangeMatches Artifact.commitCode_0_2 1024 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_3 : RangeMatches Artifact.commitCode_0_3 1536 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_4 : RangeMatches Artifact.commitCode_0_4 2048 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_5 : RangeMatches Artifact.commitCode_0_5 2560 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_6 : RangeMatches Artifact.commitCode_0_6 3072 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_7 : RangeMatches Artifact.commitCode_0_7 3584 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_8 : RangeMatches Artifact.commitCode_0_8 4096 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_9 : RangeMatches Artifact.commitCode_0_9 4608 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_10 : RangeMatches Artifact.commitCode_0_10 5120 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_11 : RangeMatches Artifact.commitCode_0_11 5632 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_12 : RangeMatches Artifact.commitCode_0_12 6144 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_13 : RangeMatches Artifact.commitCode_0_13 6656 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_14 : RangeMatches Artifact.commitCode_0_14 7168 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_15 : RangeMatches Artifact.commitCode_0_15 7680 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_16 : RangeMatches Artifact.commitCode_0_16 8192 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_17 : RangeMatches Artifact.commitCode_0_17 8704 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_18 : RangeMatches Artifact.commitCode_0_18 9216 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_19 : RangeMatches Artifact.commitCode_0_19 9728 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_20 : RangeMatches Artifact.commitCode_0_20 10240 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_21 : RangeMatches Artifact.commitCode_0_21 10752 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_22 : RangeMatches Artifact.commitCode_0_22 11264 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_23 : RangeMatches Artifact.commitCode_0_23 11776 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_24 : RangeMatches Artifact.commitCode_0_24 12288 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_25 : RangeMatches Artifact.commitCode_0_25 12800 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_26 : RangeMatches Artifact.commitCode_0_26 13312 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_27 : RangeMatches Artifact.commitCode_0_27 13824 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_28 : RangeMatches Artifact.commitCode_0_28 14336 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_29 : RangeMatches Artifact.commitCode_0_29 14848 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_30 : RangeMatches Artifact.commitCode_0_30 15360 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_31 : RangeMatches Artifact.commitCode_0_31 15872 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_32 : RangeMatches Artifact.commitCode_0_32 16384 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_33 : RangeMatches Artifact.commitCode_0_33 16896 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_34 : RangeMatches Artifact.commitCode_0_34 17408 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_35 : RangeMatches Artifact.commitCode_0_35 17920 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_36 : RangeMatches Artifact.commitCode_0_36 18432 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_37 : RangeMatches Artifact.commitCode_0_37 18944 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_38 : RangeMatches Artifact.commitCode_0_38 19456 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_39 : RangeMatches Artifact.commitCode_0_39 19968 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_40 : RangeMatches Artifact.commitCode_0_40 20480 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_41 : RangeMatches Artifact.commitCode_0_41 20992 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_42 : RangeMatches Artifact.commitCode_0_42 21504 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_43 : RangeMatches Artifact.commitCode_0_43 22016 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_44 : RangeMatches Artifact.commitCode_0_44 22528 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_45 : RangeMatches Artifact.commitCode_0_45 23040 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_46 : RangeMatches Artifact.commitCode_0_46 23552 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_47 : RangeMatches Artifact.commitCode_0_47 24064 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_48 : RangeMatches Artifact.commitCode_0_48 24576 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_49 : RangeMatches Artifact.commitCode_0_49 25088 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_50 : RangeMatches Artifact.commitCode_0_50 25600 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_51 : RangeMatches Artifact.commitCode_0_51 26112 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_52 : RangeMatches Artifact.commitCode_0_52 26624 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_53 : RangeMatches Artifact.commitCode_0_53 27136 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_54 : RangeMatches Artifact.commitCode_0_54 27648 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_55 : RangeMatches Artifact.commitCode_0_55 28160 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_56 : RangeMatches Artifact.commitCode_0_56 28672 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_57 : RangeMatches Artifact.commitCode_0_57 29184 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_58 : RangeMatches Artifact.commitCode_0_58 29696 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_59 : RangeMatches Artifact.commitCode_0_59 30208 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_60 : RangeMatches Artifact.commitCode_0_60 30720 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_61 : RangeMatches Artifact.commitCode_0_61 31232 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_62 : RangeMatches Artifact.commitCode_0_62 31744 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_63 : RangeMatches Artifact.commitCode_0_63 32256 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_64 : RangeMatches Artifact.commitCode_0_64 32768 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_65 : RangeMatches Artifact.commitCode_0_65 33280 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_66 : RangeMatches Artifact.commitCode_0_66 33792 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_67 : RangeMatches Artifact.commitCode_0_67 34304 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_68 : RangeMatches Artifact.commitCode_0_68 34816 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_69 : RangeMatches Artifact.commitCode_0_69 35328 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_70 : RangeMatches Artifact.commitCode_0_70 35840 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_71 : RangeMatches Artifact.commitCode_0_71 36352 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_72 : RangeMatches Artifact.commitCode_0_72 36864 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_73 : RangeMatches Artifact.commitCode_0_73 37376 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_74 : RangeMatches Artifact.commitCode_0_74 37888 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_75 : RangeMatches Artifact.commitCode_0_75 38400 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_76 : RangeMatches Artifact.commitCode_0_76 38912 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_77 : RangeMatches Artifact.commitCode_0_77 39424 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_78 : RangeMatches Artifact.commitCode_0_78 39936 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_79 : RangeMatches Artifact.commitCode_0_79 40448 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_80 : RangeMatches Artifact.commitCode_0_80 40960 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_81 : RangeMatches Artifact.commitCode_0_81 41472 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_82 : RangeMatches Artifact.commitCode_0_82 41984 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_83 : RangeMatches Artifact.commitCode_0_83 42496 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_84 : RangeMatches Artifact.commitCode_0_84 43008 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_85 : RangeMatches Artifact.commitCode_0_85 43520 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_86 : RangeMatches Artifact.commitCode_0_86 44032 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_87 : RangeMatches Artifact.commitCode_0_87 44544 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_88 : RangeMatches Artifact.commitCode_0_88 45056 := by
  intro i lower upper
  have inside := i.isLt
  omega

private theorem window_89 : RangeMatches Artifact.commitCode_0_89 45568 := by
  intro i lower upper
  fin_cases i <;> norm_num at lower <;> norm_num at upper <;> rfl

private theorem window_90 : RangeMatches Artifact.commitCode_0_90 46080 := by
  exact full_window _ 46080 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_91 : RangeMatches Artifact.commitCode_0_91 46592 := by
  exact full_window _ 46592 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_92 : RangeMatches Artifact.commitCode_0_92 47104 := by
  exact full_window _ 47104 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_93 : RangeMatches Artifact.commitCode_0_93 47616 := by
  exact full_window _ 47616 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_94 : RangeMatches Artifact.commitCode_0_94 48128 := by
  exact full_window _ 48128 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_95 : RangeMatches Artifact.commitCode_0_95 48640 := by
  exact full_window _ 48640 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_96 : RangeMatches Artifact.commitCode_0_96 49152 := by
  exact full_window _ 49152 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_97 : RangeMatches Artifact.commitCode_0_97 49664 := by
  exact full_window _ 49664 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_98 : RangeMatches Artifact.commitCode_0_98 50176 := by
  exact full_window _ 50176 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_99 : RangeMatches Artifact.commitCode_0_99 50688 := by
  exact full_window _ 50688 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_100 : RangeMatches Artifact.commitCode_0_100 51200 := by
  exact full_window _ 51200 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_101 : RangeMatches Artifact.commitCode_0_101 51712 := by
  exact full_window _ 51712 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_102 : RangeMatches Artifact.commitCode_0_102 52224 := by
  exact full_window _ 52224 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_103 : RangeMatches Artifact.commitCode_0_103 52736 := by
  exact full_window _ 52736 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_104 : RangeMatches Artifact.commitCode_0_104 53248 := by
  exact full_window _ 53248 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_105 : RangeMatches Artifact.commitCode_0_105 53760 := by
  exact full_window _ 53760 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_106 : RangeMatches Artifact.commitCode_0_106 54272 := by
  exact full_window _ 54272 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_107 : RangeMatches Artifact.commitCode_0_107 54784 := by
  exact full_window _ 54784 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_108 : RangeMatches Artifact.commitCode_0_108 55296 := by
  exact full_window _ 55296 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_109 : RangeMatches Artifact.commitCode_0_109 55808 := by
  exact full_window _ 55808 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_110 : RangeMatches Artifact.commitCode_0_110 56320 := by
  exact full_window _ 56320 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_111 : RangeMatches Artifact.commitCode_0_111 56832 := by
  exact full_window _ 56832 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_112 : RangeMatches Artifact.commitCode_0_112 57344 := by
  exact full_window _ 57344 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_113 : RangeMatches Artifact.commitCode_0_113 57856 := by
  exact full_window _ 57856 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_114 : RangeMatches Artifact.commitCode_0_114 58368 := by
  exact full_window _ 58368 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_115 : RangeMatches Artifact.commitCode_0_115 58880 := by
  exact full_window _ 58880 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_116 : RangeMatches Artifact.commitCode_0_116 59392 := by
  exact full_window _ 59392 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_117 : RangeMatches Artifact.commitCode_0_117 59904 := by
  exact full_window _ 59904 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_118 : RangeMatches Artifact.commitCode_0_118 60416 := by
  exact full_window _ 60416 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_119 : RangeMatches Artifact.commitCode_0_119 60928 := by
  exact full_window _ 60928 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_120 : RangeMatches Artifact.commitCode_0_120 61440 := by
  exact full_window _ 61440 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_121 : RangeMatches Artifact.commitCode_0_121 61952 := by
  exact full_window _ 61952 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_122 : RangeMatches Artifact.commitCode_0_122 62464 := by
  exact full_window _ 62464 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_123 : RangeMatches Artifact.commitCode_0_123 62976 := by
  exact full_window _ 62976 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_124 : RangeMatches Artifact.commitCode_0_124 63488 := by
  exact full_window _ 63488 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_125 : RangeMatches Artifact.commitCode_0_125 64000 := by
  exact full_window _ 64000 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_126 : RangeMatches Artifact.commitCode_0_126 64512 := by
  exact full_window _ 64512 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_127 : RangeMatches Artifact.commitCode_0_127 65024 := by
  exact full_window _ 65024 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_128 : RangeMatches Artifact.commitCode_0_128 65536 := by
  exact full_window _ 65536 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_129 : RangeMatches Artifact.commitCode_0_129 66048 := by
  exact full_window _ 66048 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_130 : RangeMatches Artifact.commitCode_0_130 66560 := by
  exact full_window _ 66560 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_131 : RangeMatches Artifact.commitCode_0_131 67072 := by
  exact full_window _ 67072 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_132 : RangeMatches Artifact.commitCode_0_132 67584 := by
  exact full_window _ 67584 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_133 : RangeMatches Artifact.commitCode_0_133 68096 := by
  exact full_window _ 68096 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_134 : RangeMatches Artifact.commitCode_0_134 68608 := by
  exact full_window _ 68608 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_135 : RangeMatches Artifact.commitCode_0_135 69120 := by
  exact full_window _ 69120 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_136 : RangeMatches Artifact.commitCode_0_136 69632 := by
  exact full_window _ 69632 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_137 : RangeMatches Artifact.commitCode_0_137 70144 := by
  exact full_window _ 70144 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_138 : RangeMatches Artifact.commitCode_0_138 70656 := by
  exact full_window _ 70656 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_139 : RangeMatches Artifact.commitCode_0_139 71168 := by
  exact full_window _ 71168 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_140 : RangeMatches Artifact.commitCode_0_140 71680 := by
  exact full_window _ 71680 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_141 : RangeMatches Artifact.commitCode_0_141 72192 := by
  exact full_window _ 72192 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_142 : RangeMatches Artifact.commitCode_0_142 72704 := by
  exact full_window _ 72704 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_143 : RangeMatches Artifact.commitCode_0_143 73216 := by
  exact full_window _ 73216 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_144 : RangeMatches Artifact.commitCode_0_144 73728 := by
  exact full_window _ 73728 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_145 : RangeMatches Artifact.commitCode_0_145 74240 := by
  exact full_window _ 74240 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_146 : RangeMatches Artifact.commitCode_0_146 74752 := by
  exact full_window _ 74752 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_147 : RangeMatches Artifact.commitCode_0_147 75264 := by
  exact full_window _ 75264 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_148 : RangeMatches Artifact.commitCode_0_148 75776 := by
  exact full_window _ 75776 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_149 : RangeMatches Artifact.commitCode_0_149 76288 := by
  exact full_window _ 76288 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_150 : RangeMatches Artifact.commitCode_0_150 76800 := by
  exact full_window _ 76800 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_151 : RangeMatches Artifact.commitCode_0_151 77312 := by
  exact full_window _ 77312 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_152 : RangeMatches Artifact.commitCode_0_152 77824 := by
  exact full_window _ 77824 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_153 : RangeMatches Artifact.commitCode_0_153 78336 := by
  exact full_window _ 78336 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_154 : RangeMatches Artifact.commitCode_0_154 78848 := by
  exact full_window _ 78848 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_155 : RangeMatches Artifact.commitCode_0_155 79360 := by
  exact full_window _ 79360 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_156 : RangeMatches Artifact.commitCode_0_156 79872 := by
  exact full_window _ 79872 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_157 : RangeMatches Artifact.commitCode_0_157 80384 := by
  exact full_window _ 80384 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_158 : RangeMatches Artifact.commitCode_0_158 80896 := by
  exact full_window _ 80896 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_159 : RangeMatches Artifact.commitCode_0_159 81408 := by
  exact full_window _ 81408 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_160 : RangeMatches Artifact.commitCode_0_160 81920 := by
  exact full_window _ 81920 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_161 : RangeMatches Artifact.commitCode_0_161 82432 := by
  exact full_window _ 82432 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_162 : RangeMatches Artifact.commitCode_0_162 82944 := by
  exact full_window _ 82944 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_163 : RangeMatches Artifact.commitCode_0_163 83456 := by
  exact full_window _ 83456 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_164 : RangeMatches Artifact.commitCode_0_164 83968 := by
  exact full_window _ 83968 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_165 : RangeMatches Artifact.commitCode_0_165 84480 := by
  exact full_window _ 84480 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_166 : RangeMatches Artifact.commitCode_0_166 84992 := by
  exact full_window _ 84992 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_167 : RangeMatches Artifact.commitCode_0_167 85504 := by
  exact full_window _ 85504 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_168 : RangeMatches Artifact.commitCode_0_168 86016 := by
  exact full_window _ 86016 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_169 : RangeMatches Artifact.commitCode_0_169 86528 := by
  exact full_window _ 86528 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_170 : RangeMatches Artifact.commitCode_0_170 87040 := by
  exact full_window _ 87040 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_171 : RangeMatches Artifact.commitCode_0_171 87552 := by
  exact full_window _ 87552 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_172 : RangeMatches Artifact.commitCode_0_172 88064 := by
  exact full_window _ 88064 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_173 : RangeMatches Artifact.commitCode_0_173 88576 := by
  exact full_window _ 88576 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_174 : RangeMatches Artifact.commitCode_0_174 89088 := by
  exact full_window _ 89088 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_175 : RangeMatches Artifact.commitCode_0_175 89600 := by
  exact full_window _ 89600 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_176 : RangeMatches Artifact.commitCode_0_176 90112 := by
  exact full_window _ 90112 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_177 : RangeMatches Artifact.commitCode_0_177 90624 := by
  exact full_window _ 90624 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_178 : RangeMatches Artifact.commitCode_0_178 91136 := by
  exact full_window _ 91136 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_179 : RangeMatches Artifact.commitCode_0_179 91648 := by
  exact full_window _ 91648 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_180 : RangeMatches Artifact.commitCode_0_180 92160 := by
  exact full_window _ 92160 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_181 : RangeMatches Artifact.commitCode_0_181 92672 := by
  exact full_window _ 92672 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_182 : RangeMatches Artifact.commitCode_0_182 93184 := by
  exact full_window _ 93184 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_183 : RangeMatches Artifact.commitCode_0_183 93696 := by
  exact full_window _ 93696 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_184 : RangeMatches Artifact.commitCode_0_184 94208 := by
  exact full_window _ 94208 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_185 : RangeMatches Artifact.commitCode_0_185 94720 := by
  exact full_window _ 94720 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_186 : RangeMatches Artifact.commitCode_0_186 95232 := by
  exact full_window _ 95232 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_187 : RangeMatches Artifact.commitCode_0_187 95744 := by
  exact full_window _ 95744 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_188 : RangeMatches Artifact.commitCode_0_188 96256 := by
  exact full_window _ 96256 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_189 : RangeMatches Artifact.commitCode_0_189 96768 := by
  exact full_window _ 96768 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_190 : RangeMatches Artifact.commitCode_0_190 97280 := by
  exact full_window _ 97280 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_191 : RangeMatches Artifact.commitCode_0_191 97792 := by
  exact full_window _ 97792 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_192 : RangeMatches Artifact.commitCode_0_192 98304 := by
  exact full_window _ 98304 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_193 : RangeMatches Artifact.commitCode_0_193 98816 := by
  exact full_window _ 98816 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_194 : RangeMatches Artifact.commitCode_0_194 99328 := by
  exact full_window _ 99328 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_195 : RangeMatches Artifact.commitCode_0_195 99840 := by
  exact full_window _ 99840 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_196 : RangeMatches Artifact.commitCode_0_196 100352 := by
  exact full_window _ 100352 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_197 : RangeMatches Artifact.commitCode_0_197 100864 := by
  exact full_window _ 100864 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_198 : RangeMatches Artifact.commitCode_0_198 101376 := by
  exact full_window _ 101376 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_199 : RangeMatches Artifact.commitCode_0_199 101888 := by
  exact full_window _ 101888 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_200 : RangeMatches Artifact.commitCode_0_200 102400 := by
  exact full_window _ 102400 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_201 : RangeMatches Artifact.commitCode_0_201 102912 := by
  exact full_window _ 102912 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_202 : RangeMatches Artifact.commitCode_0_202 103424 := by
  exact full_window _ 103424 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_203 : RangeMatches Artifact.commitCode_0_203 103936 := by
  exact full_window _ 103936 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_204 : RangeMatches Artifact.commitCode_0_204 104448 := by
  exact full_window _ 104448 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_205 : RangeMatches Artifact.commitCode_0_205 104960 := by
  exact full_window _ 104960 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_206 : RangeMatches Artifact.commitCode_0_206 105472 := by
  exact full_window _ 105472 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_207 : RangeMatches Artifact.commitCode_0_207 105984 := by
  exact full_window _ 105984 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_208 : RangeMatches Artifact.commitCode_0_208 106496 := by
  exact full_window _ 106496 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_209 : RangeMatches Artifact.commitCode_0_209 107008 := by
  exact full_window _ 107008 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_210 : RangeMatches Artifact.commitCode_0_210 107520 := by
  exact full_window _ 107520 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_211 : RangeMatches Artifact.commitCode_0_211 108032 := by
  exact full_window _ 108032 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_212 : RangeMatches Artifact.commitCode_0_212 108544 := by
  exact full_window _ 108544 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_213 : RangeMatches Artifact.commitCode_0_213 109056 := by
  exact full_window _ 109056 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_214 : RangeMatches Artifact.commitCode_0_214 109568 := by
  exact full_window _ 109568 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_215 : RangeMatches Artifact.commitCode_0_215 110080 := by
  exact full_window _ 110080 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_216 : RangeMatches Artifact.commitCode_0_216 110592 := by
  exact full_window _ 110592 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_217 : RangeMatches Artifact.commitCode_0_217 111104 := by
  exact full_window _ 111104 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_218 : RangeMatches Artifact.commitCode_0_218 111616 := by
  exact full_window _ 111616 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_219 : RangeMatches Artifact.commitCode_0_219 112128 := by
  exact full_window _ 112128 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_220 : RangeMatches Artifact.commitCode_0_220 112640 := by
  exact full_window _ 112640 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_221 : RangeMatches Artifact.commitCode_0_221 113152 := by
  exact full_window _ 113152 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_222 : RangeMatches Artifact.commitCode_0_222 113664 := by
  exact full_window _ 113664 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_223 : RangeMatches Artifact.commitCode_0_223 114176 := by
  exact full_window _ 114176 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_224 : RangeMatches Artifact.commitCode_0_224 114688 := by
  exact full_window _ 114688 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_225 : RangeMatches Artifact.commitCode_0_225 115200 := by
  exact full_window _ 115200 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_226 : RangeMatches Artifact.commitCode_0_226 115712 := by
  exact full_window _ 115712 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_227 : RangeMatches Artifact.commitCode_0_227 116224 := by
  exact full_window _ 116224 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_228 : RangeMatches Artifact.commitCode_0_228 116736 := by
  exact full_window _ 116736 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_229 : RangeMatches Artifact.commitCode_0_229 117248 := by
  exact full_window _ 117248 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_230 : RangeMatches Artifact.commitCode_0_230 117760 := by
  exact full_window _ 117760 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_231 : RangeMatches Artifact.commitCode_0_231 118272 := by
  exact full_window _ 118272 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_232 : RangeMatches Artifact.commitCode_0_232 118784 := by
  exact full_window _ 118784 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_233 : RangeMatches Artifact.commitCode_0_233 119296 := by
  exact full_window _ 119296 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_234 : RangeMatches Artifact.commitCode_0_234 119808 := by
  exact full_window _ 119808 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_235 : RangeMatches Artifact.commitCode_0_235 120320 := by
  exact full_window _ 120320 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_236 : RangeMatches Artifact.commitCode_0_236 120832 := by
  exact full_window _ 120832 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_237 : RangeMatches Artifact.commitCode_0_237 121344 := by
  exact full_window _ 121344 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_238 : RangeMatches Artifact.commitCode_0_238 121856 := by
  exact full_window _ 121856 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_239 : RangeMatches Artifact.commitCode_0_239 122368 := by
  exact full_window _ 122368 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_240 : RangeMatches Artifact.commitCode_0_240 122880 := by
  exact full_window _ 122880 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_241 : RangeMatches Artifact.commitCode_0_241 123392 := by
  exact full_window _ 123392 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_242 : RangeMatches Artifact.commitCode_0_242 123904 := by
  exact full_window _ 123904 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_243 : RangeMatches Artifact.commitCode_0_243 124416 := by
  exact full_window _ 124416 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_244 : RangeMatches Artifact.commitCode_0_244 124928 := by
  exact full_window _ 124928 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_245 : RangeMatches Artifact.commitCode_0_245 125440 := by
  exact full_window _ 125440 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_246 : RangeMatches Artifact.commitCode_0_246 125952 := by
  exact full_window _ 125952 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_247 : RangeMatches Artifact.commitCode_0_247 126464 := by
  exact full_window _ 126464 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_248 : RangeMatches Artifact.commitCode_0_248 126976 := by
  exact full_window _ 126976 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_249 : RangeMatches Artifact.commitCode_0_249 127488 := by
  exact full_window _ 127488 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_250 : RangeMatches Artifact.commitCode_0_250 128000 := by
  exact full_window _ 128000 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_251 : RangeMatches Artifact.commitCode_0_251 128512 := by
  exact full_window _ 128512 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_252 : RangeMatches Artifact.commitCode_0_252 129024 := by
  exact full_window _ 129024 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_253 : RangeMatches Artifact.commitCode_0_253 129536 := by
  exact full_window _ 129536 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_254 : RangeMatches Artifact.commitCode_0_254 130048 := by
  exact full_window _ 130048 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_255 : RangeMatches Artifact.commitCode_0_255 130560 := by
  exact full_window _ 130560 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_256 : RangeMatches Artifact.commitCode_0_256 131072 := by
  exact full_window _ 131072 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_257 : RangeMatches Artifact.commitCode_0_257 131584 := by
  exact full_window _ 131584 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_258 : RangeMatches Artifact.commitCode_0_258 132096 := by
  exact full_window _ 132096 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_259 : RangeMatches Artifact.commitCode_0_259 132608 := by
  exact full_window _ 132608 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_260 : RangeMatches Artifact.commitCode_0_260 133120 := by
  exact full_window _ 133120 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_261 : RangeMatches Artifact.commitCode_0_261 133632 := by
  exact full_window _ 133632 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_262 : RangeMatches Artifact.commitCode_0_262 134144 := by
  exact full_window _ 134144 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_263 : RangeMatches Artifact.commitCode_0_263 134656 := by
  exact full_window _ 134656 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_264 : RangeMatches Artifact.commitCode_0_264 135168 := by
  exact full_window _ 135168 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_265 : RangeMatches Artifact.commitCode_0_265 135680 := by
  exact full_window _ 135680 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_266 : RangeMatches Artifact.commitCode_0_266 136192 := by
  exact full_window _ 136192 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_267 : RangeMatches Artifact.commitCode_0_267 136704 := by
  exact full_window _ 136704 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_268 : RangeMatches Artifact.commitCode_0_268 137216 := by
  exact full_window _ 137216 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_269 : RangeMatches Artifact.commitCode_0_269 137728 := by
  exact full_window _ 137728 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_270 : RangeMatches Artifact.commitCode_0_270 138240 := by
  exact full_window _ 138240 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_271 : RangeMatches Artifact.commitCode_0_271 138752 := by
  exact full_window _ 138752 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_272 : RangeMatches Artifact.commitCode_0_272 139264 := by
  exact full_window _ 139264 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_273 : RangeMatches Artifact.commitCode_0_273 139776 := by
  exact full_window _ 139776 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_274 : RangeMatches Artifact.commitCode_0_274 140288 := by
  exact full_window _ 140288 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_275 : RangeMatches Artifact.commitCode_0_275 140800 := by
  exact full_window _ 140800 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_276 : RangeMatches Artifact.commitCode_0_276 141312 := by
  exact full_window _ 141312 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_277 : RangeMatches Artifact.commitCode_0_277 141824 := by
  exact full_window _ 141824 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_278 : RangeMatches Artifact.commitCode_0_278 142336 := by
  exact full_window _ 142336 2 (by decide) (by decide) (by decide) full_decode_2

private theorem window_279 : RangeMatches Artifact.commitCode_0_279 142848 := by
  exact full_window _ 142848 1 (by decide) (by decide) (by decide) full_decode_1

private theorem window_280 : RangeMatches Artifact.commitCode_0_280 143360 := by
  exact full_window _ 143360 0 (by decide) (by decide) (by decide) full_decode_0

private theorem window_281 : RangeMatches Artifact.commitCode_0_281 143872 := by
  intro i lower upper
  fin_cases i <;> norm_num at lower <;> norm_num at upper <;> rfl

private theorem window_282 : RangeMatches Artifact.commitCode_0_282 144384 := by
  exact projected_window _ 144384 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_283 : RangeMatches Artifact.commitCode_0_283 144896 := by
  exact projected_window _ 144896 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_284 : RangeMatches Artifact.commitCode_0_284 145408 := by
  exact projected_window _ 145408 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_285 : RangeMatches Artifact.commitCode_0_285 145920 := by
  exact projected_window _ 145920 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_286 : RangeMatches Artifact.commitCode_0_286 146432 := by
  exact projected_window _ 146432 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_287 : RangeMatches Artifact.commitCode_0_287 146944 := by
  exact projected_window _ 146944 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_288 : RangeMatches Artifact.commitCode_0_288 147456 := by
  exact projected_window _ 147456 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_289 : RangeMatches Artifact.commitCode_0_289 147968 := by
  exact projected_window _ 147968 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_290 : RangeMatches Artifact.commitCode_0_290 148480 := by
  exact projected_window _ 148480 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_291 : RangeMatches Artifact.commitCode_0_291 148992 := by
  exact projected_window _ 148992 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_292 : RangeMatches Artifact.commitCode_0_292 149504 := by
  exact projected_window _ 149504 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_293 : RangeMatches Artifact.commitCode_0_293 150016 := by
  exact projected_window _ 150016 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_294 : RangeMatches Artifact.commitCode_0_294 150528 := by
  exact projected_window _ 150528 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_295 : RangeMatches Artifact.commitCode_0_295 151040 := by
  exact projected_window _ 151040 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_296 : RangeMatches Artifact.commitCode_0_296 151552 := by
  exact projected_window _ 151552 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_297 : RangeMatches Artifact.commitCode_0_297 152064 := by
  exact projected_window _ 152064 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_298 : RangeMatches Artifact.commitCode_0_298 152576 := by
  exact projected_window _ 152576 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_299 : RangeMatches Artifact.commitCode_0_299 153088 := by
  exact projected_window _ 153088 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_300 : RangeMatches Artifact.commitCode_0_300 153600 := by
  exact projected_window _ 153600 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_301 : RangeMatches Artifact.commitCode_0_301 154112 := by
  exact projected_window _ 154112 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_302 : RangeMatches Artifact.commitCode_0_302 154624 := by
  exact projected_window _ 154624 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_303 : RangeMatches Artifact.commitCode_0_303 155136 := by
  exact projected_window _ 155136 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_304 : RangeMatches Artifact.commitCode_0_304 155648 := by
  exact projected_window _ 155648 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_305 : RangeMatches Artifact.commitCode_0_305 156160 := by
  exact projected_window _ 156160 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_306 : RangeMatches Artifact.commitCode_0_306 156672 := by
  exact projected_window _ 156672 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_307 : RangeMatches Artifact.commitCode_0_307 157184 := by
  exact projected_window _ 157184 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_308 : RangeMatches Artifact.commitCode_0_308 157696 := by
  exact projected_window _ 157696 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_309 : RangeMatches Artifact.commitCode_0_309 158208 := by
  exact projected_window _ 158208 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_310 : RangeMatches Artifact.commitCode_0_310 158720 := by
  exact projected_window _ 158720 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_311 : RangeMatches Artifact.commitCode_0_311 159232 := by
  exact projected_window _ 159232 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_312 : RangeMatches Artifact.commitCode_0_312 159744 := by
  exact projected_window _ 159744 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_313 : RangeMatches Artifact.commitCode_0_313 160256 := by
  exact projected_window _ 160256 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_314 : RangeMatches Artifact.commitCode_0_314 160768 := by
  exact projected_window _ 160768 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_315 : RangeMatches Artifact.commitCode_0_315 161280 := by
  exact projected_window _ 161280 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_316 : RangeMatches Artifact.commitCode_0_316 161792 := by
  exact projected_window _ 161792 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_317 : RangeMatches Artifact.commitCode_0_317 162304 := by
  exact projected_window _ 162304 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_318 : RangeMatches Artifact.commitCode_0_318 162816 := by
  exact projected_window _ 162816 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_319 : RangeMatches Artifact.commitCode_0_319 163328 := by
  exact projected_window _ 163328 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_320 : RangeMatches Artifact.commitCode_0_320 163840 := by
  exact projected_window _ 163840 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_321 : RangeMatches Artifact.commitCode_0_321 164352 := by
  exact projected_window _ 164352 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_322 : RangeMatches Artifact.commitCode_0_322 164864 := by
  exact projected_window _ 164864 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_323 : RangeMatches Artifact.commitCode_0_323 165376 := by
  exact projected_window _ 165376 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_324 : RangeMatches Artifact.commitCode_0_324 165888 := by
  exact projected_window _ 165888 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_325 : RangeMatches Artifact.commitCode_0_325 166400 := by
  exact projected_window _ 166400 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_326 : RangeMatches Artifact.commitCode_0_326 166912 := by
  exact projected_window _ 166912 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_327 : RangeMatches Artifact.commitCode_0_327 167424 := by
  exact projected_window _ 167424 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_328 : RangeMatches Artifact.commitCode_0_328 167936 := by
  exact projected_window _ 167936 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_329 : RangeMatches Artifact.commitCode_0_329 168448 := by
  exact projected_window _ 168448 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_330 : RangeMatches Artifact.commitCode_0_330 168960 := by
  exact projected_window _ 168960 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_331 : RangeMatches Artifact.commitCode_0_331 169472 := by
  exact projected_window _ 169472 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_332 : RangeMatches Artifact.commitCode_0_332 169984 := by
  exact projected_window _ 169984 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_333 : RangeMatches Artifact.commitCode_0_333 170496 := by
  exact projected_window _ 170496 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_334 : RangeMatches Artifact.commitCode_0_334 171008 := by
  exact projected_window _ 171008 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_335 : RangeMatches Artifact.commitCode_0_335 171520 := by
  exact projected_window _ 171520 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_336 : RangeMatches Artifact.commitCode_0_336 172032 := by
  exact projected_window _ 172032 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_337 : RangeMatches Artifact.commitCode_0_337 172544 := by
  exact projected_window _ 172544 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_338 : RangeMatches Artifact.commitCode_0_338 173056 := by
  exact projected_window _ 173056 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_339 : RangeMatches Artifact.commitCode_0_339 173568 := by
  exact projected_window _ 173568 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_340 : RangeMatches Artifact.commitCode_0_340 174080 := by
  exact projected_window _ 174080 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_341 : RangeMatches Artifact.commitCode_0_341 174592 := by
  exact projected_window _ 174592 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_342 : RangeMatches Artifact.commitCode_0_342 175104 := by
  exact projected_window _ 175104 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_343 : RangeMatches Artifact.commitCode_0_343 175616 := by
  exact projected_window _ 175616 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_344 : RangeMatches Artifact.commitCode_0_344 176128 := by
  exact projected_window _ 176128 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_345 : RangeMatches Artifact.commitCode_0_345 176640 := by
  exact projected_window _ 176640 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_346 : RangeMatches Artifact.commitCode_0_346 177152 := by
  exact projected_window _ 177152 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_347 : RangeMatches Artifact.commitCode_0_347 177664 := by
  exact projected_window _ 177664 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_348 : RangeMatches Artifact.commitCode_0_348 178176 := by
  exact projected_window _ 178176 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_349 : RangeMatches Artifact.commitCode_0_349 178688 := by
  exact projected_window _ 178688 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_350 : RangeMatches Artifact.commitCode_0_350 179200 := by
  exact projected_window _ 179200 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_351 : RangeMatches Artifact.commitCode_0_351 179712 := by
  exact projected_window _ 179712 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_352 : RangeMatches Artifact.commitCode_0_352 180224 := by
  exact projected_window _ 180224 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_353 : RangeMatches Artifact.commitCode_0_353 180736 := by
  exact projected_window _ 180736 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_354 : RangeMatches Artifact.commitCode_0_354 181248 := by
  exact projected_window _ 181248 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_355 : RangeMatches Artifact.commitCode_0_355 181760 := by
  exact projected_window _ 181760 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_356 : RangeMatches Artifact.commitCode_0_356 182272 := by
  exact projected_window _ 182272 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_357 : RangeMatches Artifact.commitCode_0_357 182784 := by
  exact projected_window _ 182784 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_358 : RangeMatches Artifact.commitCode_0_358 183296 := by
  exact projected_window _ 183296 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_359 : RangeMatches Artifact.commitCode_0_359 183808 := by
  exact projected_window _ 183808 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_360 : RangeMatches Artifact.commitCode_0_360 184320 := by
  exact projected_window _ 184320 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_361 : RangeMatches Artifact.commitCode_0_361 184832 := by
  exact projected_window _ 184832 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_362 : RangeMatches Artifact.commitCode_0_362 185344 := by
  exact projected_window _ 185344 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_363 : RangeMatches Artifact.commitCode_0_363 185856 := by
  exact projected_window _ 185856 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_364 : RangeMatches Artifact.commitCode_0_364 186368 := by
  exact projected_window _ 186368 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_365 : RangeMatches Artifact.commitCode_0_365 186880 := by
  exact projected_window _ 186880 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_366 : RangeMatches Artifact.commitCode_0_366 187392 := by
  exact projected_window _ 187392 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_367 : RangeMatches Artifact.commitCode_0_367 187904 := by
  exact projected_window _ 187904 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_368 : RangeMatches Artifact.commitCode_0_368 188416 := by
  exact projected_window _ 188416 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_369 : RangeMatches Artifact.commitCode_0_369 188928 := by
  exact projected_window _ 188928 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_370 : RangeMatches Artifact.commitCode_0_370 189440 := by
  exact projected_window _ 189440 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_371 : RangeMatches Artifact.commitCode_0_371 189952 := by
  exact projected_window _ 189952 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_372 : RangeMatches Artifact.commitCode_0_372 190464 := by
  exact projected_window _ 190464 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_373 : RangeMatches Artifact.commitCode_0_373 190976 := by
  exact projected_window _ 190976 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_374 : RangeMatches Artifact.commitCode_0_374 191488 := by
  exact projected_window _ 191488 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_375 : RangeMatches Artifact.commitCode_0_375 192000 := by
  exact projected_window _ 192000 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_376 : RangeMatches Artifact.commitCode_0_376 192512 := by
  exact projected_window _ 192512 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_377 : RangeMatches Artifact.commitCode_0_377 193024 := by
  exact projected_window _ 193024 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_378 : RangeMatches Artifact.commitCode_0_378 193536 := by
  exact projected_window _ 193536 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_379 : RangeMatches Artifact.commitCode_0_379 194048 := by
  exact projected_window _ 194048 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_380 : RangeMatches Artifact.commitCode_0_380 194560 := by
  exact projected_window _ 194560 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_381 : RangeMatches Artifact.commitCode_0_381 195072 := by
  exact projected_window _ 195072 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_382 : RangeMatches Artifact.commitCode_0_382 195584 := by
  exact projected_window _ 195584 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_383 : RangeMatches Artifact.commitCode_0_383 196096 := by
  exact projected_window _ 196096 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_384 : RangeMatches Artifact.commitCode_0_384 196608 := by
  exact projected_window _ 196608 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_385 : RangeMatches Artifact.commitCode_0_385 197120 := by
  exact projected_window _ 197120 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_386 : RangeMatches Artifact.commitCode_0_386 197632 := by
  exact projected_window _ 197632 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_387 : RangeMatches Artifact.commitCode_0_387 198144 := by
  exact projected_window _ 198144 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_388 : RangeMatches Artifact.commitCode_0_388 198656 := by
  exact projected_window _ 198656 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_389 : RangeMatches Artifact.commitCode_0_389 199168 := by
  exact projected_window _ 199168 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_390 : RangeMatches Artifact.commitCode_0_390 199680 := by
  exact projected_window _ 199680 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_391 : RangeMatches Artifact.commitCode_0_391 200192 := by
  exact projected_window _ 200192 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_392 : RangeMatches Artifact.commitCode_0_392 200704 := by
  exact projected_window _ 200704 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_393 : RangeMatches Artifact.commitCode_0_393 201216 := by
  exact projected_window _ 201216 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_394 : RangeMatches Artifact.commitCode_0_394 201728 := by
  exact projected_window _ 201728 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_395 : RangeMatches Artifact.commitCode_0_395 202240 := by
  exact projected_window _ 202240 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_396 : RangeMatches Artifact.commitCode_0_396 202752 := by
  exact projected_window _ 202752 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_397 : RangeMatches Artifact.commitCode_0_397 203264 := by
  exact projected_window _ 203264 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_398 : RangeMatches Artifact.commitCode_0_398 203776 := by
  exact projected_window _ 203776 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_399 : RangeMatches Artifact.commitCode_0_399 204288 := by
  exact projected_window _ 204288 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_400 : RangeMatches Artifact.commitCode_0_400 204800 := by
  exact projected_window _ 204800 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_401 : RangeMatches Artifact.commitCode_0_401 205312 := by
  exact projected_window _ 205312 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_402 : RangeMatches Artifact.commitCode_0_402 205824 := by
  exact projected_window _ 205824 2 (by decide) (by decide) (by decide) projected_decode_2

private theorem window_403 : RangeMatches Artifact.commitCode_0_403 206336 := by
  intro i lower upper
  fin_cases i <;> norm_num at lower <;> norm_num at upper <;> rfl

private theorem window_404 : RangeMatches Artifact.commitCode_0_404 206848 := by
  intro i lower upper
  omega

private theorem window_405 : RangeMatches Artifact.commitCode_0_405 207360 := by
  intro i lower upper
  omega

private theorem window_406 : RangeMatches Artifact.commitCode_0_406 207872 := by
  intro i lower upper
  omega

private theorem window_407 : RangeMatches Artifact.commitCode_0_407 208384 := by
  intro i lower upper
  omega

private theorem window_408 : RangeMatches Artifact.commitCode_0_408 208896 := by
  intro i lower upper
  omega

private theorem window_409 : RangeMatches Artifact.commitCode_0_409 209408 := by
  intro i lower upper
  omega

private theorem window_410 : RangeMatches Artifact.commitCode_0_410 209920 := by
  intro i lower upper
  omega

private theorem window_411 : RangeMatches Artifact.commitCode_0_411 210432 := by
  intro i lower upper
  omega

private theorem window_412 : RangeMatches Artifact.commitCode_0_412 210944 := by
  intro i lower upper
  omega

private theorem window_413 : RangeMatches Artifact.commitCode_0_413 211456 := by
  intro i lower upper
  omega

private theorem window_414 : RangeMatches Artifact.commitCode_0_414 211968 := by
  intro i lower upper
  omega

private theorem window_415 : RangeMatches Artifact.commitCode_0_415 212480 := by
  intro i lower upper
  omega

private theorem window_416 : RangeMatches Artifact.commitCode_0_416 212992 := by
  intro i lower upper
  omega

private theorem window_417 : RangeMatches Artifact.commitCode_0_417 213504 := by
  intro i lower upper
  omega

private theorem window_418 : RangeMatches Artifact.commitCode_0_418 214016 := by
  intro i lower upper
  omega

private theorem window_419 : RangeMatches Artifact.commitCode_0_419 214528 := by
  intro i lower upper
  omega

private theorem window_420 : RangeMatches Artifact.commitCode_0_420 215040 := by
  intro i lower upper
  omega

private theorem window_421 : RangeMatches Artifact.commitCode_0_421 215552 := by
  intro i lower upper
  omega

private theorem window_422 : RangeMatches Artifact.commitCode_0_422 216064 := by
  intro i lower upper
  omega

private theorem window_423 : RangeMatches Artifact.commitCode_0_423 216576 := by
  intro i lower upper
  omega

private theorem window_424 : RangeMatches Artifact.commitCode_0_424 217088 := by
  intro i lower upper
  omega

private theorem window_425 : RangeMatches Artifact.commitCode_0_425 217600 := by
  intro i lower upper
  omega

private theorem window_426 : RangeMatches Artifact.commitCode_0_426 218112 := by
  intro i lower upper
  omega

private theorem window_427 : RangeMatches Artifact.commitCode_0_427 218624 := by
  intro i lower upper
  omega

private theorem window_428 : RangeMatches Artifact.commitCode_0_428 219136 := by
  intro i lower upper
  omega

private theorem window_429 : RangeMatches Artifact.commitCode_0_429 219648 := by
  intro i lower upper
  omega

private theorem window_430 : RangeMatches Artifact.commitCode_0_430 220160 := by
  intro i lower upper
  omega

private theorem window_431 : RangeMatches Artifact.commitCode_0_431 220672 := by
  intro i lower upper
  omega

private theorem window_432 : RangeMatches Artifact.commitCode_0_432 221184 := by
  intro i lower upper
  omega

private theorem window_433 : RangeMatches Artifact.commitCode_0_433 221696 := by
  intro i lower upper
  omega

private theorem window_434 : RangeMatches Artifact.commitCode_0_434 222208 := by
  intro i lower upper
  omega

private theorem window_435 : RangeMatches Artifact.commitCode_0_435 222720 := by
  intro i lower upper
  omega

private theorem window_436 : RangeMatches Artifact.commitCode_0_436 223232 := by
  intro i lower upper
  omega

private theorem window_437 : RangeMatches Artifact.commitCode_0_437 223744 := by
  intro i lower upper
  omega

private theorem window_438 : RangeMatches Artifact.commitCode_0_438 224256 := by
  intro i lower upper
  omega

private theorem window_439 : RangeMatches Artifact.commitCode_0_439 224768 := by
  intro i lower upper
  omega

private theorem window_440 : RangeMatches Artifact.commitCode_0_440 225280 := by
  intro i lower upper
  omega

private theorem window_441 : RangeMatches Artifact.commitCode_0_441 225792 := by
  intro i lower upper
  omega

private theorem window_442 : RangeMatches Artifact.commitCode_0_442 226304 := by
  intro i lower upper
  omega

private theorem window_443 : RangeMatches Artifact.commitCode_0_443 226816 := by
  intro i lower upper
  omega

private theorem window_444 : RangeMatches Artifact.commitCode_0_444 227328 := by
  intro i lower upper
  omega

private theorem window_445 : RangeMatches Artifact.commitCode_0_445 227840 := by
  intro i lower upper
  omega

private theorem window_446 : RangeMatches Artifact.commitCode_0_446 228352 := by
  intro i lower upper
  omega

private theorem window_447 : RangeMatches Artifact.commitCode_0_447 228864 := by
  intro i lower upper
  omega

private theorem window_448 : RangeMatches Artifact.commitCode_0_448 229376 := by
  intro i lower upper
  omega

private theorem window_449 : RangeMatches Artifact.commitCode_0_449 229888 := by
  intro i lower upper
  omega

private theorem window_450 : RangeMatches Artifact.commitCode_0_450 230400 := by
  intro i lower upper
  omega

private theorem window_451 : RangeMatches Artifact.commitCode_0_451 230912 := by
  intro i lower upper
  omega

private theorem window_452 : RangeMatches Artifact.commitCode_0_452 231424 := by
  intro i lower upper
  omega

private theorem window_453 : RangeMatches Artifact.commitCode_0_453 231936 := by
  intro i lower upper
  omega

private theorem window_454 : RangeMatches Artifact.commitCode_0_454 232448 := by
  intro i lower upper
  omega

private theorem window_455 : RangeMatches Artifact.commitCode_0_455 232960 := by
  intro i lower upper
  omega

private theorem image_matches : RangeMatches Artifact.commitCode 0 := by
  exact (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_0 window_1) (range_join _ _ _ window_2 window_3)) (range_join _ _ _ (range_join _ _ _ window_4 window_5) (range_join _ _ _ window_6 window_7))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_8 window_9) (range_join _ _ _ window_10 window_11)) (range_join _ _ _ (range_join _ _ _ window_12 window_13) (range_join _ _ _ window_14 window_15)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_16 window_17) (range_join _ _ _ window_18 window_19)) (range_join _ _ _ (range_join _ _ _ window_20 window_21) (range_join _ _ _ window_22 window_23))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_24 window_25) (range_join _ _ _ window_26 window_27)) (range_join _ _ _ (range_join _ _ _ window_28 window_29) (range_join _ _ _ window_30 window_31))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_32 window_33) (range_join _ _ _ window_34 window_35)) (range_join _ _ _ (range_join _ _ _ window_36 window_37) (range_join _ _ _ window_38 window_39))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_40 window_41) (range_join _ _ _ window_42 window_43)) (range_join _ _ _ (range_join _ _ _ window_44 window_45) (range_join _ _ _ window_46 window_47)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_48 window_49) (range_join _ _ _ window_50 window_51)) (range_join _ _ _ (range_join _ _ _ window_52 window_53) (range_join _ _ _ window_54 window_55))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_56 window_57) (range_join _ _ _ window_58 window_59)) (range_join _ _ _ (range_join _ _ _ window_60 window_61) (range_join _ _ _ window_62 window_63)))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_64 window_65) (range_join _ _ _ window_66 window_67)) (range_join _ _ _ (range_join _ _ _ window_68 window_69) (range_join _ _ _ window_70 window_71))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_72 window_73) (range_join _ _ _ window_74 window_75)) (range_join _ _ _ (range_join _ _ _ window_76 window_77) (range_join _ _ _ window_78 window_79)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_80 window_81) (range_join _ _ _ window_82 window_83)) (range_join _ _ _ (range_join _ _ _ window_84 window_85) (range_join _ _ _ window_86 window_87))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_88 window_89) (range_join _ _ _ window_90 window_91)) (range_join _ _ _ (range_join _ _ _ window_92 window_93) (range_join _ _ _ window_94 window_95))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_96 window_97) (range_join _ _ _ window_98 window_99)) (range_join _ _ _ (range_join _ _ _ window_100 window_101) (range_join _ _ _ window_102 window_103))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_104 window_105) (range_join _ _ _ window_106 window_107)) (range_join _ _ _ (range_join _ _ _ window_108 window_109) (range_join _ _ _ window_110 window_111)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_112 window_113) (range_join _ _ _ window_114 window_115)) (range_join _ _ _ (range_join _ _ _ window_116 window_117) (range_join _ _ _ window_118 window_119))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_120 window_121) (range_join _ _ _ window_122 window_123)) (range_join _ _ _ (range_join _ _ _ window_124 window_125) (range_join _ _ _ window_126 window_127))))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_128 window_129) (range_join _ _ _ window_130 window_131)) (range_join _ _ _ (range_join _ _ _ window_132 window_133) (range_join _ _ _ window_134 window_135))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_136 window_137) (range_join _ _ _ window_138 window_139)) (range_join _ _ _ (range_join _ _ _ window_140 window_141) (range_join _ _ _ window_142 window_143)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_144 window_145) (range_join _ _ _ window_146 window_147)) (range_join _ _ _ (range_join _ _ _ window_148 window_149) (range_join _ _ _ window_150 window_151))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_152 window_153) (range_join _ _ _ window_154 window_155)) (range_join _ _ _ (range_join _ _ _ window_156 window_157) (range_join _ _ _ window_158 window_159))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_160 window_161) (range_join _ _ _ window_162 window_163)) (range_join _ _ _ (range_join _ _ _ window_164 window_165) (range_join _ _ _ window_166 window_167))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_168 window_169) (range_join _ _ _ window_170 window_171)) (range_join _ _ _ (range_join _ _ _ window_172 window_173) (range_join _ _ _ window_174 window_175)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_176 window_177) (range_join _ _ _ window_178 window_179)) (range_join _ _ _ (range_join _ _ _ window_180 window_181) (range_join _ _ _ window_182 window_183))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_184 window_185) (range_join _ _ _ window_186 window_187)) (range_join _ _ _ (range_join _ _ _ window_188 window_189) (range_join _ _ _ window_190 window_191)))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_192 window_193) (range_join _ _ _ window_194 window_195)) (range_join _ _ _ (range_join _ _ _ window_196 window_197) (range_join _ _ _ window_198 window_199))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_200 window_201) (range_join _ _ _ window_202 window_203)) (range_join _ _ _ (range_join _ _ _ window_204 window_205) (range_join _ _ _ window_206 window_207)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_208 window_209) (range_join _ _ _ window_210 window_211)) (range_join _ _ _ (range_join _ _ _ window_212 window_213) (range_join _ _ _ window_214 window_215))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_216 window_217) (range_join _ _ _ window_218 window_219)) (range_join _ _ _ (range_join _ _ _ window_220 window_221) (range_join _ _ _ window_222 window_223))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_224 window_225) (range_join _ _ _ window_226 window_227)) (range_join _ _ _ (range_join _ _ _ window_228 window_229) (range_join _ _ _ window_230 window_231))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_232 window_233) (range_join _ _ _ window_234 window_235)) (range_join _ _ _ (range_join _ _ _ window_236 window_237) (range_join _ _ _ window_238 window_239)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_240 window_241) (range_join _ _ _ window_242 window_243)) (range_join _ _ _ (range_join _ _ _ window_244 window_245) (range_join _ _ _ window_246 window_247))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_248 window_249) (range_join _ _ _ window_250 window_251)) (range_join _ _ _ (range_join _ _ _ window_252 window_253) (range_join _ _ _ window_254 window_255)))))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_256 window_257) (range_join _ _ _ window_258 window_259)) (range_join _ _ _ (range_join _ _ _ window_260 window_261) (range_join _ _ _ window_262 window_263))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_264 window_265) (range_join _ _ _ window_266 window_267)) (range_join _ _ _ (range_join _ _ _ window_268 window_269) (range_join _ _ _ window_270 window_271)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_272 window_273) (range_join _ _ _ window_274 window_275)) (range_join _ _ _ (range_join _ _ _ window_276 window_277) (range_join _ _ _ window_278 window_279))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_280 window_281) (range_join _ _ _ window_282 window_283)) (range_join _ _ _ (range_join _ _ _ window_284 window_285) (range_join _ _ _ window_286 window_287))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_288 window_289) (range_join _ _ _ window_290 window_291)) (range_join _ _ _ (range_join _ _ _ window_292 window_293) (range_join _ _ _ window_294 window_295))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_296 window_297) (range_join _ _ _ window_298 window_299)) (range_join _ _ _ (range_join _ _ _ window_300 window_301) (range_join _ _ _ window_302 window_303)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_304 window_305) (range_join _ _ _ window_306 window_307)) (range_join _ _ _ (range_join _ _ _ window_308 window_309) (range_join _ _ _ window_310 window_311))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_312 window_313) (range_join _ _ _ window_314 window_315)) (range_join _ _ _ (range_join _ _ _ window_316 window_317) (range_join _ _ _ window_318 window_319)))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_320 window_321) (range_join _ _ _ window_322 window_323)) (range_join _ _ _ (range_join _ _ _ window_324 window_325) (range_join _ _ _ window_326 window_327))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_328 window_329) (range_join _ _ _ window_330 window_331)) (range_join _ _ _ (range_join _ _ _ window_332 window_333) (range_join _ _ _ window_334 window_335)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_336 window_337) (range_join _ _ _ window_338 window_339)) (range_join _ _ _ (range_join _ _ _ window_340 window_341) (range_join _ _ _ window_342 window_343))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_344 window_345) (range_join _ _ _ window_346 window_347)) (range_join _ _ _ (range_join _ _ _ window_348 window_349) (range_join _ _ _ window_350 window_351))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_352 window_353) (range_join _ _ _ window_354 window_355)) (range_join _ _ _ (range_join _ _ _ window_356 window_357) (range_join _ _ _ window_358 window_359))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_360 window_361) (range_join _ _ _ window_362 window_363)) (range_join _ _ _ (range_join _ _ _ window_364 window_365) (range_join _ _ _ window_366 window_367)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_368 window_369) (range_join _ _ _ window_370 window_371)) (range_join _ _ _ (range_join _ _ _ window_372 window_373) (range_join _ _ _ window_374 window_375))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_376 window_377) (range_join _ _ _ window_378 window_379)) (range_join _ _ _ (range_join _ _ _ window_380 window_381) (range_join _ _ _ window_382 window_383))))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_384 window_385) (range_join _ _ _ window_386 window_387)) (range_join _ _ _ (range_join _ _ _ window_388 window_389) (range_join _ _ _ window_390 window_391))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_392 window_393) (range_join _ _ _ window_394 window_395)) (range_join _ _ _ (range_join _ _ _ window_396 window_397) (range_join _ _ _ window_398 window_399)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_400 window_401) (range_join _ _ _ window_402 window_403)) (range_join _ _ _ (range_join _ _ _ window_404 window_405) (range_join _ _ _ window_406 window_407))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_408 window_409) (range_join _ _ _ window_410 window_411)) (range_join _ _ _ (range_join _ _ _ window_412 window_413) (range_join _ _ _ window_414 window_415))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_416 window_417) (range_join _ _ _ window_418 window_419)) (range_join _ _ _ (range_join _ _ _ window_420 window_421) (range_join _ _ _ window_422 window_423))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_424 window_425) (range_join _ _ _ window_426 window_427)) (range_join _ _ _ (range_join _ _ _ window_428 window_429) (range_join _ _ _ window_430 window_431)))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_432 window_433) (range_join _ _ _ window_434 window_435)) (range_join _ _ _ (range_join _ _ _ window_436 window_437) (range_join _ _ _ window_438 window_439))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_440 window_441) (range_join _ _ _ window_442 window_443)) (range_join _ _ _ (range_join _ _ _ window_444 window_445) (range_join _ _ _ window_446 window_447)))))) (range_join _ _ _ (range_join _ _ _ (range_join _ _ _ window_448 window_449) (range_join _ _ _ window_450 window_451)) (range_join _ _ _ (range_join _ _ _ window_452 window_453) (range_join _ _ _ window_454 window_455))))))

attribute [local irreducible] ArtifactEncoding.decode

def packedWideCommitImage : Image :=
  ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩

theorem packed_manifest_image : packedWideCommitImage = Artifact.submission.image .commit := by
  simp only [packedWideCommitImage,Artifact.submission]

private theorem wide_commit_code :
    packedWideCommitImage.code = ArtifactEncoding.decode 32 Artifact.commitCode := by
  simp only [packedWideCommitImage]

theorem packed_index_fetch (state : MachineState) (index : Nat)
    (point : state.pc=BitVec.ofNat 64 (4096+4*index))
    (lower : (45677 : Nat) ≤ index) (upper : index < 206835) :
    fetch packedWideCommitImage state=decodeInstruction (expectedWord index) := by
  have pc : state.pc.toNat=4096+4*index := by
    rw [point,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inPacked : index<233357 := by omega
  have packed := image_matches ⟨index,inPacked⟩
    (by simpa only [Nat.zero_add,Fin.val_mk] using lower)
    (by simpa only [Nat.zero_add,Fin.val_mk] using upper)
  have word : packedWideCommitImage.code.getD index 0 = expectedWord index := by
    rw [wide_commit_code,ArtifactEncoding.getD_decode _ _ _ inPacked]
    simpa only [Nat.zero_add] using packed
  have inside : index<packedWideCommitImage.code.length := by
    rw [wide_commit_code,ArtifactEncoding.length_decode]
    exact inPacked
  have atIndex : packedWideCommitImage.code[index]? = some (expectedWord index) := by
    rw [List.getElem?_eq_getElem inside,←List.getD_eq_getElem _ _ inside,word]
  rw [fetch,pc,if_pos (by omega),
    show (4096+4*index-4096)/4=index by omega,atIndex]



private theorem mixed_full_opcode (state : MachineState) (slot : Nat)
    (bounded : slot<32768) (part : Fin 3)
    (pc : state.pc=FullWidth.parentPC 186816 slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (fullWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(45680+3*slot+part.val)) := by
    rw [pc,FullWidth.parentPC]
    change BitVec.ofNat 64 186816+BitVec.ofNat 64 (12*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (45680+3*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rw [if_pos (by omega)]
  simp only [fullWord]
  have phase : ((45680+3*slot+part.val)-45680)%3=part.val%3 := by omega
  rw [phase]

private theorem mixed_projected_opcode (state : MachineState) (slot : Nat)
    (bounded : slot<15709) (part : Fin 4)
    (pc : state.pc=packedParentPC 580040 slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (projectedWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(143986+4*slot+part.val)) := by
    rw [pc,packedParentPC]
    change BitVec.ofNat 64 580040+BitVec.ofNat 64 (16*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (143986+4*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  simp only [projectedWord]
  have phase : ((143986+4*slot+part.val)-143986)%4=part.val%4 := by omega
  rw [phase]

theorem mixed_full_words (slot : Nat) (bounded : slot<32768) :
    FullWidth.ParentFetched packedWideCommitImage (FullWidth.parentPC 186816 slot) := by
  intro state
  refine ⟨fun pc => ?_,fun pc => ?_,fun pc => ?_⟩
  · exact mixed_full_opcode state slot bounded 0 (by simpa using pc)
  · exact mixed_full_opcode state slot bounded 1 pc
  · exact mixed_full_opcode state slot bounded 2 pc

theorem mixed_projected_words (slot : Nat) (bounded : slot<15709) :
    PackedParentWordsAt packedWideCommitImage (packedParentPC 580040 slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · exact mixed_projected_opcode state slot bounded 0 (by simpa using pc)
  · exact mixed_projected_opcode state slot bounded 1 pc
  · exact mixed_projected_opcode state slot bounded 2 pc
  · exact mixed_projected_opcode state slot bounded 3 pc

def mixedFullControl : FullWidth.ParentControl packedWideCommitImage 186816 32768 where
  backOffset := 1703932
  backTarget := by decide
  branch state pc := packed_index_fetch state 143984 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 143985 pc (by decide) (by decide)

def mixedProjectedControl : PackedParentControl packedWideCommitImage 580040 15709 where
  backOffset := 1845804
  backTarget := by decide
  branch state pc := packed_index_fetch state 206822 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 206823 pc (by decide) (by decide)

theorem mixed_full_phase (state : MachineState) (fuel : Nat)
    (regs : ParentRegs state (2^24-1))
    (stop : state.getReg .x17=wordAddress (treeWord 4194303)) (pc : state.pc=186816) :
    execute packedWideCommitImage (37749503+fuel) state true =
      (do let out ← FullWidth.parentGroups 186816 32768 4194303 384 state
          let result ← execute packedWideCommitImage fuel out true
          return result.charge 125829887 12582912) :=
  FullWidth.group_execution packedWideCommitImage 186816 32768 4194303 mixed_full_words
    mixedFullControl (by decide) 384 fuel state (by decide) regs stop (fun _ => pc)

theorem mixed_projected_phase (state : MachineState) (fuel : Nat)
    (regs : ParentRegs state 4194303) (pc : state.pc=580040) :
    execute packedWideCommitImage (16777745+fuel) state true =
      (do let out ← packedParentGroups 580040 15709 267 state
          let result ← execute packedWideCommitImage fuel out true
          return result.charge 46137866 4194303) :=
  packed_group_execution packedWideCommitImage 580040 15709 mixed_projected_words
    mixedProjectedControl (by decide) 267 fuel state (by decide) regs (fun _ => pc)

private theorem wide_root_fetch (state : MachineState) (i : Nat) (inside : i < 11)
    (pc : state.pc=BitVec.ofNat 64 (831392+4*i)) :
    fetch packedWideCommitImage state=some (.base ((rootOps[i]?).getD .ECALL)) := by
  have address : state.pc=BitVec.ofNat 64 (4096+4*(206824+i)) := by
    rw [pc]
    congr 1
    omega
  rw [packed_index_fetch state (206824+i) address (by omega) (by omega)]
  interval_cases i <;> rfl

attribute [local irreducible] execute

private theorem wide_root_access (state : MachineState) (heap : state.getReg .x9=4294971424)
    (out : state.getReg .x8=4294971392) (i : Nat) (inside : i<10) :
    memoryArgumentsValid (rootPrefix state i) ((rootOps[i]?).getD .EBREAK)=true := by
  interval_cases i
  · change accessValid (state.getReg .x9+32) 8=true; rw [heap]; decide
  · change accessValid (state.getReg .x8+0) 8=true; rw [out]; decide
  · change accessValid (state.getReg .x9+40) 8=true; rw [heap]; decide
  · change accessValid (state.getReg .x8+8) 8=true; rw [out]; decide
  · change accessValid (state.getReg .x9+48) 8=true; rw [heap]; decide
  · change accessValid (state.getReg .x8+16) 8=true; rw [out]; decide
  · change accessValid (state.getReg .x9+56) 8=true; rw [heap]; decide
  · change accessValid (state.getReg .x8+24) 8=true; rw [out]; decide
  · rfl
  · rfl

theorem execute_packed_root (state : MachineState) (pc : state.pc=831392)
    (heap : state.getReg .x9=4294971424) (out : state.getReg .x8=4294971392) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true = pure ⟨.success,rootPrefix state 10,11,0⟩ := by
  have prefixPC (i : Nat) (inside : i<11) :
      (rootPrefix state i).pc=BitVec.ofNat 64 (831392+4*i) := by
    interval_cases i <;>
      simp only [rootPrefix,rootOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
  have run (left : Nat) :
      execute packedWideCommitImage (10+left) state true =
        (do let result ← execute packedWideCommitImage left (rootPrefix state 10) true
            return result.charge 10 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := rootPrefix state)
    intro i inside
    refine ⟨.base ((rootOps[i]?).getD .EBREAK),?_,?_,?_⟩
    · have fetched := wide_root_fetch (rootPrefix state i) i (by omega) (prefixPC i (by omega))
      interval_cases i <;> exact fetched
    · have access := wide_root_access state heap out i inside
      interval_cases i <;>
        simp only [rootOps,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at access ⊢ <;>
        simp only [ordinaryStep,access,↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch packedWideCommitImage (rootPrefix state 10)=some (.base .ECALL) :=
    wide_root_fetch (rootPrefix state 10) 10 (by decide) (prefixPC 10 (by decide))
  have halt : (rootPrefix state 10).getReg .x5=1 := rfl
  have success : (rootPrefix state 10).getReg .x10=0 := rfl
  rw [show 11+fuel=10+(fuel+1) by omega,run,execute,fetched]
  simp only [halt,success]
  rfl

private theorem packed_sequence_keeps_output (remaining count : Nat) (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentsTrace remaining count state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction count generalizing state with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (packed_parent_keeps_register state _ answer .x8 (by decide) (by decide))

private theorem wide_parent_full_register (base : Word) (span groups : Nat)
    (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentGroups base span groups state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction groups generalizing state with
  | zero =>
    simp only [packedParentGroups,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ groups ih =>
    simp only [packedParentGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have later := ih _ tail
    rw [MachineState.getReg_setPC] at later
    exact later.trans (packed_sequence_keeps_output _ _ _ (out := body) path)

theorem mixed_projected_phase_post (state : MachineState)
    (regs : ParentRegs state 4194303) (pc : state.pc=580040) {out : MachineState}
    (reached : out ∈ support (packedParentGroups 580040 15709 267 state)) :
    ParentRegs out 0 ∧ out.pc=831392 ∧ out.getReg .x8=state.getReg .x8 := by
  have step := packed_groups_post 580040 15709 267 state (by decide) (fun _ => pc) regs reached
  exact ⟨step.1,step.2 (by decide),wide_parent_full_register _ _ _ _ reached⟩

end TwoPermutationPrototype.RV64
