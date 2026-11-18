import CommitGolfCandidate.GroupedManifest
import CommitGolfCandidate.TwoPermutationPackedParentControl
import CommitGolfCandidate.TwoPermutationCommitRun

namespace TwoPermutationPrototype.GroupedUpper
open TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

private def parentWord (index : Nat) : BitVec 32 :=
  if index%4=0 then 0x73 else if index%4=1 then 0x00061f23 else if index%4=2 then 0xfc050513 else 0xfe060613

private def rootWords : List (BitVec 32) :=
  [0x0204bf83,0x01f43023,0x0284bf83,0x01f43423,0x0304bf83,0x01f43823,0x0384bf83,0x01f43c23,0x00100293,0x00000513,0x00000073]

private def expectedWord (index : Nat) : BitVec 32 :=
  if index<201754 then parentWord (index-70178)
  else if index=201754 then 0x00960463
  else if index=201755 then 0x80c8006f
  else rootWords.getD (index-(201754+2)) 0

private def ParentRangeMatches {count : Nat} (packed : ArtifactEncoding.Packed count)
    (offset : Nat) : Prop :=
  ∀ i : Fin count, 70178≤offset+i.val → offset+i.val<201767 →
    packed.get 32 i=expectedWord (offset+i.val)

private theorem parent_range_join {leftCount rightCount : Nat}
    (left : ArtifactEncoding.Packed leftCount) (right : ArtifactEncoding.Packed rightCount)
    (offset : Nat) (first : ParentRangeMatches left offset)
    (last : ParentRangeMatches right (offset+leftCount)) :
    ParentRangeMatches (.join left right) offset := by
  intro index lower upper
  by_cases inside : index.val<leftCount
  · rw [ArtifactEncoding.get_join_left 32 left right index inside]
    exact first ⟨index.val,inside⟩ lower upper
  · rw [ArtifactEncoding.get_join_right 32 left right index inside]
    have position : offset+leftCount+(index.val-leftCount)=offset+index.val := by omega
    have equal := last ⟨index.val-leftCount,by omega⟩ (by simpa only [position] using lower)
      (by simpa only [position] using upper)
    simpa only [position] using equal

private theorem parent_periodic_window (packed : ArtifactEncoding.Packed 512)
    (offset phase : Nat) (alignment : (offset-70178)%4=phase%4)
    (inside : 70178≤offset) (ends : offset+512≤201754)
    (decode : ∀ i : Fin 512, packed.get 32 i=parentWord (phase+i.val)) :
    ParentRangeMatches packed offset := by
  intro i _ _
  have before := i.isLt
  rw [expectedWord,if_pos (by omega),decode]
  simp only [parentWord]
  have same : (phase+i.val)%4=(offset+i.val-70178)%4 := by omega
  rw [same]

private theorem grouped_periodic (i : Fin 512) :
    GroupedArtifact.commitCode_0_138.get 32 i=parentWord (2+i.val) := by
  fin_cases i <;> rfl

private theorem win0 : ParentRangeMatches GroupedArtifact.commitCode_0_0 0 := by
  intro i lo _; have h := i.isLt;omega
private theorem win1 : ParentRangeMatches GroupedArtifact.commitCode_0_1 512 := by
  intro i lo _; have h := i.isLt;omega
private theorem win2 : ParentRangeMatches GroupedArtifact.commitCode_0_2 1024 := by
  intro i lo _; have h := i.isLt;omega
private theorem win3 : ParentRangeMatches GroupedArtifact.commitCode_0_3 1536 := by
  intro i lo _; have h := i.isLt;omega
private theorem win4 : ParentRangeMatches GroupedArtifact.commitCode_0_4 2048 := by
  intro i lo _; have h := i.isLt;omega
private theorem win5 : ParentRangeMatches GroupedArtifact.commitCode_0_5 2560 := by
  intro i lo _; have h := i.isLt;omega
private theorem win6 : ParentRangeMatches GroupedArtifact.commitCode_0_6 3072 := by
  intro i lo _; have h := i.isLt;omega
private theorem win7 : ParentRangeMatches GroupedArtifact.commitCode_0_7 3584 := by
  intro i lo _; have h := i.isLt;omega
private theorem win8 : ParentRangeMatches GroupedArtifact.commitCode_0_8 4096 := by
  intro i lo _; have h := i.isLt;omega
private theorem win9 : ParentRangeMatches GroupedArtifact.commitCode_0_9 4608 := by
  intro i lo _; have h := i.isLt;omega
private theorem win10 : ParentRangeMatches GroupedArtifact.commitCode_0_10 5120 := by
  intro i lo _; have h := i.isLt;omega
private theorem win11 : ParentRangeMatches GroupedArtifact.commitCode_0_11 5632 := by
  intro i lo _; have h := i.isLt;omega
private theorem win12 : ParentRangeMatches GroupedArtifact.commitCode_0_12 6144 := by
  intro i lo _; have h := i.isLt;omega
private theorem win13 : ParentRangeMatches GroupedArtifact.commitCode_0_13 6656 := by
  intro i lo _; have h := i.isLt;omega
private theorem win14 : ParentRangeMatches GroupedArtifact.commitCode_0_14 7168 := by
  intro i lo _; have h := i.isLt;omega
private theorem win15 : ParentRangeMatches GroupedArtifact.commitCode_0_15 7680 := by
  intro i lo _; have h := i.isLt;omega
private theorem win16 : ParentRangeMatches GroupedArtifact.commitCode_0_16 8192 := by
  intro i lo _; have h := i.isLt;omega
private theorem win17 : ParentRangeMatches GroupedArtifact.commitCode_0_17 8704 := by
  intro i lo _; have h := i.isLt;omega
private theorem win18 : ParentRangeMatches GroupedArtifact.commitCode_0_18 9216 := by
  intro i lo _; have h := i.isLt;omega
private theorem win19 : ParentRangeMatches GroupedArtifact.commitCode_0_19 9728 := by
  intro i lo _; have h := i.isLt;omega
private theorem win20 : ParentRangeMatches GroupedArtifact.commitCode_0_20 10240 := by
  intro i lo _; have h := i.isLt;omega
private theorem win21 : ParentRangeMatches GroupedArtifact.commitCode_0_21 10752 := by
  intro i lo _; have h := i.isLt;omega
private theorem win22 : ParentRangeMatches GroupedArtifact.commitCode_0_22 11264 := by
  intro i lo _; have h := i.isLt;omega
private theorem win23 : ParentRangeMatches GroupedArtifact.commitCode_0_23 11776 := by
  intro i lo _; have h := i.isLt;omega
private theorem win24 : ParentRangeMatches GroupedArtifact.commitCode_0_24 12288 := by
  intro i lo _; have h := i.isLt;omega
private theorem win25 : ParentRangeMatches GroupedArtifact.commitCode_0_25 12800 := by
  intro i lo _; have h := i.isLt;omega
private theorem win26 : ParentRangeMatches GroupedArtifact.commitCode_0_26 13312 := by
  intro i lo _; have h := i.isLt;omega
private theorem win27 : ParentRangeMatches GroupedArtifact.commitCode_0_27 13824 := by
  intro i lo _; have h := i.isLt;omega
private theorem win28 : ParentRangeMatches GroupedArtifact.commitCode_0_28 14336 := by
  intro i lo _; have h := i.isLt;omega
private theorem win29 : ParentRangeMatches GroupedArtifact.commitCode_0_29 14848 := by
  intro i lo _; have h := i.isLt;omega
private theorem win30 : ParentRangeMatches GroupedArtifact.commitCode_0_30 15360 := by
  intro i lo _; have h := i.isLt;omega
private theorem win31 : ParentRangeMatches GroupedArtifact.commitCode_0_31 15872 := by
  intro i lo _; have h := i.isLt;omega
private theorem win32 : ParentRangeMatches GroupedArtifact.commitCode_0_32 16384 := by
  intro i lo _; have h := i.isLt;omega
private theorem win33 : ParentRangeMatches GroupedArtifact.commitCode_0_33 16896 := by
  intro i lo _; have h := i.isLt;omega
private theorem win34 : ParentRangeMatches GroupedArtifact.commitCode_0_34 17408 := by
  intro i lo _; have h := i.isLt;omega
private theorem win35 : ParentRangeMatches GroupedArtifact.commitCode_0_35 17920 := by
  intro i lo _; have h := i.isLt;omega
private theorem win36 : ParentRangeMatches GroupedArtifact.commitCode_0_36 18432 := by
  intro i lo _; have h := i.isLt;omega
private theorem win37 : ParentRangeMatches GroupedArtifact.commitCode_0_37 18944 := by
  intro i lo _; have h := i.isLt;omega
private theorem win38 : ParentRangeMatches GroupedArtifact.commitCode_0_38 19456 := by
  intro i lo _; have h := i.isLt;omega
private theorem win39 : ParentRangeMatches GroupedArtifact.commitCode_0_39 19968 := by
  intro i lo _; have h := i.isLt;omega
private theorem win40 : ParentRangeMatches GroupedArtifact.commitCode_0_40 20480 := by
  intro i lo _; have h := i.isLt;omega
private theorem win41 : ParentRangeMatches GroupedArtifact.commitCode_0_41 20992 := by
  intro i lo _; have h := i.isLt;omega
private theorem win42 : ParentRangeMatches GroupedArtifact.commitCode_0_42 21504 := by
  intro i lo _; have h := i.isLt;omega
private theorem win43 : ParentRangeMatches GroupedArtifact.commitCode_0_43 22016 := by
  intro i lo _; have h := i.isLt;omega
private theorem win44 : ParentRangeMatches GroupedArtifact.commitCode_0_44 22528 := by
  intro i lo _; have h := i.isLt;omega
private theorem win45 : ParentRangeMatches GroupedArtifact.commitCode_0_45 23040 := by
  intro i lo _; have h := i.isLt;omega
private theorem win46 : ParentRangeMatches GroupedArtifact.commitCode_0_46 23552 := by
  intro i lo _; have h := i.isLt;omega
private theorem win47 : ParentRangeMatches GroupedArtifact.commitCode_0_47 24064 := by
  intro i lo _; have h := i.isLt;omega
private theorem win48 : ParentRangeMatches GroupedArtifact.commitCode_0_48 24576 := by
  intro i lo _; have h := i.isLt;omega
private theorem win49 : ParentRangeMatches GroupedArtifact.commitCode_0_49 25088 := by
  intro i lo _; have h := i.isLt;omega
private theorem win50 : ParentRangeMatches GroupedArtifact.commitCode_0_50 25600 := by
  intro i lo _; have h := i.isLt;omega
private theorem win51 : ParentRangeMatches GroupedArtifact.commitCode_0_51 26112 := by
  intro i lo _; have h := i.isLt;omega
private theorem win52 : ParentRangeMatches GroupedArtifact.commitCode_0_52 26624 := by
  intro i lo _; have h := i.isLt;omega
private theorem win53 : ParentRangeMatches GroupedArtifact.commitCode_0_53 27136 := by
  intro i lo _; have h := i.isLt;omega
private theorem win54 : ParentRangeMatches GroupedArtifact.commitCode_0_54 27648 := by
  intro i lo _; have h := i.isLt;omega
private theorem win55 : ParentRangeMatches GroupedArtifact.commitCode_0_55 28160 := by
  intro i lo _; have h := i.isLt;omega
private theorem win56 : ParentRangeMatches GroupedArtifact.commitCode_0_56 28672 := by
  intro i lo _; have h := i.isLt;omega
private theorem win57 : ParentRangeMatches GroupedArtifact.commitCode_0_57 29184 := by
  intro i lo _; have h := i.isLt;omega
private theorem win58 : ParentRangeMatches GroupedArtifact.commitCode_0_58 29696 := by
  intro i lo _; have h := i.isLt;omega
private theorem win59 : ParentRangeMatches GroupedArtifact.commitCode_0_59 30208 := by
  intro i lo _; have h := i.isLt;omega
private theorem win60 : ParentRangeMatches GroupedArtifact.commitCode_0_60 30720 := by
  intro i lo _; have h := i.isLt;omega
private theorem win61 : ParentRangeMatches GroupedArtifact.commitCode_0_61 31232 := by
  intro i lo _; have h := i.isLt;omega
private theorem win62 : ParentRangeMatches GroupedArtifact.commitCode_0_62 31744 := by
  intro i lo _; have h := i.isLt;omega
private theorem win63 : ParentRangeMatches GroupedArtifact.commitCode_0_63 32256 := by
  intro i lo _; have h := i.isLt;omega
private theorem win64 : ParentRangeMatches GroupedArtifact.commitCode_0_64 32768 := by
  intro i lo _; have h := i.isLt;omega
private theorem win65 : ParentRangeMatches GroupedArtifact.commitCode_0_65 33280 := by
  intro i lo _; have h := i.isLt;omega
private theorem win66 : ParentRangeMatches GroupedArtifact.commitCode_0_66 33792 := by
  intro i lo _; have h := i.isLt;omega
private theorem win67 : ParentRangeMatches GroupedArtifact.commitCode_0_67 34304 := by
  intro i lo _; have h := i.isLt;omega
private theorem win68 : ParentRangeMatches GroupedArtifact.commitCode_0_68 34816 := by
  intro i lo _; have h := i.isLt;omega
private theorem win69 : ParentRangeMatches GroupedArtifact.commitCode_0_69 35328 := by
  intro i lo _; have h := i.isLt;omega
private theorem win70 : ParentRangeMatches GroupedArtifact.commitCode_0_70 35840 := by
  intro i lo _; have h := i.isLt;omega
private theorem win71 : ParentRangeMatches GroupedArtifact.commitCode_0_71 36352 := by
  intro i lo _; have h := i.isLt;omega
private theorem win72 : ParentRangeMatches GroupedArtifact.commitCode_0_72 36864 := by
  intro i lo _; have h := i.isLt;omega
private theorem win73 : ParentRangeMatches GroupedArtifact.commitCode_0_73 37376 := by
  intro i lo _; have h := i.isLt;omega
private theorem win74 : ParentRangeMatches GroupedArtifact.commitCode_0_74 37888 := by
  intro i lo _; have h := i.isLt;omega
private theorem win75 : ParentRangeMatches GroupedArtifact.commitCode_0_75 38400 := by
  intro i lo _; have h := i.isLt;omega
private theorem win76 : ParentRangeMatches GroupedArtifact.commitCode_0_76 38912 := by
  intro i lo _; have h := i.isLt;omega
private theorem win77 : ParentRangeMatches GroupedArtifact.commitCode_0_77 39424 := by
  intro i lo _; have h := i.isLt;omega
private theorem win78 : ParentRangeMatches GroupedArtifact.commitCode_0_78 39936 := by
  intro i lo _; have h := i.isLt;omega
private theorem win79 : ParentRangeMatches GroupedArtifact.commitCode_0_79 40448 := by
  intro i lo _; have h := i.isLt;omega
private theorem win80 : ParentRangeMatches GroupedArtifact.commitCode_0_80 40960 := by
  intro i lo _; have h := i.isLt;omega
private theorem win81 : ParentRangeMatches GroupedArtifact.commitCode_0_81 41472 := by
  intro i lo _; have h := i.isLt;omega
private theorem win82 : ParentRangeMatches GroupedArtifact.commitCode_0_82 41984 := by
  intro i lo _; have h := i.isLt;omega
private theorem win83 : ParentRangeMatches GroupedArtifact.commitCode_0_83 42496 := by
  intro i lo _; have h := i.isLt;omega
private theorem win84 : ParentRangeMatches GroupedArtifact.commitCode_0_84 43008 := by
  intro i lo _; have h := i.isLt;omega
private theorem win85 : ParentRangeMatches GroupedArtifact.commitCode_0_85 43520 := by
  intro i lo _; have h := i.isLt;omega
private theorem win86 : ParentRangeMatches GroupedArtifact.commitCode_0_86 44032 := by
  intro i lo _; have h := i.isLt;omega
private theorem win87 : ParentRangeMatches GroupedArtifact.commitCode_0_87 44544 := by
  intro i lo _; have h := i.isLt;omega
private theorem win88 : ParentRangeMatches GroupedArtifact.commitCode_0_88 45056 := by
  intro i lo _; have h := i.isLt;omega
private theorem win89 : ParentRangeMatches GroupedArtifact.commitCode_0_89 45568 := by
  intro i lo _; have h := i.isLt;omega
private theorem win90 : ParentRangeMatches GroupedArtifact.commitCode_0_90 46080 := by
  intro i lo _; have h := i.isLt;omega
private theorem win91 : ParentRangeMatches GroupedArtifact.commitCode_0_91 46592 := by
  intro i lo _; have h := i.isLt;omega
private theorem win92 : ParentRangeMatches GroupedArtifact.commitCode_0_92 47104 := by
  intro i lo _; have h := i.isLt;omega
private theorem win93 : ParentRangeMatches GroupedArtifact.commitCode_0_93 47616 := by
  intro i lo _; have h := i.isLt;omega
private theorem win94 : ParentRangeMatches GroupedArtifact.commitCode_0_94 48128 := by
  intro i lo _; have h := i.isLt;omega
private theorem win95 : ParentRangeMatches GroupedArtifact.commitCode_0_95 48640 := by
  intro i lo _; have h := i.isLt;omega
private theorem win96 : ParentRangeMatches GroupedArtifact.commitCode_0_96 49152 := by
  intro i lo _; have h := i.isLt;omega
private theorem win97 : ParentRangeMatches GroupedArtifact.commitCode_0_97 49664 := by
  intro i lo _; have h := i.isLt;omega
private theorem win98 : ParentRangeMatches GroupedArtifact.commitCode_0_98 50176 := by
  intro i lo _; have h := i.isLt;omega
private theorem win99 : ParentRangeMatches GroupedArtifact.commitCode_0_99 50688 := by
  intro i lo _; have h := i.isLt;omega
private theorem win100 : ParentRangeMatches GroupedArtifact.commitCode_0_100 51200 := by
  intro i lo _; have h := i.isLt;omega
private theorem win101 : ParentRangeMatches GroupedArtifact.commitCode_0_101 51712 := by
  intro i lo _; have h := i.isLt;omega
private theorem win102 : ParentRangeMatches GroupedArtifact.commitCode_0_102 52224 := by
  intro i lo _; have h := i.isLt;omega
private theorem win103 : ParentRangeMatches GroupedArtifact.commitCode_0_103 52736 := by
  intro i lo _; have h := i.isLt;omega
private theorem win104 : ParentRangeMatches GroupedArtifact.commitCode_0_104 53248 := by
  intro i lo _; have h := i.isLt;omega
private theorem win105 : ParentRangeMatches GroupedArtifact.commitCode_0_105 53760 := by
  intro i lo _; have h := i.isLt;omega
private theorem win106 : ParentRangeMatches GroupedArtifact.commitCode_0_106 54272 := by
  intro i lo _; have h := i.isLt;omega
private theorem win107 : ParentRangeMatches GroupedArtifact.commitCode_0_107 54784 := by
  intro i lo _; have h := i.isLt;omega
private theorem win108 : ParentRangeMatches GroupedArtifact.commitCode_0_108 55296 := by
  intro i lo _; have h := i.isLt;omega
private theorem win109 : ParentRangeMatches GroupedArtifact.commitCode_0_109 55808 := by
  intro i lo _; have h := i.isLt;omega
private theorem win110 : ParentRangeMatches GroupedArtifact.commitCode_0_110 56320 := by
  intro i lo _; have h := i.isLt;omega
private theorem win111 : ParentRangeMatches GroupedArtifact.commitCode_0_111 56832 := by
  intro i lo _; have h := i.isLt;omega
private theorem win112 : ParentRangeMatches GroupedArtifact.commitCode_0_112 57344 := by
  intro i lo _; have h := i.isLt;omega
private theorem win113 : ParentRangeMatches GroupedArtifact.commitCode_0_113 57856 := by
  intro i lo _; have h := i.isLt;omega
private theorem win114 : ParentRangeMatches GroupedArtifact.commitCode_0_114 58368 := by
  intro i lo _; have h := i.isLt;omega
private theorem win115 : ParentRangeMatches GroupedArtifact.commitCode_0_115 58880 := by
  intro i lo _; have h := i.isLt;omega
private theorem win116 : ParentRangeMatches GroupedArtifact.commitCode_0_116 59392 := by
  intro i lo _; have h := i.isLt;omega
private theorem win117 : ParentRangeMatches GroupedArtifact.commitCode_0_117 59904 := by
  intro i lo _; have h := i.isLt;omega
private theorem win118 : ParentRangeMatches GroupedArtifact.commitCode_0_118 60416 := by
  intro i lo _; have h := i.isLt;omega
private theorem win119 : ParentRangeMatches GroupedArtifact.commitCode_0_119 60928 := by
  intro i lo _; have h := i.isLt;omega
private theorem win120 : ParentRangeMatches GroupedArtifact.commitCode_0_120 61440 := by
  intro i lo _; have h := i.isLt;omega
private theorem win121 : ParentRangeMatches GroupedArtifact.commitCode_0_121 61952 := by
  intro i lo _; have h := i.isLt;omega
private theorem win122 : ParentRangeMatches GroupedArtifact.commitCode_0_122 62464 := by
  intro i lo _; have h := i.isLt;omega
private theorem win123 : ParentRangeMatches GroupedArtifact.commitCode_0_123 62976 := by
  intro i lo _; have h := i.isLt;omega
private theorem win124 : ParentRangeMatches GroupedArtifact.commitCode_0_124 63488 := by
  intro i lo _; have h := i.isLt;omega
private theorem win125 : ParentRangeMatches GroupedArtifact.commitCode_0_125 64000 := by
  intro i lo _; have h := i.isLt;omega
private theorem win126 : ParentRangeMatches GroupedArtifact.commitCode_0_126 64512 := by
  intro i lo _; have h := i.isLt;omega
private theorem win127 : ParentRangeMatches GroupedArtifact.commitCode_0_127 65024 := by
  intro i lo _; have h := i.isLt;omega
private theorem win128 : ParentRangeMatches GroupedArtifact.commitCode_0_128 65536 := by
  intro i lo _; have h := i.isLt;omega
private theorem win129 : ParentRangeMatches GroupedArtifact.commitCode_0_129 66048 := by
  intro i lo _; have h := i.isLt;omega
private theorem win130 : ParentRangeMatches GroupedArtifact.commitCode_0_130 66560 := by
  intro i lo _; have h := i.isLt;omega
private theorem win131 : ParentRangeMatches GroupedArtifact.commitCode_0_131 67072 := by
  intro i lo _; have h := i.isLt;omega
private theorem win132 : ParentRangeMatches GroupedArtifact.commitCode_0_132 67584 := by
  intro i lo _; have h := i.isLt;omega
private theorem win133 : ParentRangeMatches GroupedArtifact.commitCode_0_133 68096 := by
  intro i lo _; have h := i.isLt;omega
private theorem win134 : ParentRangeMatches GroupedArtifact.commitCode_0_134 68608 := by
  intro i lo _; have h := i.isLt;omega
private theorem win135 : ParentRangeMatches GroupedArtifact.commitCode_0_135 69120 := by
  intro i lo _; have h := i.isLt;omega
private theorem win136 : ParentRangeMatches GroupedArtifact.commitCode_0_136 69632 := by
  intro i lo _; have h := i.isLt;omega
private theorem win137 : ParentRangeMatches GroupedArtifact.commitCode_0_137 70144 := by
  unfold ParentRangeMatches expectedWord parentWord rootWords;decide +kernel
private theorem win138 : ParentRangeMatches GroupedArtifact.commitCode_0_138 70656 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win139 : ParentRangeMatches GroupedArtifact.commitCode_0_139 71168 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win140 : ParentRangeMatches GroupedArtifact.commitCode_0_140 71680 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win141 : ParentRangeMatches GroupedArtifact.commitCode_0_141 72192 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win142 : ParentRangeMatches GroupedArtifact.commitCode_0_142 72704 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win143 : ParentRangeMatches GroupedArtifact.commitCode_0_143 73216 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win144 : ParentRangeMatches GroupedArtifact.commitCode_0_144 73728 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win145 : ParentRangeMatches GroupedArtifact.commitCode_0_145 74240 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win146 : ParentRangeMatches GroupedArtifact.commitCode_0_146 74752 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win147 : ParentRangeMatches GroupedArtifact.commitCode_0_147 75264 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win148 : ParentRangeMatches GroupedArtifact.commitCode_0_148 75776 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win149 : ParentRangeMatches GroupedArtifact.commitCode_0_149 76288 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win150 : ParentRangeMatches GroupedArtifact.commitCode_0_150 76800 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win151 : ParentRangeMatches GroupedArtifact.commitCode_0_151 77312 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win152 : ParentRangeMatches GroupedArtifact.commitCode_0_152 77824 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win153 : ParentRangeMatches GroupedArtifact.commitCode_0_153 78336 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win154 : ParentRangeMatches GroupedArtifact.commitCode_0_154 78848 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win155 : ParentRangeMatches GroupedArtifact.commitCode_0_155 79360 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win156 : ParentRangeMatches GroupedArtifact.commitCode_0_156 79872 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win157 : ParentRangeMatches GroupedArtifact.commitCode_0_157 80384 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win158 : ParentRangeMatches GroupedArtifact.commitCode_0_158 80896 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win159 : ParentRangeMatches GroupedArtifact.commitCode_0_159 81408 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win160 : ParentRangeMatches GroupedArtifact.commitCode_0_160 81920 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win161 : ParentRangeMatches GroupedArtifact.commitCode_0_161 82432 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win162 : ParentRangeMatches GroupedArtifact.commitCode_0_162 82944 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win163 : ParentRangeMatches GroupedArtifact.commitCode_0_163 83456 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win164 : ParentRangeMatches GroupedArtifact.commitCode_0_164 83968 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win165 : ParentRangeMatches GroupedArtifact.commitCode_0_165 84480 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win166 : ParentRangeMatches GroupedArtifact.commitCode_0_166 84992 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win167 : ParentRangeMatches GroupedArtifact.commitCode_0_167 85504 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win168 : ParentRangeMatches GroupedArtifact.commitCode_0_168 86016 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win169 : ParentRangeMatches GroupedArtifact.commitCode_0_169 86528 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win170 : ParentRangeMatches GroupedArtifact.commitCode_0_170 87040 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win171 : ParentRangeMatches GroupedArtifact.commitCode_0_171 87552 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win172 : ParentRangeMatches GroupedArtifact.commitCode_0_172 88064 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win173 : ParentRangeMatches GroupedArtifact.commitCode_0_173 88576 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win174 : ParentRangeMatches GroupedArtifact.commitCode_0_174 89088 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win175 : ParentRangeMatches GroupedArtifact.commitCode_0_175 89600 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win176 : ParentRangeMatches GroupedArtifact.commitCode_0_176 90112 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win177 : ParentRangeMatches GroupedArtifact.commitCode_0_177 90624 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win178 : ParentRangeMatches GroupedArtifact.commitCode_0_178 91136 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win179 : ParentRangeMatches GroupedArtifact.commitCode_0_179 91648 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win180 : ParentRangeMatches GroupedArtifact.commitCode_0_180 92160 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win181 : ParentRangeMatches GroupedArtifact.commitCode_0_181 92672 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win182 : ParentRangeMatches GroupedArtifact.commitCode_0_182 93184 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win183 : ParentRangeMatches GroupedArtifact.commitCode_0_183 93696 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win184 : ParentRangeMatches GroupedArtifact.commitCode_0_184 94208 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win185 : ParentRangeMatches GroupedArtifact.commitCode_0_185 94720 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win186 : ParentRangeMatches GroupedArtifact.commitCode_0_186 95232 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win187 : ParentRangeMatches GroupedArtifact.commitCode_0_187 95744 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win188 : ParentRangeMatches GroupedArtifact.commitCode_0_188 96256 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win189 : ParentRangeMatches GroupedArtifact.commitCode_0_189 96768 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win190 : ParentRangeMatches GroupedArtifact.commitCode_0_190 97280 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win191 : ParentRangeMatches GroupedArtifact.commitCode_0_191 97792 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win192 : ParentRangeMatches GroupedArtifact.commitCode_0_192 98304 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win193 : ParentRangeMatches GroupedArtifact.commitCode_0_193 98816 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win194 : ParentRangeMatches GroupedArtifact.commitCode_0_194 99328 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win195 : ParentRangeMatches GroupedArtifact.commitCode_0_195 99840 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win196 : ParentRangeMatches GroupedArtifact.commitCode_0_196 100352 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win197 : ParentRangeMatches GroupedArtifact.commitCode_0_197 100864 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win198 : ParentRangeMatches GroupedArtifact.commitCode_0_198 101376 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win199 : ParentRangeMatches GroupedArtifact.commitCode_0_199 101888 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win200 : ParentRangeMatches GroupedArtifact.commitCode_0_200 102400 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win201 : ParentRangeMatches GroupedArtifact.commitCode_0_201 102912 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win202 : ParentRangeMatches GroupedArtifact.commitCode_0_202 103424 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win203 : ParentRangeMatches GroupedArtifact.commitCode_0_203 103936 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win204 : ParentRangeMatches GroupedArtifact.commitCode_0_204 104448 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win205 : ParentRangeMatches GroupedArtifact.commitCode_0_205 104960 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win206 : ParentRangeMatches GroupedArtifact.commitCode_0_206 105472 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win207 : ParentRangeMatches GroupedArtifact.commitCode_0_207 105984 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win208 : ParentRangeMatches GroupedArtifact.commitCode_0_208 106496 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win209 : ParentRangeMatches GroupedArtifact.commitCode_0_209 107008 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win210 : ParentRangeMatches GroupedArtifact.commitCode_0_210 107520 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win211 : ParentRangeMatches GroupedArtifact.commitCode_0_211 108032 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win212 : ParentRangeMatches GroupedArtifact.commitCode_0_212 108544 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win213 : ParentRangeMatches GroupedArtifact.commitCode_0_213 109056 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win214 : ParentRangeMatches GroupedArtifact.commitCode_0_214 109568 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win215 : ParentRangeMatches GroupedArtifact.commitCode_0_215 110080 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win216 : ParentRangeMatches GroupedArtifact.commitCode_0_216 110592 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win217 : ParentRangeMatches GroupedArtifact.commitCode_0_217 111104 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win218 : ParentRangeMatches GroupedArtifact.commitCode_0_218 111616 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win219 : ParentRangeMatches GroupedArtifact.commitCode_0_219 112128 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win220 : ParentRangeMatches GroupedArtifact.commitCode_0_220 112640 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win221 : ParentRangeMatches GroupedArtifact.commitCode_0_221 113152 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win222 : ParentRangeMatches GroupedArtifact.commitCode_0_222 113664 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win223 : ParentRangeMatches GroupedArtifact.commitCode_0_223 114176 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win224 : ParentRangeMatches GroupedArtifact.commitCode_0_224 114688 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win225 : ParentRangeMatches GroupedArtifact.commitCode_0_225 115200 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win226 : ParentRangeMatches GroupedArtifact.commitCode_0_226 115712 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win227 : ParentRangeMatches GroupedArtifact.commitCode_0_227 116224 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win228 : ParentRangeMatches GroupedArtifact.commitCode_0_228 116736 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win229 : ParentRangeMatches GroupedArtifact.commitCode_0_229 117248 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win230 : ParentRangeMatches GroupedArtifact.commitCode_0_230 117760 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win231 : ParentRangeMatches GroupedArtifact.commitCode_0_231 118272 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win232 : ParentRangeMatches GroupedArtifact.commitCode_0_232 118784 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win233 : ParentRangeMatches GroupedArtifact.commitCode_0_233 119296 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win234 : ParentRangeMatches GroupedArtifact.commitCode_0_234 119808 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win235 : ParentRangeMatches GroupedArtifact.commitCode_0_235 120320 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win236 : ParentRangeMatches GroupedArtifact.commitCode_0_236 120832 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win237 : ParentRangeMatches GroupedArtifact.commitCode_0_237 121344 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win238 : ParentRangeMatches GroupedArtifact.commitCode_0_238 121856 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win239 : ParentRangeMatches GroupedArtifact.commitCode_0_239 122368 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win240 : ParentRangeMatches GroupedArtifact.commitCode_0_240 122880 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win241 : ParentRangeMatches GroupedArtifact.commitCode_0_241 123392 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win242 : ParentRangeMatches GroupedArtifact.commitCode_0_242 123904 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win243 : ParentRangeMatches GroupedArtifact.commitCode_0_243 124416 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win244 : ParentRangeMatches GroupedArtifact.commitCode_0_244 124928 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win245 : ParentRangeMatches GroupedArtifact.commitCode_0_245 125440 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win246 : ParentRangeMatches GroupedArtifact.commitCode_0_246 125952 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win247 : ParentRangeMatches GroupedArtifact.commitCode_0_247 126464 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win248 : ParentRangeMatches GroupedArtifact.commitCode_0_248 126976 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win249 : ParentRangeMatches GroupedArtifact.commitCode_0_249 127488 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win250 : ParentRangeMatches GroupedArtifact.commitCode_0_250 128000 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win251 : ParentRangeMatches GroupedArtifact.commitCode_0_251 128512 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win252 : ParentRangeMatches GroupedArtifact.commitCode_0_252 129024 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win253 : ParentRangeMatches GroupedArtifact.commitCode_0_253 129536 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win254 : ParentRangeMatches GroupedArtifact.commitCode_0_254 130048 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win255 : ParentRangeMatches GroupedArtifact.commitCode_0_255 130560 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win256 : ParentRangeMatches GroupedArtifact.commitCode_0_256 131072 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win257 : ParentRangeMatches GroupedArtifact.commitCode_0_257 131584 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win258 : ParentRangeMatches GroupedArtifact.commitCode_0_258 132096 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win259 : ParentRangeMatches GroupedArtifact.commitCode_0_259 132608 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win260 : ParentRangeMatches GroupedArtifact.commitCode_0_260 133120 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win261 : ParentRangeMatches GroupedArtifact.commitCode_0_261 133632 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win262 : ParentRangeMatches GroupedArtifact.commitCode_0_262 134144 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win263 : ParentRangeMatches GroupedArtifact.commitCode_0_263 134656 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win264 : ParentRangeMatches GroupedArtifact.commitCode_0_264 135168 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win265 : ParentRangeMatches GroupedArtifact.commitCode_0_265 135680 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win266 : ParentRangeMatches GroupedArtifact.commitCode_0_266 136192 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win267 : ParentRangeMatches GroupedArtifact.commitCode_0_267 136704 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win268 : ParentRangeMatches GroupedArtifact.commitCode_0_268 137216 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win269 : ParentRangeMatches GroupedArtifact.commitCode_0_269 137728 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win270 : ParentRangeMatches GroupedArtifact.commitCode_0_270 138240 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win271 : ParentRangeMatches GroupedArtifact.commitCode_0_271 138752 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win272 : ParentRangeMatches GroupedArtifact.commitCode_0_272 139264 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win273 : ParentRangeMatches GroupedArtifact.commitCode_0_273 139776 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win274 : ParentRangeMatches GroupedArtifact.commitCode_0_274 140288 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win275 : ParentRangeMatches GroupedArtifact.commitCode_0_275 140800 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win276 : ParentRangeMatches GroupedArtifact.commitCode_0_276 141312 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win277 : ParentRangeMatches GroupedArtifact.commitCode_0_277 141824 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win278 : ParentRangeMatches GroupedArtifact.commitCode_0_278 142336 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win279 : ParentRangeMatches GroupedArtifact.commitCode_0_279 142848 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win280 : ParentRangeMatches GroupedArtifact.commitCode_0_280 143360 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win281 : ParentRangeMatches GroupedArtifact.commitCode_0_281 143872 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win282 : ParentRangeMatches GroupedArtifact.commitCode_0_282 144384 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win283 : ParentRangeMatches GroupedArtifact.commitCode_0_283 144896 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win284 : ParentRangeMatches GroupedArtifact.commitCode_0_284 145408 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win285 : ParentRangeMatches GroupedArtifact.commitCode_0_285 145920 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win286 : ParentRangeMatches GroupedArtifact.commitCode_0_286 146432 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win287 : ParentRangeMatches GroupedArtifact.commitCode_0_287 146944 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win288 : ParentRangeMatches GroupedArtifact.commitCode_0_288 147456 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win289 : ParentRangeMatches GroupedArtifact.commitCode_0_289 147968 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win290 : ParentRangeMatches GroupedArtifact.commitCode_0_290 148480 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win291 : ParentRangeMatches GroupedArtifact.commitCode_0_291 148992 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win292 : ParentRangeMatches GroupedArtifact.commitCode_0_292 149504 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win293 : ParentRangeMatches GroupedArtifact.commitCode_0_293 150016 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win294 : ParentRangeMatches GroupedArtifact.commitCode_0_294 150528 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win295 : ParentRangeMatches GroupedArtifact.commitCode_0_295 151040 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win296 : ParentRangeMatches GroupedArtifact.commitCode_0_296 151552 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win297 : ParentRangeMatches GroupedArtifact.commitCode_0_297 152064 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win298 : ParentRangeMatches GroupedArtifact.commitCode_0_298 152576 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win299 : ParentRangeMatches GroupedArtifact.commitCode_0_299 153088 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win300 : ParentRangeMatches GroupedArtifact.commitCode_0_300 153600 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win301 : ParentRangeMatches GroupedArtifact.commitCode_0_301 154112 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win302 : ParentRangeMatches GroupedArtifact.commitCode_0_302 154624 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win303 : ParentRangeMatches GroupedArtifact.commitCode_0_303 155136 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win304 : ParentRangeMatches GroupedArtifact.commitCode_0_304 155648 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win305 : ParentRangeMatches GroupedArtifact.commitCode_0_305 156160 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win306 : ParentRangeMatches GroupedArtifact.commitCode_0_306 156672 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win307 : ParentRangeMatches GroupedArtifact.commitCode_0_307 157184 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win308 : ParentRangeMatches GroupedArtifact.commitCode_0_308 157696 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win309 : ParentRangeMatches GroupedArtifact.commitCode_0_309 158208 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win310 : ParentRangeMatches GroupedArtifact.commitCode_0_310 158720 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win311 : ParentRangeMatches GroupedArtifact.commitCode_0_311 159232 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win312 : ParentRangeMatches GroupedArtifact.commitCode_0_312 159744 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win313 : ParentRangeMatches GroupedArtifact.commitCode_0_313 160256 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win314 : ParentRangeMatches GroupedArtifact.commitCode_0_314 160768 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win315 : ParentRangeMatches GroupedArtifact.commitCode_0_315 161280 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win316 : ParentRangeMatches GroupedArtifact.commitCode_0_316 161792 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win317 : ParentRangeMatches GroupedArtifact.commitCode_0_317 162304 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win318 : ParentRangeMatches GroupedArtifact.commitCode_0_318 162816 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win319 : ParentRangeMatches GroupedArtifact.commitCode_0_319 163328 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win320 : ParentRangeMatches GroupedArtifact.commitCode_0_320 163840 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win321 : ParentRangeMatches GroupedArtifact.commitCode_0_321 164352 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win322 : ParentRangeMatches GroupedArtifact.commitCode_0_322 164864 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win323 : ParentRangeMatches GroupedArtifact.commitCode_0_323 165376 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win324 : ParentRangeMatches GroupedArtifact.commitCode_0_324 165888 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win325 : ParentRangeMatches GroupedArtifact.commitCode_0_325 166400 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win326 : ParentRangeMatches GroupedArtifact.commitCode_0_326 166912 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win327 : ParentRangeMatches GroupedArtifact.commitCode_0_327 167424 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win328 : ParentRangeMatches GroupedArtifact.commitCode_0_328 167936 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win329 : ParentRangeMatches GroupedArtifact.commitCode_0_329 168448 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win330 : ParentRangeMatches GroupedArtifact.commitCode_0_330 168960 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win331 : ParentRangeMatches GroupedArtifact.commitCode_0_331 169472 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win332 : ParentRangeMatches GroupedArtifact.commitCode_0_332 169984 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win333 : ParentRangeMatches GroupedArtifact.commitCode_0_333 170496 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win334 : ParentRangeMatches GroupedArtifact.commitCode_0_334 171008 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win335 : ParentRangeMatches GroupedArtifact.commitCode_0_335 171520 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win336 : ParentRangeMatches GroupedArtifact.commitCode_0_336 172032 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win337 : ParentRangeMatches GroupedArtifact.commitCode_0_337 172544 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win338 : ParentRangeMatches GroupedArtifact.commitCode_0_338 173056 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win339 : ParentRangeMatches GroupedArtifact.commitCode_0_339 173568 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win340 : ParentRangeMatches GroupedArtifact.commitCode_0_340 174080 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win341 : ParentRangeMatches GroupedArtifact.commitCode_0_341 174592 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win342 : ParentRangeMatches GroupedArtifact.commitCode_0_342 175104 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win343 : ParentRangeMatches GroupedArtifact.commitCode_0_343 175616 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win344 : ParentRangeMatches GroupedArtifact.commitCode_0_344 176128 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win345 : ParentRangeMatches GroupedArtifact.commitCode_0_345 176640 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win346 : ParentRangeMatches GroupedArtifact.commitCode_0_346 177152 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win347 : ParentRangeMatches GroupedArtifact.commitCode_0_347 177664 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win348 : ParentRangeMatches GroupedArtifact.commitCode_0_348 178176 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win349 : ParentRangeMatches GroupedArtifact.commitCode_0_349 178688 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win350 : ParentRangeMatches GroupedArtifact.commitCode_0_350 179200 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win351 : ParentRangeMatches GroupedArtifact.commitCode_0_351 179712 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win352 : ParentRangeMatches GroupedArtifact.commitCode_0_352 180224 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win353 : ParentRangeMatches GroupedArtifact.commitCode_0_353 180736 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win354 : ParentRangeMatches GroupedArtifact.commitCode_0_354 181248 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win355 : ParentRangeMatches GroupedArtifact.commitCode_0_355 181760 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win356 : ParentRangeMatches GroupedArtifact.commitCode_0_356 182272 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win357 : ParentRangeMatches GroupedArtifact.commitCode_0_357 182784 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win358 : ParentRangeMatches GroupedArtifact.commitCode_0_358 183296 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win359 : ParentRangeMatches GroupedArtifact.commitCode_0_359 183808 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win360 : ParentRangeMatches GroupedArtifact.commitCode_0_360 184320 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win361 : ParentRangeMatches GroupedArtifact.commitCode_0_361 184832 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win362 : ParentRangeMatches GroupedArtifact.commitCode_0_362 185344 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win363 : ParentRangeMatches GroupedArtifact.commitCode_0_363 185856 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win364 : ParentRangeMatches GroupedArtifact.commitCode_0_364 186368 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win365 : ParentRangeMatches GroupedArtifact.commitCode_0_365 186880 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win366 : ParentRangeMatches GroupedArtifact.commitCode_0_366 187392 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win367 : ParentRangeMatches GroupedArtifact.commitCode_0_367 187904 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win368 : ParentRangeMatches GroupedArtifact.commitCode_0_368 188416 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win369 : ParentRangeMatches GroupedArtifact.commitCode_0_369 188928 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win370 : ParentRangeMatches GroupedArtifact.commitCode_0_370 189440 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win371 : ParentRangeMatches GroupedArtifact.commitCode_0_371 189952 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win372 : ParentRangeMatches GroupedArtifact.commitCode_0_372 190464 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win373 : ParentRangeMatches GroupedArtifact.commitCode_0_373 190976 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win374 : ParentRangeMatches GroupedArtifact.commitCode_0_374 191488 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win375 : ParentRangeMatches GroupedArtifact.commitCode_0_375 192000 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win376 : ParentRangeMatches GroupedArtifact.commitCode_0_376 192512 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win377 : ParentRangeMatches GroupedArtifact.commitCode_0_377 193024 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win378 : ParentRangeMatches GroupedArtifact.commitCode_0_378 193536 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win379 : ParentRangeMatches GroupedArtifact.commitCode_0_379 194048 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win380 : ParentRangeMatches GroupedArtifact.commitCode_0_380 194560 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win381 : ParentRangeMatches GroupedArtifact.commitCode_0_381 195072 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win382 : ParentRangeMatches GroupedArtifact.commitCode_0_382 195584 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win383 : ParentRangeMatches GroupedArtifact.commitCode_0_383 196096 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win384 : ParentRangeMatches GroupedArtifact.commitCode_0_384 196608 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win385 : ParentRangeMatches GroupedArtifact.commitCode_0_385 197120 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win386 : ParentRangeMatches GroupedArtifact.commitCode_0_386 197632 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win387 : ParentRangeMatches GroupedArtifact.commitCode_0_387 198144 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win388 : ParentRangeMatches GroupedArtifact.commitCode_0_388 198656 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win389 : ParentRangeMatches GroupedArtifact.commitCode_0_389 199168 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win390 : ParentRangeMatches GroupedArtifact.commitCode_0_390 199680 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win391 : ParentRangeMatches GroupedArtifact.commitCode_0_391 200192 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win392 : ParentRangeMatches GroupedArtifact.commitCode_0_392 200704 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win393 : ParentRangeMatches GroupedArtifact.commitCode_0_393 201216 := by
  exact parent_periodic_window _ _ 2 (by decide) (by decide) (by decide) grouped_periodic
private theorem win394 : ParentRangeMatches GroupedArtifact.commitCode_0_394 201728 := by
  unfold ParentRangeMatches expectedWord parentWord rootWords;decide +kernel

private theorem parent_packed_matches : ParentRangeMatches GroupedArtifact.commitCode 0 := by
  exact (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win0 win1) (parent_range_join _ _ _ win2 win3)) (parent_range_join _ _ _ (parent_range_join _ _ _ win4 win5) (parent_range_join _ _ _ win6 win7))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win8 win9) (parent_range_join _ _ _ win10 win11)) (parent_range_join _ _ _ (parent_range_join _ _ _ win12 win13) (parent_range_join _ _ _ win14 win15)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win16 win17) (parent_range_join _ _ _ win18 win19)) (parent_range_join _ _ _ (parent_range_join _ _ _ win20 win21) (parent_range_join _ _ _ win22 win23))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win24 win25) (parent_range_join _ _ _ win26 win27)) (parent_range_join _ _ _ (parent_range_join _ _ _ win28 win29) (parent_range_join _ _ _ win30 win31))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win32 win33) (parent_range_join _ _ _ win34 win35)) (parent_range_join _ _ _ (parent_range_join _ _ _ win36 win37) (parent_range_join _ _ _ win38 win39))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win40 win41) (parent_range_join _ _ _ win42 win43)) (parent_range_join _ _ _ (parent_range_join _ _ _ win44 win45) (parent_range_join _ _ _ win46 win47)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win48 win49) (parent_range_join _ _ _ win50 win51)) (parent_range_join _ _ _ (parent_range_join _ _ _ win52 win53) (parent_range_join _ _ _ win54 win55))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win56 win57) (parent_range_join _ _ _ win58 win59)) (parent_range_join _ _ _ (parent_range_join _ _ _ win60 win61) (parent_range_join _ _ _ win62 win63)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win64 win65) (parent_range_join _ _ _ win66 win67)) (parent_range_join _ _ _ (parent_range_join _ _ _ win68 win69) (parent_range_join _ _ _ win70 win71))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win72 win73) (parent_range_join _ _ _ win74 win75)) (parent_range_join _ _ _ (parent_range_join _ _ _ win76 win77) (parent_range_join _ _ _ win78 win79)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win80 win81) (parent_range_join _ _ _ win82 win83)) (parent_range_join _ _ _ (parent_range_join _ _ _ win84 win85) (parent_range_join _ _ _ win86 win87))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win88 win89) (parent_range_join _ _ _ win90 win91)) (parent_range_join _ _ _ (parent_range_join _ _ _ win92 win93) (parent_range_join _ _ _ win94 win95))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win96 win97) (parent_range_join _ _ _ win98 win99)) (parent_range_join _ _ _ (parent_range_join _ _ _ win100 win101) (parent_range_join _ _ _ win102 win103))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win104 win105) (parent_range_join _ _ _ win106 win107)) (parent_range_join _ _ _ (parent_range_join _ _ _ win108 win109) (parent_range_join _ _ _ win110 win111)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win112 win113) (parent_range_join _ _ _ win114 win115)) (parent_range_join _ _ _ (parent_range_join _ _ _ win116 win117) (parent_range_join _ _ _ win118 win119))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win120 win121) (parent_range_join _ _ _ win122 win123)) (parent_range_join _ _ _ (parent_range_join _ _ _ win124 win125) (parent_range_join _ _ _ win126 win127)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win128 win129) (parent_range_join _ _ _ win130 win131)) (parent_range_join _ _ _ (parent_range_join _ _ _ win132 win133) (parent_range_join _ _ _ win134 win135))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win136 win137) (parent_range_join _ _ _ win138 win139)) (parent_range_join _ _ _ (parent_range_join _ _ _ win140 win141) (parent_range_join _ _ _ win142 win143)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win144 win145) (parent_range_join _ _ _ win146 win147)) (parent_range_join _ _ _ (parent_range_join _ _ _ win148 win149) (parent_range_join _ _ _ win150 win151))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win152 win153) (parent_range_join _ _ _ win154 win155)) (parent_range_join _ _ _ (parent_range_join _ _ _ win156 win157) (parent_range_join _ _ _ win158 win159))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win160 win161) (parent_range_join _ _ _ win162 win163)) (parent_range_join _ _ _ (parent_range_join _ _ _ win164 win165) (parent_range_join _ _ _ win166 win167))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win168 win169) (parent_range_join _ _ _ win170 win171)) (parent_range_join _ _ _ (parent_range_join _ _ _ win172 win173) (parent_range_join _ _ _ win174 win175)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win176 win177) (parent_range_join _ _ _ win178 win179)) (parent_range_join _ _ _ (parent_range_join _ _ _ win180 win181) (parent_range_join _ _ _ win182 win183))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win184 win185) (parent_range_join _ _ _ win186 win187)) (parent_range_join _ _ _ (parent_range_join _ _ _ win188 win189) (parent_range_join _ _ _ win190 win191)))))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win192 win193) (parent_range_join _ _ _ win194 win195)) (parent_range_join _ _ _ (parent_range_join _ _ _ win196 win197) (parent_range_join _ _ _ win198 win199))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win200 win201) (parent_range_join _ _ _ win202 win203)) (parent_range_join _ _ _ (parent_range_join _ _ _ win204 win205) (parent_range_join _ _ _ win206 win207)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win208 win209) (parent_range_join _ _ _ win210 win211)) (parent_range_join _ _ _ (parent_range_join _ _ _ win212 win213) (parent_range_join _ _ _ win214 win215))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win216 win217) (parent_range_join _ _ _ win218 win219)) (parent_range_join _ _ _ (parent_range_join _ _ _ win220 win221) (parent_range_join _ _ _ win222 win223))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win224 win225) (parent_range_join _ _ _ win226 win227)) (parent_range_join _ _ _ (parent_range_join _ _ _ win228 win229) (parent_range_join _ _ _ win230 win231))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win232 win233) (parent_range_join _ _ _ win234 win235)) (parent_range_join _ _ _ (parent_range_join _ _ _ win236 win237) (parent_range_join _ _ _ win238 win239)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win240 win241) (parent_range_join _ _ _ win242 win243)) (parent_range_join _ _ _ (parent_range_join _ _ _ win244 win245) (parent_range_join _ _ _ win246 win247))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win248 win249) (parent_range_join _ _ _ win250 win251)) (parent_range_join _ _ _ (parent_range_join _ _ _ win252 win253) (parent_range_join _ _ _ win254 win255)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win256 win257) (parent_range_join _ _ _ win258 win259)) (parent_range_join _ _ _ (parent_range_join _ _ _ win260 win261) (parent_range_join _ _ _ win262 win263))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win264 win265) (parent_range_join _ _ _ win266 win267)) (parent_range_join _ _ _ (parent_range_join _ _ _ win268 win269) (parent_range_join _ _ _ win270 win271)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win272 win273) (parent_range_join _ _ _ win274 win275)) (parent_range_join _ _ _ (parent_range_join _ _ _ win276 win277) (parent_range_join _ _ _ win278 win279))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win280 win281) (parent_range_join _ _ _ win282 win283)) (parent_range_join _ _ _ (parent_range_join _ _ _ win284 win285) (parent_range_join _ _ _ win286 win287))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win288 win289) (parent_range_join _ _ _ win290 win291)) (parent_range_join _ _ _ (parent_range_join _ _ _ win292 win293) (parent_range_join _ _ _ win294 win295))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win296 win297) (parent_range_join _ _ _ win298 win299)) (parent_range_join _ _ _ (parent_range_join _ _ _ win300 win301) (parent_range_join _ _ _ win302 win303)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win304 win305) (parent_range_join _ _ _ win306 win307)) (parent_range_join _ _ _ (parent_range_join _ _ _ win308 win309) (parent_range_join _ _ _ win310 win311))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win312 win313) (parent_range_join _ _ _ win314 win315)) (parent_range_join _ _ _ (parent_range_join _ _ _ win316 win317) (parent_range_join _ _ _ win318 win319))))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win320 win321) (parent_range_join _ _ _ win322 win323)) (parent_range_join _ _ _ (parent_range_join _ _ _ win324 win325) (parent_range_join _ _ _ win326 win327))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win328 win329) (parent_range_join _ _ _ win330 win331)) (parent_range_join _ _ _ (parent_range_join _ _ _ win332 win333) (parent_range_join _ _ _ win334 win335)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win336 win337) (parent_range_join _ _ _ win338 win339)) (parent_range_join _ _ _ (parent_range_join _ _ _ win340 win341) (parent_range_join _ _ _ win342 win343))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win344 win345) (parent_range_join _ _ _ win346 win347)) (parent_range_join _ _ _ (parent_range_join _ _ _ win348 win349) (parent_range_join _ _ _ win350 win351))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win352 win353) (parent_range_join _ _ _ win354 win355)) (parent_range_join _ _ _ (parent_range_join _ _ _ win356 win357) (parent_range_join _ _ _ win358 win359))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win360 win361) (parent_range_join _ _ _ win362 win363)) (parent_range_join _ _ _ (parent_range_join _ _ _ win364 win365) (parent_range_join _ _ _ win366 win367)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win368 win369) (parent_range_join _ _ _ win370 win371)) (parent_range_join _ _ _ (parent_range_join _ _ _ win372 win373) (parent_range_join _ _ _ win374 win375))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win376 win377) (parent_range_join _ _ _ win378 win379)) (parent_range_join _ _ _ (parent_range_join _ _ _ win380 win381) (parent_range_join _ _ _ win382 win383)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ win384 win385) (parent_range_join _ _ _ win386 win387)) (parent_range_join _ _ _ (parent_range_join _ _ _ win388 win389) (parent_range_join _ _ _ win390 win391))) (parent_range_join _ _ _ win392 (parent_range_join _ _ _ win393 win394))))))

attribute [local irreducible] ArtifactEncoding.decode

def packedWideCommitImage : Image :=
  ⟨ArtifactEncoding.decode 32 GroupedArtifact.commitCode,ArtifactEncoding.decode 8 GroupedArtifact.commitData⟩

theorem packed_manifest_image : packedWideCommitImage = GroupedArtifact.submission.image .commit := by
  simp only [packedWideCommitImage,GroupedArtifact.submission]

private theorem wide_commit_code :
    packedWideCommitImage.code = ArtifactEncoding.decode 32 GroupedArtifact.commitCode := by
  simp only [packedWideCommitImage]

theorem packed_index_fetch (state : MachineState) (index : Nat)
    (point : state.pc=BitVec.ofNat 64 (4096+4*index))
    (lower : (70178 : Nat) ≤ index) (upper : index < 201767) :
    fetch packedWideCommitImage state=decodeInstruction (expectedWord index) := by
  have pc : state.pc.toNat=4096+4*index := by
    rw [point,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inPacked : index<201767 := by omega
  have packed := parent_packed_matches ⟨index,inPacked⟩
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


private theorem wide_parent_opcode (state : MachineState) (slot : Nat)
    (bounded : slot<32894) (part : Fin 4)
    (pc : state.pc=packedParentPC 284808 slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (parentWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(70178+4*slot+part.val)) := by
    rw [pc,packedParentPC]
    change BitVec.ofNat 64 284808+BitVec.ofNat 64 (16*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  have lower : 70178≤70178+4*slot+part.val := by omega
  have upper : 70178+4*slot+part.val<201767 := by omega
  rw [packed_index_fetch state (70178+4*slot+part.val) address lower upper]
  rw [expectedWord,if_pos (by omega)]
  simp only [parentWord]
  have phase : ((70178+4*slot+part.val)-70178)%4=part.val%4 := by omega
  rw [phase]

theorem packed_parent_words (slot : Nat) (bounded : slot<32894) :
    PackedParentWordsAt packedWideCommitImage (packedParentPC 284808 slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · have fetched := wide_parent_opcode state slot bounded 0 (by simpa using pc)
    exact fetched
  · exact wide_parent_opcode state slot bounded 1 pc
  · exact wide_parent_opcode state slot bounded 2 pc
  · exact wide_parent_opcode state slot bounded 3 pc

def loopBase : Word := 286840

theorem loop_pc (slot : Nat) : packedParentPC 284808 (127+slot) = packedParentPC loopBase slot := by
  unfold packedParentPC loopBase
  change BitVec.ofNat 64 284808+BitVec.ofNat 64 _=BitVec.ofNat 64 286840+BitVec.ofNat 64 _
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add];congr 1 <;> omega

def fixedWideParentControl : PackedParentControl packedWideCommitImage loopBase 32767 where
  backOffset := 1572876
  backTarget := by decide
  branch state pc := packed_index_fetch state 201754 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 201755 pc (by decide) (by decide)

theorem upper_prefix_run (s : MachineState) (fuel : Nat) (r : ParentRegs s 4194303) (pc : s.pc=284808) :
    execute packedWideCommitImage (508+fuel) s true = (do
      let mid ← packedParentsTrace 4194176 127 s
      let e ← execute packedWideCommitImage fuel mid true
      return e.charge 1397 127) :=
  packed_parent_segment packedWideCommitImage 284808 32894 packed_parent_words
    4194176 127 0 fuel s (by decide) (by decide) r (by simpa [packedParentPC] using pc)

theorem upper_loop_run (s : MachineState) (fuel : Nat) (r : ParentRegs s 4194176) (pc : s.pc=loopBase) :
    execute packedWideCommitImage (16776959+fuel) s true = (do
      let mid ← packedParentGroups loopBase 32767 128 s
      let e ← execute packedWideCommitImage fuel mid true
      return e.charge 46136191 4194176) := by
  have fetches (i : Nat) (hi : i<32767) : PackedParentWordsAt packedWideCommitImage (packedParentPC loopBase i) := by
    rw [←loop_pc]
    exact packed_parent_words (127+i) (by omega)
  exact packed_group_execution packedWideCommitImage loopBase 32767 fetches
    fixedWideParentControl (by decide) 128 fuel s (by decide) r (fun _ => pc)

private theorem wide_root_fetch (state : MachineState) (i : Nat) (inside : i < 11)
    (pc : state.pc=BitVec.ofNat 64 (811120+4*i)) :
    fetch packedWideCommitImage state=some (.base ((rootOps[i]?).getD .ECALL)) := by
  have address : state.pc=BitVec.ofNat 64 (4096+4*(201756+i)) := by
    rw [pc]
    congr 1
    omega
  rw [packed_index_fetch state (201756+i) address (by omega) (by omega)]
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

theorem execute_packed_root (state : MachineState) (pc : state.pc=811120)
    (heap : state.getReg .x9=4294971424) (out : state.getReg .x8=4294971392) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true = pure ⟨.success,rootPrefix state 10,11,0⟩ := by
  have prefixPC (i : Nat) (inside : i<11) :
      (rootPrefix state i).pc=BitVec.ofNat 64 (811120+4*i) := by
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

end TwoPermutationPrototype.GroupedUpper
