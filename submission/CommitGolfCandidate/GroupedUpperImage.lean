import CommitGolfCandidate.K1Manifest
import CommitGolfCandidate.K3CUBands
import CommitGolfCandidate.TwoPermutationRoot

/-!
# The decoded commit tail (4-tile unrolled image with optimal upper-band spans)
-/

namespace TwoPermutationPrototype.GroupedUpper
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

def tailStart : Nat := 181047
def l21SetupLen : Nat := 7
def l21Span : Nat := 8192
def l21Passes : Nat := 256
def bandASpan : Nat := 10240
def bandAPasses : Nat := 192
def bandBSpan : Nat := 2570
def bandBPasses : Nat := 51
def l21Base : Word := 728312
def heapSetupPC : Word := 826624
def bandABase : Word := 826652
def midPC : Word := 990500
def bandBBase : Word := 990504
def rootParentPC : Word := 1052192
def rootPC : Word := 1052208

def l21SetupOps : List Instr :=
  [.ADDI .x11 .x0 64,.ADDI .x13 .x0 0,.ADDI .x7 .x21 2184,.ADDI .x10 .x24 2184,.LUI .x12 32768,.ADD .x12 .x12 .x9,.ADDI .x12 .x12 4064]
def heapSetupOps : List Instr :=
  [.SUB .x10 .x12 .x9,.ADD .x10 .x10 .x12,.LUI .x7 1024,.ADD .x7 .x7 .x9,.ADDI .x7 .x7 4064,.LUI .x6 4,.ADDI .x6 .x6 4095]

private def l21Word (phase : Nat) : BitVec 32 :=
  if phase%3=0 then 0x00000073 else if phase%3=1 then 0x80050513 else 0xfe060613
private def bandAWord (phase : Nat) : BitVec 32 :=
  if phase%4=0 then 0x00000073 else if phase%4=1 then 0x00061f23 else if phase%4=2 then 0xfc050513 else 0xfe060613
private def bandBWord (phase : Nat) : BitVec 32 :=
  if phase%6=0 then 0x00000073 else if phase%6=1 then 0x01c65f83 else if phase%6=2 then 0x006fffb3 else if phase%6=3 then 0x01f62e23 else if phase%6=4 then 0xfc050513 else 0xfe060613
private def lit0Words : List (BitVec 32) := [0x04000593,0x00000693,0x888a8393,0x888c0513,0x08000637,0x00960633,0xfe060613]
private def lit1Words : List (BitVec 32) := [0x00750463,0xffde706f,0x40960533,0x00c50533,0x004003b7,0x009383b3,0xfe038393,0x00004337,0xfff30313]
private def lit2Words : List (BitVec 32) := [0x00760463,0xffdd706f,0x02048393]
private def lit3Words : List (BitVec 32) := [0x00760463,0xf0df006f,0x00000073,0x01c65f83,0x006fffb3,0x01f62e23,0x0204bf83,0x01f43023,0x0284bf83,0x01f43423,0x0304bf83,0x01f43823,0x0384bf83,0x01f43c23,0x00100293,0x00000513,0x00000073]

private def expectedWord (index : Nat) : BitVec 32 :=
  if index<181054 then lit0Words.getD (index-181047) 0
  else if index<205630 then l21Word (index-181054)
  else if index<205639 then lit1Words.getD (index-205630) 0
  else if index<246599 then bandAWord (index-205639)
  else if index<246602 then lit2Words.getD (index-246599) 0
  else if index<262022 then bandBWord (index-246602)
  else if index<262039 then lit3Words.getD (index-262022) 0
  else 0

private def ParentRangeMatches {count : Nat} (packed : ArtifactEncoding.Packed count) (offset : Nat) : Prop :=
  ∀ i : Fin count, 181047≤offset+i.val → offset+i.val<262039 → packed.get 32 i=expectedWord (offset+i.val)

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

private theorem l21_periodic_window (packed : ArtifactEncoding.Packed 512)
    (offset phase : Nat) (alignment : (offset-181054)%3=phase%3)
    (inside : 181054≤offset) (ends : offset+512≤205630)
    (decode : ∀ i : Fin 512, packed.get 32 i=l21Word (phase+i.val)) :
    ParentRangeMatches packed offset := by
  intro i _ _
  have before := i.isLt
  rw [expectedWord,if_neg (by omega),if_pos (by omega),decode]
  simp only [l21Word]
  have same : (phase+i.val)%3=(offset+i.val-181054)%3 := by omega
  rw [same]

private theorem bandA_periodic_window (packed : ArtifactEncoding.Packed 512)
    (offset phase : Nat) (alignment : (offset-205639)%4=phase%4)
    (inside : 205639≤offset) (ends : offset+512≤246599)
    (decode : ∀ i : Fin 512, packed.get 32 i=bandAWord (phase+i.val)) :
    ParentRangeMatches packed offset := by
  intro i _ _
  have before := i.isLt
  rw [expectedWord,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),decode]
  simp only [bandAWord]
  have same : (phase+i.val)%4=(offset+i.val-205639)%4 := by omega
  rw [same]

private theorem bandB_periodic_window (packed : ArtifactEncoding.Packed 512)
    (offset phase : Nat) (alignment : (offset-246602)%6=phase%6)
    (inside : 246602≤offset) (ends : offset+512≤262022)
    (decode : ∀ i : Fin 512, packed.get 32 i=bandBWord (phase+i.val)) :
    ParentRangeMatches packed offset := by
  intro i _ _
  have before := i.isLt
  rw [expectedWord,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),decode]
  simp only [bandBWord]
  have same : (phase+i.val)%6=(offset+i.val-246602)%6 := by omega
  rw [same]

private theorem l21_periodic_0 (i : Fin 512) :
    K1Artifact.commitCode_0_356.get 32 i = l21Word (0+i.val) := by
  revert i; decide +kernel
private theorem l21_periodic_1 (i : Fin 512) :
    K1Artifact.commitCode_0_355.get 32 i = l21Word (1+i.val) := by
  revert i; decide +kernel
private theorem l21_periodic_2 (i : Fin 512) :
    K1Artifact.commitCode_0_354.get 32 i = l21Word (2+i.val) := by
  revert i; decide +kernel
private theorem bandA_periodic_1 (i : Fin 512) :
    K1Artifact.commitCode_0_402.get 32 i = bandAWord (1+i.val) := by
  revert i; decide +kernel
private theorem bandB_periodic_0 (i : Fin 512) :
    K1Artifact.commitCode_0_484.get 32 i = bandBWord (0+i.val) := by
  revert i; decide +kernel
private theorem bandB_periodic_2 (i : Fin 512) :
    K1Artifact.commitCode_0_482.get 32 i = bandBWord (2+i.val) := by
  revert i; decide +kernel
private theorem bandB_periodic_4 (i : Fin 512) :
    K1Artifact.commitCode_0_483.get 32 i = bandBWord (4+i.val) := by
  revert i; decide +kernel

private theorem win0 : ParentRangeMatches K1Artifact.commitCode_0_0 0 := by
  intro i lo _; have h := i.isLt; omega
private theorem win1 : ParentRangeMatches K1Artifact.commitCode_0_1 512 := by
  intro i lo _; have h := i.isLt; omega
private theorem win2 : ParentRangeMatches K1Artifact.commitCode_0_2 1024 := by
  intro i lo _; have h := i.isLt; omega
private theorem win3 : ParentRangeMatches K1Artifact.commitCode_0_3 1536 := by
  intro i lo _; have h := i.isLt; omega
private theorem win4 : ParentRangeMatches K1Artifact.commitCode_0_4 2048 := by
  intro i lo _; have h := i.isLt; omega
private theorem win5 : ParentRangeMatches K1Artifact.commitCode_0_5 2560 := by
  intro i lo _; have h := i.isLt; omega
private theorem win6 : ParentRangeMatches K1Artifact.commitCode_0_6 3072 := by
  intro i lo _; have h := i.isLt; omega
private theorem win7 : ParentRangeMatches K1Artifact.commitCode_0_7 3584 := by
  intro i lo _; have h := i.isLt; omega
private theorem win8 : ParentRangeMatches K1Artifact.commitCode_0_8 4096 := by
  intro i lo _; have h := i.isLt; omega
private theorem win9 : ParentRangeMatches K1Artifact.commitCode_0_9 4608 := by
  intro i lo _; have h := i.isLt; omega
private theorem win10 : ParentRangeMatches K1Artifact.commitCode_0_10 5120 := by
  intro i lo _; have h := i.isLt; omega
private theorem win11 : ParentRangeMatches K1Artifact.commitCode_0_11 5632 := by
  intro i lo _; have h := i.isLt; omega
private theorem win12 : ParentRangeMatches K1Artifact.commitCode_0_12 6144 := by
  intro i lo _; have h := i.isLt; omega
private theorem win13 : ParentRangeMatches K1Artifact.commitCode_0_13 6656 := by
  intro i lo _; have h := i.isLt; omega
private theorem win14 : ParentRangeMatches K1Artifact.commitCode_0_14 7168 := by
  intro i lo _; have h := i.isLt; omega
private theorem win15 : ParentRangeMatches K1Artifact.commitCode_0_15 7680 := by
  intro i lo _; have h := i.isLt; omega
private theorem win16 : ParentRangeMatches K1Artifact.commitCode_0_16 8192 := by
  intro i lo _; have h := i.isLt; omega
private theorem win17 : ParentRangeMatches K1Artifact.commitCode_0_17 8704 := by
  intro i lo _; have h := i.isLt; omega
private theorem win18 : ParentRangeMatches K1Artifact.commitCode_0_18 9216 := by
  intro i lo _; have h := i.isLt; omega
private theorem win19 : ParentRangeMatches K1Artifact.commitCode_0_19 9728 := by
  intro i lo _; have h := i.isLt; omega
private theorem win20 : ParentRangeMatches K1Artifact.commitCode_0_20 10240 := by
  intro i lo _; have h := i.isLt; omega
private theorem win21 : ParentRangeMatches K1Artifact.commitCode_0_21 10752 := by
  intro i lo _; have h := i.isLt; omega
private theorem win22 : ParentRangeMatches K1Artifact.commitCode_0_22 11264 := by
  intro i lo _; have h := i.isLt; omega
private theorem win23 : ParentRangeMatches K1Artifact.commitCode_0_23 11776 := by
  intro i lo _; have h := i.isLt; omega
private theorem win24 : ParentRangeMatches K1Artifact.commitCode_0_24 12288 := by
  intro i lo _; have h := i.isLt; omega
private theorem win25 : ParentRangeMatches K1Artifact.commitCode_0_25 12800 := by
  intro i lo _; have h := i.isLt; omega
private theorem win26 : ParentRangeMatches K1Artifact.commitCode_0_26 13312 := by
  intro i lo _; have h := i.isLt; omega
private theorem win27 : ParentRangeMatches K1Artifact.commitCode_0_27 13824 := by
  intro i lo _; have h := i.isLt; omega
private theorem win28 : ParentRangeMatches K1Artifact.commitCode_0_28 14336 := by
  intro i lo _; have h := i.isLt; omega
private theorem win29 : ParentRangeMatches K1Artifact.commitCode_0_29 14848 := by
  intro i lo _; have h := i.isLt; omega
private theorem win30 : ParentRangeMatches K1Artifact.commitCode_0_30 15360 := by
  intro i lo _; have h := i.isLt; omega
private theorem win31 : ParentRangeMatches K1Artifact.commitCode_0_31 15872 := by
  intro i lo _; have h := i.isLt; omega
private theorem win32 : ParentRangeMatches K1Artifact.commitCode_0_32 16384 := by
  intro i lo _; have h := i.isLt; omega
private theorem win33 : ParentRangeMatches K1Artifact.commitCode_0_33 16896 := by
  intro i lo _; have h := i.isLt; omega
private theorem win34 : ParentRangeMatches K1Artifact.commitCode_0_34 17408 := by
  intro i lo _; have h := i.isLt; omega
private theorem win35 : ParentRangeMatches K1Artifact.commitCode_0_35 17920 := by
  intro i lo _; have h := i.isLt; omega
private theorem win36 : ParentRangeMatches K1Artifact.commitCode_0_36 18432 := by
  intro i lo _; have h := i.isLt; omega
private theorem win37 : ParentRangeMatches K1Artifact.commitCode_0_37 18944 := by
  intro i lo _; have h := i.isLt; omega
private theorem win38 : ParentRangeMatches K1Artifact.commitCode_0_38 19456 := by
  intro i lo _; have h := i.isLt; omega
private theorem win39 : ParentRangeMatches K1Artifact.commitCode_0_39 19968 := by
  intro i lo _; have h := i.isLt; omega
private theorem win40 : ParentRangeMatches K1Artifact.commitCode_0_40 20480 := by
  intro i lo _; have h := i.isLt; omega
private theorem win41 : ParentRangeMatches K1Artifact.commitCode_0_41 20992 := by
  intro i lo _; have h := i.isLt; omega
private theorem win42 : ParentRangeMatches K1Artifact.commitCode_0_42 21504 := by
  intro i lo _; have h := i.isLt; omega
private theorem win43 : ParentRangeMatches K1Artifact.commitCode_0_43 22016 := by
  intro i lo _; have h := i.isLt; omega
private theorem win44 : ParentRangeMatches K1Artifact.commitCode_0_44 22528 := by
  intro i lo _; have h := i.isLt; omega
private theorem win45 : ParentRangeMatches K1Artifact.commitCode_0_45 23040 := by
  intro i lo _; have h := i.isLt; omega
private theorem win46 : ParentRangeMatches K1Artifact.commitCode_0_46 23552 := by
  intro i lo _; have h := i.isLt; omega
private theorem win47 : ParentRangeMatches K1Artifact.commitCode_0_47 24064 := by
  intro i lo _; have h := i.isLt; omega
private theorem win48 : ParentRangeMatches K1Artifact.commitCode_0_48 24576 := by
  intro i lo _; have h := i.isLt; omega
private theorem win49 : ParentRangeMatches K1Artifact.commitCode_0_49 25088 := by
  intro i lo _; have h := i.isLt; omega
private theorem win50 : ParentRangeMatches K1Artifact.commitCode_0_50 25600 := by
  intro i lo _; have h := i.isLt; omega
private theorem win51 : ParentRangeMatches K1Artifact.commitCode_0_51 26112 := by
  intro i lo _; have h := i.isLt; omega
private theorem win52 : ParentRangeMatches K1Artifact.commitCode_0_52 26624 := by
  intro i lo _; have h := i.isLt; omega
private theorem win53 : ParentRangeMatches K1Artifact.commitCode_0_53 27136 := by
  intro i lo _; have h := i.isLt; omega
private theorem win54 : ParentRangeMatches K1Artifact.commitCode_0_54 27648 := by
  intro i lo _; have h := i.isLt; omega
private theorem win55 : ParentRangeMatches K1Artifact.commitCode_0_55 28160 := by
  intro i lo _; have h := i.isLt; omega
private theorem win56 : ParentRangeMatches K1Artifact.commitCode_0_56 28672 := by
  intro i lo _; have h := i.isLt; omega
private theorem win57 : ParentRangeMatches K1Artifact.commitCode_0_57 29184 := by
  intro i lo _; have h := i.isLt; omega
private theorem win58 : ParentRangeMatches K1Artifact.commitCode_0_58 29696 := by
  intro i lo _; have h := i.isLt; omega
private theorem win59 : ParentRangeMatches K1Artifact.commitCode_0_59 30208 := by
  intro i lo _; have h := i.isLt; omega
private theorem win60 : ParentRangeMatches K1Artifact.commitCode_0_60 30720 := by
  intro i lo _; have h := i.isLt; omega
private theorem win61 : ParentRangeMatches K1Artifact.commitCode_0_61 31232 := by
  intro i lo _; have h := i.isLt; omega
private theorem win62 : ParentRangeMatches K1Artifact.commitCode_0_62 31744 := by
  intro i lo _; have h := i.isLt; omega
private theorem win63 : ParentRangeMatches K1Artifact.commitCode_0_63 32256 := by
  intro i lo _; have h := i.isLt; omega
private theorem win64 : ParentRangeMatches K1Artifact.commitCode_0_64 32768 := by
  intro i lo _; have h := i.isLt; omega
private theorem win65 : ParentRangeMatches K1Artifact.commitCode_0_65 33280 := by
  intro i lo _; have h := i.isLt; omega
private theorem win66 : ParentRangeMatches K1Artifact.commitCode_0_66 33792 := by
  intro i lo _; have h := i.isLt; omega
private theorem win67 : ParentRangeMatches K1Artifact.commitCode_0_67 34304 := by
  intro i lo _; have h := i.isLt; omega
private theorem win68 : ParentRangeMatches K1Artifact.commitCode_0_68 34816 := by
  intro i lo _; have h := i.isLt; omega
private theorem win69 : ParentRangeMatches K1Artifact.commitCode_0_69 35328 := by
  intro i lo _; have h := i.isLt; omega
private theorem win70 : ParentRangeMatches K1Artifact.commitCode_0_70 35840 := by
  intro i lo _; have h := i.isLt; omega
private theorem win71 : ParentRangeMatches K1Artifact.commitCode_0_71 36352 := by
  intro i lo _; have h := i.isLt; omega
private theorem win72 : ParentRangeMatches K1Artifact.commitCode_0_72 36864 := by
  intro i lo _; have h := i.isLt; omega
private theorem win73 : ParentRangeMatches K1Artifact.commitCode_0_73 37376 := by
  intro i lo _; have h := i.isLt; omega
private theorem win74 : ParentRangeMatches K1Artifact.commitCode_0_74 37888 := by
  intro i lo _; have h := i.isLt; omega
private theorem win75 : ParentRangeMatches K1Artifact.commitCode_0_75 38400 := by
  intro i lo _; have h := i.isLt; omega
private theorem win76 : ParentRangeMatches K1Artifact.commitCode_0_76 38912 := by
  intro i lo _; have h := i.isLt; omega
private theorem win77 : ParentRangeMatches K1Artifact.commitCode_0_77 39424 := by
  intro i lo _; have h := i.isLt; omega
private theorem win78 : ParentRangeMatches K1Artifact.commitCode_0_78 39936 := by
  intro i lo _; have h := i.isLt; omega
private theorem win79 : ParentRangeMatches K1Artifact.commitCode_0_79 40448 := by
  intro i lo _; have h := i.isLt; omega
private theorem win80 : ParentRangeMatches K1Artifact.commitCode_0_80 40960 := by
  intro i lo _; have h := i.isLt; omega
private theorem win81 : ParentRangeMatches K1Artifact.commitCode_0_81 41472 := by
  intro i lo _; have h := i.isLt; omega
private theorem win82 : ParentRangeMatches K1Artifact.commitCode_0_82 41984 := by
  intro i lo _; have h := i.isLt; omega
private theorem win83 : ParentRangeMatches K1Artifact.commitCode_0_83 42496 := by
  intro i lo _; have h := i.isLt; omega
private theorem win84 : ParentRangeMatches K1Artifact.commitCode_0_84 43008 := by
  intro i lo _; have h := i.isLt; omega
private theorem win85 : ParentRangeMatches K1Artifact.commitCode_0_85 43520 := by
  intro i lo _; have h := i.isLt; omega
private theorem win86 : ParentRangeMatches K1Artifact.commitCode_0_86 44032 := by
  intro i lo _; have h := i.isLt; omega
private theorem win87 : ParentRangeMatches K1Artifact.commitCode_0_87 44544 := by
  intro i lo _; have h := i.isLt; omega
private theorem win88 : ParentRangeMatches K1Artifact.commitCode_0_88 45056 := by
  intro i lo _; have h := i.isLt; omega
private theorem win89 : ParentRangeMatches K1Artifact.commitCode_0_89 45568 := by
  intro i lo _; have h := i.isLt; omega
private theorem win90 : ParentRangeMatches K1Artifact.commitCode_0_90 46080 := by
  intro i lo _; have h := i.isLt; omega
private theorem win91 : ParentRangeMatches K1Artifact.commitCode_0_91 46592 := by
  intro i lo _; have h := i.isLt; omega
private theorem win92 : ParentRangeMatches K1Artifact.commitCode_0_92 47104 := by
  intro i lo _; have h := i.isLt; omega
private theorem win93 : ParentRangeMatches K1Artifact.commitCode_0_93 47616 := by
  intro i lo _; have h := i.isLt; omega
private theorem win94 : ParentRangeMatches K1Artifact.commitCode_0_94 48128 := by
  intro i lo _; have h := i.isLt; omega
private theorem win95 : ParentRangeMatches K1Artifact.commitCode_0_95 48640 := by
  intro i lo _; have h := i.isLt; omega
private theorem win96 : ParentRangeMatches K1Artifact.commitCode_0_96 49152 := by
  intro i lo _; have h := i.isLt; omega
private theorem win97 : ParentRangeMatches K1Artifact.commitCode_0_97 49664 := by
  intro i lo _; have h := i.isLt; omega
private theorem win98 : ParentRangeMatches K1Artifact.commitCode_0_98 50176 := by
  intro i lo _; have h := i.isLt; omega
private theorem win99 : ParentRangeMatches K1Artifact.commitCode_0_99 50688 := by
  intro i lo _; have h := i.isLt; omega
private theorem win100 : ParentRangeMatches K1Artifact.commitCode_0_100 51200 := by
  intro i lo _; have h := i.isLt; omega
private theorem win101 : ParentRangeMatches K1Artifact.commitCode_0_101 51712 := by
  intro i lo _; have h := i.isLt; omega
private theorem win102 : ParentRangeMatches K1Artifact.commitCode_0_102 52224 := by
  intro i lo _; have h := i.isLt; omega
private theorem win103 : ParentRangeMatches K1Artifact.commitCode_0_103 52736 := by
  intro i lo _; have h := i.isLt; omega
private theorem win104 : ParentRangeMatches K1Artifact.commitCode_0_104 53248 := by
  intro i lo _; have h := i.isLt; omega
private theorem win105 : ParentRangeMatches K1Artifact.commitCode_0_105 53760 := by
  intro i lo _; have h := i.isLt; omega
private theorem win106 : ParentRangeMatches K1Artifact.commitCode_0_106 54272 := by
  intro i lo _; have h := i.isLt; omega
private theorem win107 : ParentRangeMatches K1Artifact.commitCode_0_107 54784 := by
  intro i lo _; have h := i.isLt; omega
private theorem win108 : ParentRangeMatches K1Artifact.commitCode_0_108 55296 := by
  intro i lo _; have h := i.isLt; omega
private theorem win109 : ParentRangeMatches K1Artifact.commitCode_0_109 55808 := by
  intro i lo _; have h := i.isLt; omega
private theorem win110 : ParentRangeMatches K1Artifact.commitCode_0_110 56320 := by
  intro i lo _; have h := i.isLt; omega
private theorem win111 : ParentRangeMatches K1Artifact.commitCode_0_111 56832 := by
  intro i lo _; have h := i.isLt; omega
private theorem win112 : ParentRangeMatches K1Artifact.commitCode_0_112 57344 := by
  intro i lo _; have h := i.isLt; omega
private theorem win113 : ParentRangeMatches K1Artifact.commitCode_0_113 57856 := by
  intro i lo _; have h := i.isLt; omega
private theorem win114 : ParentRangeMatches K1Artifact.commitCode_0_114 58368 := by
  intro i lo _; have h := i.isLt; omega
private theorem win115 : ParentRangeMatches K1Artifact.commitCode_0_115 58880 := by
  intro i lo _; have h := i.isLt; omega
private theorem win116 : ParentRangeMatches K1Artifact.commitCode_0_116 59392 := by
  intro i lo _; have h := i.isLt; omega
private theorem win117 : ParentRangeMatches K1Artifact.commitCode_0_117 59904 := by
  intro i lo _; have h := i.isLt; omega
private theorem win118 : ParentRangeMatches K1Artifact.commitCode_0_118 60416 := by
  intro i lo _; have h := i.isLt; omega
private theorem win119 : ParentRangeMatches K1Artifact.commitCode_0_119 60928 := by
  intro i lo _; have h := i.isLt; omega
private theorem win120 : ParentRangeMatches K1Artifact.commitCode_0_120 61440 := by
  intro i lo _; have h := i.isLt; omega
private theorem win121 : ParentRangeMatches K1Artifact.commitCode_0_121 61952 := by
  intro i lo _; have h := i.isLt; omega
private theorem win122 : ParentRangeMatches K1Artifact.commitCode_0_122 62464 := by
  intro i lo _; have h := i.isLt; omega
private theorem win123 : ParentRangeMatches K1Artifact.commitCode_0_123 62976 := by
  intro i lo _; have h := i.isLt; omega
private theorem win124 : ParentRangeMatches K1Artifact.commitCode_0_124 63488 := by
  intro i lo _; have h := i.isLt; omega
private theorem win125 : ParentRangeMatches K1Artifact.commitCode_0_125 64000 := by
  intro i lo _; have h := i.isLt; omega
private theorem win126 : ParentRangeMatches K1Artifact.commitCode_0_126 64512 := by
  intro i lo _; have h := i.isLt; omega
private theorem win127 : ParentRangeMatches K1Artifact.commitCode_0_127 65024 := by
  intro i lo _; have h := i.isLt; omega
private theorem win128 : ParentRangeMatches K1Artifact.commitCode_0_128 65536 := by
  intro i lo _; have h := i.isLt; omega
private theorem win129 : ParentRangeMatches K1Artifact.commitCode_0_129 66048 := by
  intro i lo _; have h := i.isLt; omega
private theorem win130 : ParentRangeMatches K1Artifact.commitCode_0_130 66560 := by
  intro i lo _; have h := i.isLt; omega
private theorem win131 : ParentRangeMatches K1Artifact.commitCode_0_131 67072 := by
  intro i lo _; have h := i.isLt; omega
private theorem win132 : ParentRangeMatches K1Artifact.commitCode_0_132 67584 := by
  intro i lo _; have h := i.isLt; omega
private theorem win133 : ParentRangeMatches K1Artifact.commitCode_0_133 68096 := by
  intro i lo _; have h := i.isLt; omega
private theorem win134 : ParentRangeMatches K1Artifact.commitCode_0_134 68608 := by
  intro i lo _; have h := i.isLt; omega
private theorem win135 : ParentRangeMatches K1Artifact.commitCode_0_135 69120 := by
  intro i lo _; have h := i.isLt; omega
private theorem win136 : ParentRangeMatches K1Artifact.commitCode_0_136 69632 := by
  intro i lo _; have h := i.isLt; omega
private theorem win137 : ParentRangeMatches K1Artifact.commitCode_0_137 70144 := by
  intro i lo _; have h := i.isLt; omega
private theorem win138 : ParentRangeMatches K1Artifact.commitCode_0_138 70656 := by
  intro i lo _; have h := i.isLt; omega
private theorem win139 : ParentRangeMatches K1Artifact.commitCode_0_139 71168 := by
  intro i lo _; have h := i.isLt; omega
private theorem win140 : ParentRangeMatches K1Artifact.commitCode_0_140 71680 := by
  intro i lo _; have h := i.isLt; omega
private theorem win141 : ParentRangeMatches K1Artifact.commitCode_0_141 72192 := by
  intro i lo _; have h := i.isLt; omega
private theorem win142 : ParentRangeMatches K1Artifact.commitCode_0_142 72704 := by
  intro i lo _; have h := i.isLt; omega
private theorem win143 : ParentRangeMatches K1Artifact.commitCode_0_143 73216 := by
  intro i lo _; have h := i.isLt; omega
private theorem win144 : ParentRangeMatches K1Artifact.commitCode_0_144 73728 := by
  intro i lo _; have h := i.isLt; omega
private theorem win145 : ParentRangeMatches K1Artifact.commitCode_0_145 74240 := by
  intro i lo _; have h := i.isLt; omega
private theorem win146 : ParentRangeMatches K1Artifact.commitCode_0_146 74752 := by
  intro i lo _; have h := i.isLt; omega
private theorem win147 : ParentRangeMatches K1Artifact.commitCode_0_147 75264 := by
  intro i lo _; have h := i.isLt; omega
private theorem win148 : ParentRangeMatches K1Artifact.commitCode_0_148 75776 := by
  intro i lo _; have h := i.isLt; omega
private theorem win149 : ParentRangeMatches K1Artifact.commitCode_0_149 76288 := by
  intro i lo _; have h := i.isLt; omega
private theorem win150 : ParentRangeMatches K1Artifact.commitCode_0_150 76800 := by
  intro i lo _; have h := i.isLt; omega
private theorem win151 : ParentRangeMatches K1Artifact.commitCode_0_151 77312 := by
  intro i lo _; have h := i.isLt; omega
private theorem win152 : ParentRangeMatches K1Artifact.commitCode_0_152 77824 := by
  intro i lo _; have h := i.isLt; omega
private theorem win153 : ParentRangeMatches K1Artifact.commitCode_0_153 78336 := by
  intro i lo _; have h := i.isLt; omega
private theorem win154 : ParentRangeMatches K1Artifact.commitCode_0_154 78848 := by
  intro i lo _; have h := i.isLt; omega
private theorem win155 : ParentRangeMatches K1Artifact.commitCode_0_155 79360 := by
  intro i lo _; have h := i.isLt; omega
private theorem win156 : ParentRangeMatches K1Artifact.commitCode_0_156 79872 := by
  intro i lo _; have h := i.isLt; omega
private theorem win157 : ParentRangeMatches K1Artifact.commitCode_0_157 80384 := by
  intro i lo _; have h := i.isLt; omega
private theorem win158 : ParentRangeMatches K1Artifact.commitCode_0_158 80896 := by
  intro i lo _; have h := i.isLt; omega
private theorem win159 : ParentRangeMatches K1Artifact.commitCode_0_159 81408 := by
  intro i lo _; have h := i.isLt; omega
private theorem win160 : ParentRangeMatches K1Artifact.commitCode_0_160 81920 := by
  intro i lo _; have h := i.isLt; omega
private theorem win161 : ParentRangeMatches K1Artifact.commitCode_0_161 82432 := by
  intro i lo _; have h := i.isLt; omega
private theorem win162 : ParentRangeMatches K1Artifact.commitCode_0_162 82944 := by
  intro i lo _; have h := i.isLt; omega
private theorem win163 : ParentRangeMatches K1Artifact.commitCode_0_163 83456 := by
  intro i lo _; have h := i.isLt; omega
private theorem win164 : ParentRangeMatches K1Artifact.commitCode_0_164 83968 := by
  intro i lo _; have h := i.isLt; omega
private theorem win165 : ParentRangeMatches K1Artifact.commitCode_0_165 84480 := by
  intro i lo _; have h := i.isLt; omega
private theorem win166 : ParentRangeMatches K1Artifact.commitCode_0_166 84992 := by
  intro i lo _; have h := i.isLt; omega
private theorem win167 : ParentRangeMatches K1Artifact.commitCode_0_167 85504 := by
  intro i lo _; have h := i.isLt; omega
private theorem win168 : ParentRangeMatches K1Artifact.commitCode_0_168 86016 := by
  intro i lo _; have h := i.isLt; omega
private theorem win169 : ParentRangeMatches K1Artifact.commitCode_0_169 86528 := by
  intro i lo _; have h := i.isLt; omega
private theorem win170 : ParentRangeMatches K1Artifact.commitCode_0_170 87040 := by
  intro i lo _; have h := i.isLt; omega
private theorem win171 : ParentRangeMatches K1Artifact.commitCode_0_171 87552 := by
  intro i lo _; have h := i.isLt; omega
private theorem win172 : ParentRangeMatches K1Artifact.commitCode_0_172 88064 := by
  intro i lo _; have h := i.isLt; omega
private theorem win173 : ParentRangeMatches K1Artifact.commitCode_0_173 88576 := by
  intro i lo _; have h := i.isLt; omega
private theorem win174 : ParentRangeMatches K1Artifact.commitCode_0_174 89088 := by
  intro i lo _; have h := i.isLt; omega
private theorem win175 : ParentRangeMatches K1Artifact.commitCode_0_175 89600 := by
  intro i lo _; have h := i.isLt; omega
private theorem win176 : ParentRangeMatches K1Artifact.commitCode_0_176 90112 := by
  intro i lo _; have h := i.isLt; omega
private theorem win177 : ParentRangeMatches K1Artifact.commitCode_0_177 90624 := by
  intro i lo _; have h := i.isLt; omega
private theorem win178 : ParentRangeMatches K1Artifact.commitCode_0_178 91136 := by
  intro i lo _; have h := i.isLt; omega
private theorem win179 : ParentRangeMatches K1Artifact.commitCode_0_179 91648 := by
  intro i lo _; have h := i.isLt; omega
private theorem win180 : ParentRangeMatches K1Artifact.commitCode_0_180 92160 := by
  intro i lo _; have h := i.isLt; omega
private theorem win181 : ParentRangeMatches K1Artifact.commitCode_0_181 92672 := by
  intro i lo _; have h := i.isLt; omega
private theorem win182 : ParentRangeMatches K1Artifact.commitCode_0_182 93184 := by
  intro i lo _; have h := i.isLt; omega
private theorem win183 : ParentRangeMatches K1Artifact.commitCode_0_183 93696 := by
  intro i lo _; have h := i.isLt; omega
private theorem win184 : ParentRangeMatches K1Artifact.commitCode_0_184 94208 := by
  intro i lo _; have h := i.isLt; omega
private theorem win185 : ParentRangeMatches K1Artifact.commitCode_0_185 94720 := by
  intro i lo _; have h := i.isLt; omega
private theorem win186 : ParentRangeMatches K1Artifact.commitCode_0_186 95232 := by
  intro i lo _; have h := i.isLt; omega
private theorem win187 : ParentRangeMatches K1Artifact.commitCode_0_187 95744 := by
  intro i lo _; have h := i.isLt; omega
private theorem win188 : ParentRangeMatches K1Artifact.commitCode_0_188 96256 := by
  intro i lo _; have h := i.isLt; omega
private theorem win189 : ParentRangeMatches K1Artifact.commitCode_0_189 96768 := by
  intro i lo _; have h := i.isLt; omega
private theorem win190 : ParentRangeMatches K1Artifact.commitCode_0_190 97280 := by
  intro i lo _; have h := i.isLt; omega
private theorem win191 : ParentRangeMatches K1Artifact.commitCode_0_191 97792 := by
  intro i lo _; have h := i.isLt; omega
private theorem win192 : ParentRangeMatches K1Artifact.commitCode_0_192 98304 := by
  intro i lo _; have h := i.isLt; omega
private theorem win193 : ParentRangeMatches K1Artifact.commitCode_0_193 98816 := by
  intro i lo _; have h := i.isLt; omega
private theorem win194 : ParentRangeMatches K1Artifact.commitCode_0_194 99328 := by
  intro i lo _; have h := i.isLt; omega
private theorem win195 : ParentRangeMatches K1Artifact.commitCode_0_195 99840 := by
  intro i lo _; have h := i.isLt; omega
private theorem win196 : ParentRangeMatches K1Artifact.commitCode_0_196 100352 := by
  intro i lo _; have h := i.isLt; omega
private theorem win197 : ParentRangeMatches K1Artifact.commitCode_0_197 100864 := by
  intro i lo _; have h := i.isLt; omega
private theorem win198 : ParentRangeMatches K1Artifact.commitCode_0_198 101376 := by
  intro i lo _; have h := i.isLt; omega
private theorem win199 : ParentRangeMatches K1Artifact.commitCode_0_199 101888 := by
  intro i lo _; have h := i.isLt; omega
private theorem win200 : ParentRangeMatches K1Artifact.commitCode_0_200 102400 := by
  intro i lo _; have h := i.isLt; omega
private theorem win201 : ParentRangeMatches K1Artifact.commitCode_0_201 102912 := by
  intro i lo _; have h := i.isLt; omega
private theorem win202 : ParentRangeMatches K1Artifact.commitCode_0_202 103424 := by
  intro i lo _; have h := i.isLt; omega
private theorem win203 : ParentRangeMatches K1Artifact.commitCode_0_203 103936 := by
  intro i lo _; have h := i.isLt; omega
private theorem win204 : ParentRangeMatches K1Artifact.commitCode_0_204 104448 := by
  intro i lo _; have h := i.isLt; omega
private theorem win205 : ParentRangeMatches K1Artifact.commitCode_0_205 104960 := by
  intro i lo _; have h := i.isLt; omega
private theorem win206 : ParentRangeMatches K1Artifact.commitCode_0_206 105472 := by
  intro i lo _; have h := i.isLt; omega
private theorem win207 : ParentRangeMatches K1Artifact.commitCode_0_207 105984 := by
  intro i lo _; have h := i.isLt; omega
private theorem win208 : ParentRangeMatches K1Artifact.commitCode_0_208 106496 := by
  intro i lo _; have h := i.isLt; omega
private theorem win209 : ParentRangeMatches K1Artifact.commitCode_0_209 107008 := by
  intro i lo _; have h := i.isLt; omega
private theorem win210 : ParentRangeMatches K1Artifact.commitCode_0_210 107520 := by
  intro i lo _; have h := i.isLt; omega
private theorem win211 : ParentRangeMatches K1Artifact.commitCode_0_211 108032 := by
  intro i lo _; have h := i.isLt; omega
private theorem win212 : ParentRangeMatches K1Artifact.commitCode_0_212 108544 := by
  intro i lo _; have h := i.isLt; omega
private theorem win213 : ParentRangeMatches K1Artifact.commitCode_0_213 109056 := by
  intro i lo _; have h := i.isLt; omega
private theorem win214 : ParentRangeMatches K1Artifact.commitCode_0_214 109568 := by
  intro i lo _; have h := i.isLt; omega
private theorem win215 : ParentRangeMatches K1Artifact.commitCode_0_215 110080 := by
  intro i lo _; have h := i.isLt; omega
private theorem win216 : ParentRangeMatches K1Artifact.commitCode_0_216 110592 := by
  intro i lo _; have h := i.isLt; omega
private theorem win217 : ParentRangeMatches K1Artifact.commitCode_0_217 111104 := by
  intro i lo _; have h := i.isLt; omega
private theorem win218 : ParentRangeMatches K1Artifact.commitCode_0_218 111616 := by
  intro i lo _; have h := i.isLt; omega
private theorem win219 : ParentRangeMatches K1Artifact.commitCode_0_219 112128 := by
  intro i lo _; have h := i.isLt; omega
private theorem win220 : ParentRangeMatches K1Artifact.commitCode_0_220 112640 := by
  intro i lo _; have h := i.isLt; omega
private theorem win221 : ParentRangeMatches K1Artifact.commitCode_0_221 113152 := by
  intro i lo _; have h := i.isLt; omega
private theorem win222 : ParentRangeMatches K1Artifact.commitCode_0_222 113664 := by
  intro i lo _; have h := i.isLt; omega
private theorem win223 : ParentRangeMatches K1Artifact.commitCode_0_223 114176 := by
  intro i lo _; have h := i.isLt; omega
private theorem win224 : ParentRangeMatches K1Artifact.commitCode_0_224 114688 := by
  intro i lo _; have h := i.isLt; omega
private theorem win225 : ParentRangeMatches K1Artifact.commitCode_0_225 115200 := by
  intro i lo _; have h := i.isLt; omega
private theorem win226 : ParentRangeMatches K1Artifact.commitCode_0_226 115712 := by
  intro i lo _; have h := i.isLt; omega
private theorem win227 : ParentRangeMatches K1Artifact.commitCode_0_227 116224 := by
  intro i lo _; have h := i.isLt; omega
private theorem win228 : ParentRangeMatches K1Artifact.commitCode_0_228 116736 := by
  intro i lo _; have h := i.isLt; omega
private theorem win229 : ParentRangeMatches K1Artifact.commitCode_0_229 117248 := by
  intro i lo _; have h := i.isLt; omega
private theorem win230 : ParentRangeMatches K1Artifact.commitCode_0_230 117760 := by
  intro i lo _; have h := i.isLt; omega
private theorem win231 : ParentRangeMatches K1Artifact.commitCode_0_231 118272 := by
  intro i lo _; have h := i.isLt; omega
private theorem win232 : ParentRangeMatches K1Artifact.commitCode_0_232 118784 := by
  intro i lo _; have h := i.isLt; omega
private theorem win233 : ParentRangeMatches K1Artifact.commitCode_0_233 119296 := by
  intro i lo _; have h := i.isLt; omega
private theorem win234 : ParentRangeMatches K1Artifact.commitCode_0_234 119808 := by
  intro i lo _; have h := i.isLt; omega
private theorem win235 : ParentRangeMatches K1Artifact.commitCode_0_235 120320 := by
  intro i lo _; have h := i.isLt; omega
private theorem win236 : ParentRangeMatches K1Artifact.commitCode_0_236 120832 := by
  intro i lo _; have h := i.isLt; omega
private theorem win237 : ParentRangeMatches K1Artifact.commitCode_0_237 121344 := by
  intro i lo _; have h := i.isLt; omega
private theorem win238 : ParentRangeMatches K1Artifact.commitCode_0_238 121856 := by
  intro i lo _; have h := i.isLt; omega
private theorem win239 : ParentRangeMatches K1Artifact.commitCode_0_239 122368 := by
  intro i lo _; have h := i.isLt; omega
private theorem win240 : ParentRangeMatches K1Artifact.commitCode_0_240 122880 := by
  intro i lo _; have h := i.isLt; omega
private theorem win241 : ParentRangeMatches K1Artifact.commitCode_0_241 123392 := by
  intro i lo _; have h := i.isLt; omega
private theorem win242 : ParentRangeMatches K1Artifact.commitCode_0_242 123904 := by
  intro i lo _; have h := i.isLt; omega
private theorem win243 : ParentRangeMatches K1Artifact.commitCode_0_243 124416 := by
  intro i lo _; have h := i.isLt; omega
private theorem win244 : ParentRangeMatches K1Artifact.commitCode_0_244 124928 := by
  intro i lo _; have h := i.isLt; omega
private theorem win245 : ParentRangeMatches K1Artifact.commitCode_0_245 125440 := by
  intro i lo _; have h := i.isLt; omega
private theorem win246 : ParentRangeMatches K1Artifact.commitCode_0_246 125952 := by
  intro i lo _; have h := i.isLt; omega
private theorem win247 : ParentRangeMatches K1Artifact.commitCode_0_247 126464 := by
  intro i lo _; have h := i.isLt; omega
private theorem win248 : ParentRangeMatches K1Artifact.commitCode_0_248 126976 := by
  intro i lo _; have h := i.isLt; omega
private theorem win249 : ParentRangeMatches K1Artifact.commitCode_0_249 127488 := by
  intro i lo _; have h := i.isLt; omega
private theorem win250 : ParentRangeMatches K1Artifact.commitCode_0_250 128000 := by
  intro i lo _; have h := i.isLt; omega
private theorem win251 : ParentRangeMatches K1Artifact.commitCode_0_251 128512 := by
  intro i lo _; have h := i.isLt; omega
private theorem win252 : ParentRangeMatches K1Artifact.commitCode_0_252 129024 := by
  intro i lo _; have h := i.isLt; omega
private theorem win253 : ParentRangeMatches K1Artifact.commitCode_0_253 129536 := by
  intro i lo _; have h := i.isLt; omega
private theorem win254 : ParentRangeMatches K1Artifact.commitCode_0_254 130048 := by
  intro i lo _; have h := i.isLt; omega
private theorem win255 : ParentRangeMatches K1Artifact.commitCode_0_255 130560 := by
  intro i lo _; have h := i.isLt; omega
private theorem win256 : ParentRangeMatches K1Artifact.commitCode_0_256 131072 := by
  intro i lo _; have h := i.isLt; omega
private theorem win257 : ParentRangeMatches K1Artifact.commitCode_0_257 131584 := by
  intro i lo _; have h := i.isLt; omega
private theorem win258 : ParentRangeMatches K1Artifact.commitCode_0_258 132096 := by
  intro i lo _; have h := i.isLt; omega
private theorem win259 : ParentRangeMatches K1Artifact.commitCode_0_259 132608 := by
  intro i lo _; have h := i.isLt; omega
private theorem win260 : ParentRangeMatches K1Artifact.commitCode_0_260 133120 := by
  intro i lo _; have h := i.isLt; omega
private theorem win261 : ParentRangeMatches K1Artifact.commitCode_0_261 133632 := by
  intro i lo _; have h := i.isLt; omega
private theorem win262 : ParentRangeMatches K1Artifact.commitCode_0_262 134144 := by
  intro i lo _; have h := i.isLt; omega
private theorem win263 : ParentRangeMatches K1Artifact.commitCode_0_263 134656 := by
  intro i lo _; have h := i.isLt; omega
private theorem win264 : ParentRangeMatches K1Artifact.commitCode_0_264 135168 := by
  intro i lo _; have h := i.isLt; omega
private theorem win265 : ParentRangeMatches K1Artifact.commitCode_0_265 135680 := by
  intro i lo _; have h := i.isLt; omega
private theorem win266 : ParentRangeMatches K1Artifact.commitCode_0_266 136192 := by
  intro i lo _; have h := i.isLt; omega
private theorem win267 : ParentRangeMatches K1Artifact.commitCode_0_267 136704 := by
  intro i lo _; have h := i.isLt; omega
private theorem win268 : ParentRangeMatches K1Artifact.commitCode_0_268 137216 := by
  intro i lo _; have h := i.isLt; omega
private theorem win269 : ParentRangeMatches K1Artifact.commitCode_0_269 137728 := by
  intro i lo _; have h := i.isLt; omega
private theorem win270 : ParentRangeMatches K1Artifact.commitCode_0_270 138240 := by
  intro i lo _; have h := i.isLt; omega
private theorem win271 : ParentRangeMatches K1Artifact.commitCode_0_271 138752 := by
  intro i lo _; have h := i.isLt; omega
private theorem win272 : ParentRangeMatches K1Artifact.commitCode_0_272 139264 := by
  intro i lo _; have h := i.isLt; omega
private theorem win273 : ParentRangeMatches K1Artifact.commitCode_0_273 139776 := by
  intro i lo _; have h := i.isLt; omega
private theorem win274 : ParentRangeMatches K1Artifact.commitCode_0_274 140288 := by
  intro i lo _; have h := i.isLt; omega
private theorem win275 : ParentRangeMatches K1Artifact.commitCode_0_275 140800 := by
  intro i lo _; have h := i.isLt; omega
private theorem win276 : ParentRangeMatches K1Artifact.commitCode_0_276 141312 := by
  intro i lo _; have h := i.isLt; omega
private theorem win277 : ParentRangeMatches K1Artifact.commitCode_0_277 141824 := by
  intro i lo _; have h := i.isLt; omega
private theorem win278 : ParentRangeMatches K1Artifact.commitCode_0_278 142336 := by
  intro i lo _; have h := i.isLt; omega
private theorem win279 : ParentRangeMatches K1Artifact.commitCode_0_279 142848 := by
  intro i lo _; have h := i.isLt; omega
private theorem win280 : ParentRangeMatches K1Artifact.commitCode_0_280 143360 := by
  intro i lo _; have h := i.isLt; omega
private theorem win281 : ParentRangeMatches K1Artifact.commitCode_0_281 143872 := by
  intro i lo _; have h := i.isLt; omega
private theorem win282 : ParentRangeMatches K1Artifact.commitCode_0_282 144384 := by
  intro i lo _; have h := i.isLt; omega
private theorem win283 : ParentRangeMatches K1Artifact.commitCode_0_283 144896 := by
  intro i lo _; have h := i.isLt; omega
private theorem win284 : ParentRangeMatches K1Artifact.commitCode_0_284 145408 := by
  intro i lo _; have h := i.isLt; omega
private theorem win285 : ParentRangeMatches K1Artifact.commitCode_0_285 145920 := by
  intro i lo _; have h := i.isLt; omega
private theorem win286 : ParentRangeMatches K1Artifact.commitCode_0_286 146432 := by
  intro i lo _; have h := i.isLt; omega
private theorem win287 : ParentRangeMatches K1Artifact.commitCode_0_287 146944 := by
  intro i lo _; have h := i.isLt; omega
private theorem win288 : ParentRangeMatches K1Artifact.commitCode_0_288 147456 := by
  intro i lo _; have h := i.isLt; omega
private theorem win289 : ParentRangeMatches K1Artifact.commitCode_0_289 147968 := by
  intro i lo _; have h := i.isLt; omega
private theorem win290 : ParentRangeMatches K1Artifact.commitCode_0_290 148480 := by
  intro i lo _; have h := i.isLt; omega
private theorem win291 : ParentRangeMatches K1Artifact.commitCode_0_291 148992 := by
  intro i lo _; have h := i.isLt; omega
private theorem win292 : ParentRangeMatches K1Artifact.commitCode_0_292 149504 := by
  intro i lo _; have h := i.isLt; omega
private theorem win293 : ParentRangeMatches K1Artifact.commitCode_0_293 150016 := by
  intro i lo _; have h := i.isLt; omega
private theorem win294 : ParentRangeMatches K1Artifact.commitCode_0_294 150528 := by
  intro i lo _; have h := i.isLt; omega
private theorem win295 : ParentRangeMatches K1Artifact.commitCode_0_295 151040 := by
  intro i lo _; have h := i.isLt; omega
private theorem win296 : ParentRangeMatches K1Artifact.commitCode_0_296 151552 := by
  intro i lo _; have h := i.isLt; omega
private theorem win297 : ParentRangeMatches K1Artifact.commitCode_0_297 152064 := by
  intro i lo _; have h := i.isLt; omega
private theorem win298 : ParentRangeMatches K1Artifact.commitCode_0_298 152576 := by
  intro i lo _; have h := i.isLt; omega
private theorem win299 : ParentRangeMatches K1Artifact.commitCode_0_299 153088 := by
  intro i lo _; have h := i.isLt; omega
private theorem win300 : ParentRangeMatches K1Artifact.commitCode_0_300 153600 := by
  intro i lo _; have h := i.isLt; omega
private theorem win301 : ParentRangeMatches K1Artifact.commitCode_0_301 154112 := by
  intro i lo _; have h := i.isLt; omega
private theorem win302 : ParentRangeMatches K1Artifact.commitCode_0_302 154624 := by
  intro i lo _; have h := i.isLt; omega
private theorem win303 : ParentRangeMatches K1Artifact.commitCode_0_303 155136 := by
  intro i lo _; have h := i.isLt; omega
private theorem win304 : ParentRangeMatches K1Artifact.commitCode_0_304 155648 := by
  intro i lo _; have h := i.isLt; omega
private theorem win305 : ParentRangeMatches K1Artifact.commitCode_0_305 156160 := by
  intro i lo _; have h := i.isLt; omega
private theorem win306 : ParentRangeMatches K1Artifact.commitCode_0_306 156672 := by
  intro i lo _; have h := i.isLt; omega
private theorem win307 : ParentRangeMatches K1Artifact.commitCode_0_307 157184 := by
  intro i lo _; have h := i.isLt; omega
private theorem win308 : ParentRangeMatches K1Artifact.commitCode_0_308 157696 := by
  intro i lo _; have h := i.isLt; omega
private theorem win309 : ParentRangeMatches K1Artifact.commitCode_0_309 158208 := by
  intro i lo _; have h := i.isLt; omega
private theorem win310 : ParentRangeMatches K1Artifact.commitCode_0_310 158720 := by
  intro i lo _; have h := i.isLt; omega
private theorem win311 : ParentRangeMatches K1Artifact.commitCode_0_311 159232 := by
  intro i lo _; have h := i.isLt; omega
private theorem win312 : ParentRangeMatches K1Artifact.commitCode_0_312 159744 := by
  intro i lo _; have h := i.isLt; omega
private theorem win313 : ParentRangeMatches K1Artifact.commitCode_0_313 160256 := by
  intro i lo _; have h := i.isLt; omega
private theorem win314 : ParentRangeMatches K1Artifact.commitCode_0_314 160768 := by
  intro i lo _; have h := i.isLt; omega
private theorem win315 : ParentRangeMatches K1Artifact.commitCode_0_315 161280 := by
  intro i lo _; have h := i.isLt; omega
private theorem win316 : ParentRangeMatches K1Artifact.commitCode_0_316 161792 := by
  intro i lo _; have h := i.isLt; omega
private theorem win317 : ParentRangeMatches K1Artifact.commitCode_0_317 162304 := by
  intro i lo _; have h := i.isLt; omega
private theorem win318 : ParentRangeMatches K1Artifact.commitCode_0_318 162816 := by
  intro i lo _; have h := i.isLt; omega
private theorem win319 : ParentRangeMatches K1Artifact.commitCode_0_319 163328 := by
  intro i lo _; have h := i.isLt; omega
private theorem win320 : ParentRangeMatches K1Artifact.commitCode_0_320 163840 := by
  intro i lo _; have h := i.isLt; omega
private theorem win321 : ParentRangeMatches K1Artifact.commitCode_0_321 164352 := by
  intro i lo _; have h := i.isLt; omega
private theorem win322 : ParentRangeMatches K1Artifact.commitCode_0_322 164864 := by
  intro i lo _; have h := i.isLt; omega
private theorem win323 : ParentRangeMatches K1Artifact.commitCode_0_323 165376 := by
  intro i lo _; have h := i.isLt; omega
private theorem win324 : ParentRangeMatches K1Artifact.commitCode_0_324 165888 := by
  intro i lo _; have h := i.isLt; omega
private theorem win325 : ParentRangeMatches K1Artifact.commitCode_0_325 166400 := by
  intro i lo _; have h := i.isLt; omega
private theorem win326 : ParentRangeMatches K1Artifact.commitCode_0_326 166912 := by
  intro i lo _; have h := i.isLt; omega
private theorem win327 : ParentRangeMatches K1Artifact.commitCode_0_327 167424 := by
  intro i lo _; have h := i.isLt; omega
private theorem win328 : ParentRangeMatches K1Artifact.commitCode_0_328 167936 := by
  intro i lo _; have h := i.isLt; omega
private theorem win329 : ParentRangeMatches K1Artifact.commitCode_0_329 168448 := by
  intro i lo _; have h := i.isLt; omega
private theorem win330 : ParentRangeMatches K1Artifact.commitCode_0_330 168960 := by
  intro i lo _; have h := i.isLt; omega
private theorem win331 : ParentRangeMatches K1Artifact.commitCode_0_331 169472 := by
  intro i lo _; have h := i.isLt; omega
private theorem win332 : ParentRangeMatches K1Artifact.commitCode_0_332 169984 := by
  intro i lo _; have h := i.isLt; omega
private theorem win333 : ParentRangeMatches K1Artifact.commitCode_0_333 170496 := by
  intro i lo _; have h := i.isLt; omega
private theorem win334 : ParentRangeMatches K1Artifact.commitCode_0_334 171008 := by
  intro i lo _; have h := i.isLt; omega
private theorem win335 : ParentRangeMatches K1Artifact.commitCode_0_335 171520 := by
  intro i lo _; have h := i.isLt; omega
private theorem win336 : ParentRangeMatches K1Artifact.commitCode_0_336 172032 := by
  intro i lo _; have h := i.isLt; omega
private theorem win337 : ParentRangeMatches K1Artifact.commitCode_0_337 172544 := by
  intro i lo _; have h := i.isLt; omega
private theorem win338 : ParentRangeMatches K1Artifact.commitCode_0_338 173056 := by
  intro i lo _; have h := i.isLt; omega
private theorem win339 : ParentRangeMatches K1Artifact.commitCode_0_339 173568 := by
  intro i lo _; have h := i.isLt; omega
private theorem win340 : ParentRangeMatches K1Artifact.commitCode_0_340 174080 := by
  intro i lo _; have h := i.isLt; omega
private theorem win341 : ParentRangeMatches K1Artifact.commitCode_0_341 174592 := by
  intro i lo _; have h := i.isLt; omega
private theorem win342 : ParentRangeMatches K1Artifact.commitCode_0_342 175104 := by
  intro i lo _; have h := i.isLt; omega
private theorem win343 : ParentRangeMatches K1Artifact.commitCode_0_343 175616 := by
  intro i lo _; have h := i.isLt; omega
private theorem win344 : ParentRangeMatches K1Artifact.commitCode_0_344 176128 := by
  intro i lo _; have h := i.isLt; omega
private theorem win345 : ParentRangeMatches K1Artifact.commitCode_0_345 176640 := by
  intro i lo _; have h := i.isLt; omega
private theorem win346 : ParentRangeMatches K1Artifact.commitCode_0_346 177152 := by
  intro i lo _; have h := i.isLt; omega
private theorem win347 : ParentRangeMatches K1Artifact.commitCode_0_347 177664 := by
  intro i lo _; have h := i.isLt; omega
private theorem win348 : ParentRangeMatches K1Artifact.commitCode_0_348 178176 := by
  intro i lo _; have h := i.isLt; omega
private theorem win349 : ParentRangeMatches K1Artifact.commitCode_0_349 178688 := by
  intro i lo _; have h := i.isLt; omega
private theorem win350 : ParentRangeMatches K1Artifact.commitCode_0_350 179200 := by
  intro i lo _; have h := i.isLt; omega
private theorem win351 : ParentRangeMatches K1Artifact.commitCode_0_351 179712 := by
  intro i lo _; have h := i.isLt; omega
private theorem win352 : ParentRangeMatches K1Artifact.commitCode_0_352 180224 := by
  intro i lo _; have h := i.isLt; omega
private theorem win353 : ParentRangeMatches K1Artifact.commitCode_0_353 180736 := by
  intro i lo hi; revert i lo hi; decide +kernel
private theorem win354 : ParentRangeMatches K1Artifact.commitCode_0_354 181248 :=
  l21_periodic_window K1Artifact.commitCode_0_354 181248 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win355 : ParentRangeMatches K1Artifact.commitCode_0_355 181760 :=
  l21_periodic_window K1Artifact.commitCode_0_355 181760 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win356 : ParentRangeMatches K1Artifact.commitCode_0_356 182272 :=
  l21_periodic_window K1Artifact.commitCode_0_356 182272 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win357 : ParentRangeMatches K1Artifact.commitCode_0_357 182784 :=
  l21_periodic_window K1Artifact.commitCode_0_357 182784 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win358 : ParentRangeMatches K1Artifact.commitCode_0_358 183296 :=
  l21_periodic_window K1Artifact.commitCode_0_358 183296 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win359 : ParentRangeMatches K1Artifact.commitCode_0_359 183808 :=
  l21_periodic_window K1Artifact.commitCode_0_359 183808 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win360 : ParentRangeMatches K1Artifact.commitCode_0_360 184320 :=
  l21_periodic_window K1Artifact.commitCode_0_360 184320 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win361 : ParentRangeMatches K1Artifact.commitCode_0_361 184832 :=
  l21_periodic_window K1Artifact.commitCode_0_361 184832 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win362 : ParentRangeMatches K1Artifact.commitCode_0_362 185344 :=
  l21_periodic_window K1Artifact.commitCode_0_362 185344 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win363 : ParentRangeMatches K1Artifact.commitCode_0_363 185856 :=
  l21_periodic_window K1Artifact.commitCode_0_363 185856 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win364 : ParentRangeMatches K1Artifact.commitCode_0_364 186368 :=
  l21_periodic_window K1Artifact.commitCode_0_364 186368 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win365 : ParentRangeMatches K1Artifact.commitCode_0_365 186880 :=
  l21_periodic_window K1Artifact.commitCode_0_365 186880 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win366 : ParentRangeMatches K1Artifact.commitCode_0_366 187392 :=
  l21_periodic_window K1Artifact.commitCode_0_366 187392 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win367 : ParentRangeMatches K1Artifact.commitCode_0_367 187904 :=
  l21_periodic_window K1Artifact.commitCode_0_367 187904 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win368 : ParentRangeMatches K1Artifact.commitCode_0_368 188416 :=
  l21_periodic_window K1Artifact.commitCode_0_368 188416 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win369 : ParentRangeMatches K1Artifact.commitCode_0_369 188928 :=
  l21_periodic_window K1Artifact.commitCode_0_369 188928 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win370 : ParentRangeMatches K1Artifact.commitCode_0_370 189440 :=
  l21_periodic_window K1Artifact.commitCode_0_370 189440 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win371 : ParentRangeMatches K1Artifact.commitCode_0_371 189952 :=
  l21_periodic_window K1Artifact.commitCode_0_371 189952 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win372 : ParentRangeMatches K1Artifact.commitCode_0_372 190464 :=
  l21_periodic_window K1Artifact.commitCode_0_372 190464 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win373 : ParentRangeMatches K1Artifact.commitCode_0_373 190976 :=
  l21_periodic_window K1Artifact.commitCode_0_373 190976 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win374 : ParentRangeMatches K1Artifact.commitCode_0_374 191488 :=
  l21_periodic_window K1Artifact.commitCode_0_374 191488 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win375 : ParentRangeMatches K1Artifact.commitCode_0_375 192000 :=
  l21_periodic_window K1Artifact.commitCode_0_375 192000 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win376 : ParentRangeMatches K1Artifact.commitCode_0_376 192512 :=
  l21_periodic_window K1Artifact.commitCode_0_376 192512 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win377 : ParentRangeMatches K1Artifact.commitCode_0_377 193024 :=
  l21_periodic_window K1Artifact.commitCode_0_377 193024 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win378 : ParentRangeMatches K1Artifact.commitCode_0_378 193536 :=
  l21_periodic_window K1Artifact.commitCode_0_378 193536 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win379 : ParentRangeMatches K1Artifact.commitCode_0_379 194048 :=
  l21_periodic_window K1Artifact.commitCode_0_379 194048 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win380 : ParentRangeMatches K1Artifact.commitCode_0_380 194560 :=
  l21_periodic_window K1Artifact.commitCode_0_380 194560 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win381 : ParentRangeMatches K1Artifact.commitCode_0_381 195072 :=
  l21_periodic_window K1Artifact.commitCode_0_381 195072 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win382 : ParentRangeMatches K1Artifact.commitCode_0_382 195584 :=
  l21_periodic_window K1Artifact.commitCode_0_382 195584 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win383 : ParentRangeMatches K1Artifact.commitCode_0_383 196096 :=
  l21_periodic_window K1Artifact.commitCode_0_383 196096 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win384 : ParentRangeMatches K1Artifact.commitCode_0_384 196608 :=
  l21_periodic_window K1Artifact.commitCode_0_384 196608 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win385 : ParentRangeMatches K1Artifact.commitCode_0_385 197120 :=
  l21_periodic_window K1Artifact.commitCode_0_385 197120 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win386 : ParentRangeMatches K1Artifact.commitCode_0_386 197632 :=
  l21_periodic_window K1Artifact.commitCode_0_386 197632 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win387 : ParentRangeMatches K1Artifact.commitCode_0_387 198144 :=
  l21_periodic_window K1Artifact.commitCode_0_387 198144 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win388 : ParentRangeMatches K1Artifact.commitCode_0_388 198656 :=
  l21_periodic_window K1Artifact.commitCode_0_388 198656 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win389 : ParentRangeMatches K1Artifact.commitCode_0_389 199168 :=
  l21_periodic_window K1Artifact.commitCode_0_389 199168 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win390 : ParentRangeMatches K1Artifact.commitCode_0_390 199680 :=
  l21_periodic_window K1Artifact.commitCode_0_390 199680 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win391 : ParentRangeMatches K1Artifact.commitCode_0_391 200192 :=
  l21_periodic_window K1Artifact.commitCode_0_391 200192 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win392 : ParentRangeMatches K1Artifact.commitCode_0_392 200704 :=
  l21_periodic_window K1Artifact.commitCode_0_392 200704 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win393 : ParentRangeMatches K1Artifact.commitCode_0_393 201216 :=
  l21_periodic_window K1Artifact.commitCode_0_393 201216 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win394 : ParentRangeMatches K1Artifact.commitCode_0_394 201728 :=
  l21_periodic_window K1Artifact.commitCode_0_394 201728 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win395 : ParentRangeMatches K1Artifact.commitCode_0_395 202240 :=
  l21_periodic_window K1Artifact.commitCode_0_395 202240 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win396 : ParentRangeMatches K1Artifact.commitCode_0_396 202752 :=
  l21_periodic_window K1Artifact.commitCode_0_396 202752 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win397 : ParentRangeMatches K1Artifact.commitCode_0_397 203264 :=
  l21_periodic_window K1Artifact.commitCode_0_397 203264 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win398 : ParentRangeMatches K1Artifact.commitCode_0_398 203776 :=
  l21_periodic_window K1Artifact.commitCode_0_398 203776 0 (by decide) (by decide) (by decide) l21_periodic_0
private theorem win399 : ParentRangeMatches K1Artifact.commitCode_0_399 204288 :=
  l21_periodic_window K1Artifact.commitCode_0_399 204288 2 (by decide) (by decide) (by decide) l21_periodic_2
private theorem win400 : ParentRangeMatches K1Artifact.commitCode_0_400 204800 :=
  l21_periodic_window K1Artifact.commitCode_0_400 204800 1 (by decide) (by decide) (by decide) l21_periodic_1
private theorem win401 : ParentRangeMatches K1Artifact.commitCode_0_401 205312 := by
  intro i lo hi; revert i lo hi; decide +kernel
private theorem win402 : ParentRangeMatches K1Artifact.commitCode_0_402 205824 :=
  bandA_periodic_window K1Artifact.commitCode_0_402 205824 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win403 : ParentRangeMatches K1Artifact.commitCode_0_403 206336 :=
  bandA_periodic_window K1Artifact.commitCode_0_403 206336 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win404 : ParentRangeMatches K1Artifact.commitCode_0_404 206848 :=
  bandA_periodic_window K1Artifact.commitCode_0_404 206848 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win405 : ParentRangeMatches K1Artifact.commitCode_0_405 207360 :=
  bandA_periodic_window K1Artifact.commitCode_0_405 207360 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win406 : ParentRangeMatches K1Artifact.commitCode_0_406 207872 :=
  bandA_periodic_window K1Artifact.commitCode_0_406 207872 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win407 : ParentRangeMatches K1Artifact.commitCode_0_407 208384 :=
  bandA_periodic_window K1Artifact.commitCode_0_407 208384 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win408 : ParentRangeMatches K1Artifact.commitCode_0_408 208896 :=
  bandA_periodic_window K1Artifact.commitCode_0_408 208896 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win409 : ParentRangeMatches K1Artifact.commitCode_0_409 209408 :=
  bandA_periodic_window K1Artifact.commitCode_0_409 209408 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win410 : ParentRangeMatches K1Artifact.commitCode_0_410 209920 :=
  bandA_periodic_window K1Artifact.commitCode_0_410 209920 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win411 : ParentRangeMatches K1Artifact.commitCode_0_411 210432 :=
  bandA_periodic_window K1Artifact.commitCode_0_411 210432 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win412 : ParentRangeMatches K1Artifact.commitCode_0_412 210944 :=
  bandA_periodic_window K1Artifact.commitCode_0_412 210944 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win413 : ParentRangeMatches K1Artifact.commitCode_0_413 211456 :=
  bandA_periodic_window K1Artifact.commitCode_0_413 211456 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win414 : ParentRangeMatches K1Artifact.commitCode_0_414 211968 :=
  bandA_periodic_window K1Artifact.commitCode_0_414 211968 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win415 : ParentRangeMatches K1Artifact.commitCode_0_415 212480 :=
  bandA_periodic_window K1Artifact.commitCode_0_415 212480 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win416 : ParentRangeMatches K1Artifact.commitCode_0_416 212992 :=
  bandA_periodic_window K1Artifact.commitCode_0_416 212992 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win417 : ParentRangeMatches K1Artifact.commitCode_0_417 213504 :=
  bandA_periodic_window K1Artifact.commitCode_0_417 213504 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win418 : ParentRangeMatches K1Artifact.commitCode_0_418 214016 :=
  bandA_periodic_window K1Artifact.commitCode_0_418 214016 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win419 : ParentRangeMatches K1Artifact.commitCode_0_419 214528 :=
  bandA_periodic_window K1Artifact.commitCode_0_419 214528 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win420 : ParentRangeMatches K1Artifact.commitCode_0_420 215040 :=
  bandA_periodic_window K1Artifact.commitCode_0_420 215040 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win421 : ParentRangeMatches K1Artifact.commitCode_0_421 215552 :=
  bandA_periodic_window K1Artifact.commitCode_0_421 215552 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win422 : ParentRangeMatches K1Artifact.commitCode_0_422 216064 :=
  bandA_periodic_window K1Artifact.commitCode_0_422 216064 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win423 : ParentRangeMatches K1Artifact.commitCode_0_423 216576 :=
  bandA_periodic_window K1Artifact.commitCode_0_423 216576 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win424 : ParentRangeMatches K1Artifact.commitCode_0_424 217088 :=
  bandA_periodic_window K1Artifact.commitCode_0_424 217088 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win425 : ParentRangeMatches K1Artifact.commitCode_0_425 217600 :=
  bandA_periodic_window K1Artifact.commitCode_0_425 217600 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win426 : ParentRangeMatches K1Artifact.commitCode_0_426 218112 :=
  bandA_periodic_window K1Artifact.commitCode_0_426 218112 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win427 : ParentRangeMatches K1Artifact.commitCode_0_427 218624 :=
  bandA_periodic_window K1Artifact.commitCode_0_427 218624 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win428 : ParentRangeMatches K1Artifact.commitCode_0_428 219136 :=
  bandA_periodic_window K1Artifact.commitCode_0_428 219136 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win429 : ParentRangeMatches K1Artifact.commitCode_0_429 219648 :=
  bandA_periodic_window K1Artifact.commitCode_0_429 219648 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win430 : ParentRangeMatches K1Artifact.commitCode_0_430 220160 :=
  bandA_periodic_window K1Artifact.commitCode_0_430 220160 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win431 : ParentRangeMatches K1Artifact.commitCode_0_431 220672 :=
  bandA_periodic_window K1Artifact.commitCode_0_431 220672 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win432 : ParentRangeMatches K1Artifact.commitCode_0_432 221184 :=
  bandA_periodic_window K1Artifact.commitCode_0_432 221184 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win433 : ParentRangeMatches K1Artifact.commitCode_0_433 221696 :=
  bandA_periodic_window K1Artifact.commitCode_0_433 221696 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win434 : ParentRangeMatches K1Artifact.commitCode_0_434 222208 :=
  bandA_periodic_window K1Artifact.commitCode_0_434 222208 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win435 : ParentRangeMatches K1Artifact.commitCode_0_435 222720 :=
  bandA_periodic_window K1Artifact.commitCode_0_435 222720 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win436 : ParentRangeMatches K1Artifact.commitCode_0_436 223232 :=
  bandA_periodic_window K1Artifact.commitCode_0_436 223232 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win437 : ParentRangeMatches K1Artifact.commitCode_0_437 223744 :=
  bandA_periodic_window K1Artifact.commitCode_0_437 223744 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win438 : ParentRangeMatches K1Artifact.commitCode_0_438 224256 :=
  bandA_periodic_window K1Artifact.commitCode_0_438 224256 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win439 : ParentRangeMatches K1Artifact.commitCode_0_439 224768 :=
  bandA_periodic_window K1Artifact.commitCode_0_439 224768 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win440 : ParentRangeMatches K1Artifact.commitCode_0_440 225280 :=
  bandA_periodic_window K1Artifact.commitCode_0_440 225280 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win441 : ParentRangeMatches K1Artifact.commitCode_0_441 225792 :=
  bandA_periodic_window K1Artifact.commitCode_0_441 225792 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win442 : ParentRangeMatches K1Artifact.commitCode_0_442 226304 :=
  bandA_periodic_window K1Artifact.commitCode_0_442 226304 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win443 : ParentRangeMatches K1Artifact.commitCode_0_443 226816 :=
  bandA_periodic_window K1Artifact.commitCode_0_443 226816 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win444 : ParentRangeMatches K1Artifact.commitCode_0_444 227328 :=
  bandA_periodic_window K1Artifact.commitCode_0_444 227328 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win445 : ParentRangeMatches K1Artifact.commitCode_0_445 227840 :=
  bandA_periodic_window K1Artifact.commitCode_0_445 227840 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win446 : ParentRangeMatches K1Artifact.commitCode_0_446 228352 :=
  bandA_periodic_window K1Artifact.commitCode_0_446 228352 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win447 : ParentRangeMatches K1Artifact.commitCode_0_447 228864 :=
  bandA_periodic_window K1Artifact.commitCode_0_447 228864 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win448 : ParentRangeMatches K1Artifact.commitCode_0_448 229376 :=
  bandA_periodic_window K1Artifact.commitCode_0_448 229376 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win449 : ParentRangeMatches K1Artifact.commitCode_0_449 229888 :=
  bandA_periodic_window K1Artifact.commitCode_0_449 229888 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win450 : ParentRangeMatches K1Artifact.commitCode_0_450 230400 :=
  bandA_periodic_window K1Artifact.commitCode_0_450 230400 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win451 : ParentRangeMatches K1Artifact.commitCode_0_451 230912 :=
  bandA_periodic_window K1Artifact.commitCode_0_451 230912 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win452 : ParentRangeMatches K1Artifact.commitCode_0_452 231424 :=
  bandA_periodic_window K1Artifact.commitCode_0_452 231424 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win453 : ParentRangeMatches K1Artifact.commitCode_0_453 231936 :=
  bandA_periodic_window K1Artifact.commitCode_0_453 231936 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win454 : ParentRangeMatches K1Artifact.commitCode_0_454 232448 :=
  bandA_periodic_window K1Artifact.commitCode_0_454 232448 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win455 : ParentRangeMatches K1Artifact.commitCode_0_455 232960 :=
  bandA_periodic_window K1Artifact.commitCode_0_455 232960 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win456 : ParentRangeMatches K1Artifact.commitCode_0_456 233472 :=
  bandA_periodic_window K1Artifact.commitCode_0_456 233472 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win457 : ParentRangeMatches K1Artifact.commitCode_0_457 233984 :=
  bandA_periodic_window K1Artifact.commitCode_0_457 233984 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win458 : ParentRangeMatches K1Artifact.commitCode_0_458 234496 :=
  bandA_periodic_window K1Artifact.commitCode_0_458 234496 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win459 : ParentRangeMatches K1Artifact.commitCode_0_459 235008 :=
  bandA_periodic_window K1Artifact.commitCode_0_459 235008 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win460 : ParentRangeMatches K1Artifact.commitCode_0_460 235520 :=
  bandA_periodic_window K1Artifact.commitCode_0_460 235520 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win461 : ParentRangeMatches K1Artifact.commitCode_0_461 236032 :=
  bandA_periodic_window K1Artifact.commitCode_0_461 236032 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win462 : ParentRangeMatches K1Artifact.commitCode_0_462 236544 :=
  bandA_periodic_window K1Artifact.commitCode_0_462 236544 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win463 : ParentRangeMatches K1Artifact.commitCode_0_463 237056 :=
  bandA_periodic_window K1Artifact.commitCode_0_463 237056 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win464 : ParentRangeMatches K1Artifact.commitCode_0_464 237568 :=
  bandA_periodic_window K1Artifact.commitCode_0_464 237568 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win465 : ParentRangeMatches K1Artifact.commitCode_0_465 238080 :=
  bandA_periodic_window K1Artifact.commitCode_0_465 238080 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win466 : ParentRangeMatches K1Artifact.commitCode_0_466 238592 :=
  bandA_periodic_window K1Artifact.commitCode_0_466 238592 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win467 : ParentRangeMatches K1Artifact.commitCode_0_467 239104 :=
  bandA_periodic_window K1Artifact.commitCode_0_467 239104 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win468 : ParentRangeMatches K1Artifact.commitCode_0_468 239616 :=
  bandA_periodic_window K1Artifact.commitCode_0_468 239616 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win469 : ParentRangeMatches K1Artifact.commitCode_0_469 240128 :=
  bandA_periodic_window K1Artifact.commitCode_0_469 240128 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win470 : ParentRangeMatches K1Artifact.commitCode_0_470 240640 :=
  bandA_periodic_window K1Artifact.commitCode_0_470 240640 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win471 : ParentRangeMatches K1Artifact.commitCode_0_471 241152 :=
  bandA_periodic_window K1Artifact.commitCode_0_471 241152 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win472 : ParentRangeMatches K1Artifact.commitCode_0_472 241664 :=
  bandA_periodic_window K1Artifact.commitCode_0_472 241664 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win473 : ParentRangeMatches K1Artifact.commitCode_0_473 242176 :=
  bandA_periodic_window K1Artifact.commitCode_0_473 242176 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win474 : ParentRangeMatches K1Artifact.commitCode_0_474 242688 :=
  bandA_periodic_window K1Artifact.commitCode_0_474 242688 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win475 : ParentRangeMatches K1Artifact.commitCode_0_475 243200 :=
  bandA_periodic_window K1Artifact.commitCode_0_475 243200 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win476 : ParentRangeMatches K1Artifact.commitCode_0_476 243712 :=
  bandA_periodic_window K1Artifact.commitCode_0_476 243712 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win477 : ParentRangeMatches K1Artifact.commitCode_0_477 244224 :=
  bandA_periodic_window K1Artifact.commitCode_0_477 244224 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win478 : ParentRangeMatches K1Artifact.commitCode_0_478 244736 :=
  bandA_periodic_window K1Artifact.commitCode_0_478 244736 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win479 : ParentRangeMatches K1Artifact.commitCode_0_479 245248 :=
  bandA_periodic_window K1Artifact.commitCode_0_479 245248 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win480 : ParentRangeMatches K1Artifact.commitCode_0_480 245760 :=
  bandA_periodic_window K1Artifact.commitCode_0_480 245760 1 (by decide) (by decide) (by decide) bandA_periodic_1
private theorem win481 : ParentRangeMatches K1Artifact.commitCode_0_481 246272 := by
  intro i lo hi; revert i lo hi; decide +kernel
private theorem win482 : ParentRangeMatches K1Artifact.commitCode_0_482 246784 :=
  bandB_periodic_window K1Artifact.commitCode_0_482 246784 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win483 : ParentRangeMatches K1Artifact.commitCode_0_483 247296 :=
  bandB_periodic_window K1Artifact.commitCode_0_483 247296 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win484 : ParentRangeMatches K1Artifact.commitCode_0_484 247808 :=
  bandB_periodic_window K1Artifact.commitCode_0_484 247808 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win485 : ParentRangeMatches K1Artifact.commitCode_0_485 248320 :=
  bandB_periodic_window K1Artifact.commitCode_0_485 248320 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win486 : ParentRangeMatches K1Artifact.commitCode_0_486 248832 :=
  bandB_periodic_window K1Artifact.commitCode_0_486 248832 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win487 : ParentRangeMatches K1Artifact.commitCode_0_487 249344 :=
  bandB_periodic_window K1Artifact.commitCode_0_487 249344 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win488 : ParentRangeMatches K1Artifact.commitCode_0_488 249856 :=
  bandB_periodic_window K1Artifact.commitCode_0_488 249856 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win489 : ParentRangeMatches K1Artifact.commitCode_0_489 250368 :=
  bandB_periodic_window K1Artifact.commitCode_0_489 250368 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win490 : ParentRangeMatches K1Artifact.commitCode_0_490 250880 :=
  bandB_periodic_window K1Artifact.commitCode_0_490 250880 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win491 : ParentRangeMatches K1Artifact.commitCode_0_491 251392 :=
  bandB_periodic_window K1Artifact.commitCode_0_491 251392 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win492 : ParentRangeMatches K1Artifact.commitCode_0_492 251904 :=
  bandB_periodic_window K1Artifact.commitCode_0_492 251904 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win493 : ParentRangeMatches K1Artifact.commitCode_0_493 252416 :=
  bandB_periodic_window K1Artifact.commitCode_0_493 252416 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win494 : ParentRangeMatches K1Artifact.commitCode_0_494 252928 :=
  bandB_periodic_window K1Artifact.commitCode_0_494 252928 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win495 : ParentRangeMatches K1Artifact.commitCode_0_495 253440 :=
  bandB_periodic_window K1Artifact.commitCode_0_495 253440 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win496 : ParentRangeMatches K1Artifact.commitCode_0_496 253952 :=
  bandB_periodic_window K1Artifact.commitCode_0_496 253952 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win497 : ParentRangeMatches K1Artifact.commitCode_0_497 254464 :=
  bandB_periodic_window K1Artifact.commitCode_0_497 254464 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win498 : ParentRangeMatches K1Artifact.commitCode_0_498 254976 :=
  bandB_periodic_window K1Artifact.commitCode_0_498 254976 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win499 : ParentRangeMatches K1Artifact.commitCode_0_499 255488 :=
  bandB_periodic_window K1Artifact.commitCode_0_499 255488 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win500 : ParentRangeMatches K1Artifact.commitCode_0_500 256000 :=
  bandB_periodic_window K1Artifact.commitCode_0_500 256000 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win501 : ParentRangeMatches K1Artifact.commitCode_0_501 256512 :=
  bandB_periodic_window K1Artifact.commitCode_0_501 256512 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win502 : ParentRangeMatches K1Artifact.commitCode_0_502 257024 :=
  bandB_periodic_window K1Artifact.commitCode_0_502 257024 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win503 : ParentRangeMatches K1Artifact.commitCode_0_503 257536 :=
  bandB_periodic_window K1Artifact.commitCode_0_503 257536 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win504 : ParentRangeMatches K1Artifact.commitCode_0_504 258048 :=
  bandB_periodic_window K1Artifact.commitCode_0_504 258048 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win505 : ParentRangeMatches K1Artifact.commitCode_0_505 258560 :=
  bandB_periodic_window K1Artifact.commitCode_0_505 258560 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win506 : ParentRangeMatches K1Artifact.commitCode_0_506 259072 :=
  bandB_periodic_window K1Artifact.commitCode_0_506 259072 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win507 : ParentRangeMatches K1Artifact.commitCode_0_507 259584 :=
  bandB_periodic_window K1Artifact.commitCode_0_507 259584 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win508 : ParentRangeMatches K1Artifact.commitCode_0_508 260096 :=
  bandB_periodic_window K1Artifact.commitCode_0_508 260096 0 (by decide) (by decide) (by decide) bandB_periodic_0
private theorem win509 : ParentRangeMatches K1Artifact.commitCode_0_509 260608 :=
  bandB_periodic_window K1Artifact.commitCode_0_509 260608 2 (by decide) (by decide) (by decide) bandB_periodic_2
private theorem win510 : ParentRangeMatches K1Artifact.commitCode_0_510 261120 :=
  bandB_periodic_window K1Artifact.commitCode_0_510 261120 4 (by decide) (by decide) (by decide) bandB_periodic_4
private theorem win511 : ParentRangeMatches K1Artifact.commitCode_0_511 261632 := by
  intro i lo hi; revert i lo hi; decide +kernel

private theorem blk1_0 : ParentRangeMatches K1Artifact.commitCode_1_0 0 :=
  (parent_range_join _ _ 0 (parent_range_join _ _ 0 (parent_range_join _ _ 0 win0 win1) (parent_range_join _ _ 1024 win2 win3)) (parent_range_join _ _ 2048 (parent_range_join _ _ 2048 win4 win5) (parent_range_join _ _ 3072 win6 win7)))
private theorem blk1_1 : ParentRangeMatches K1Artifact.commitCode_1_1 4096 :=
  (parent_range_join _ _ 4096 (parent_range_join _ _ 4096 (parent_range_join _ _ 4096 win8 win9) (parent_range_join _ _ 5120 win10 win11)) (parent_range_join _ _ 6144 (parent_range_join _ _ 6144 win12 win13) (parent_range_join _ _ 7168 win14 win15)))
private theorem blk1_2 : ParentRangeMatches K1Artifact.commitCode_1_2 8192 :=
  (parent_range_join _ _ 8192 (parent_range_join _ _ 8192 (parent_range_join _ _ 8192 win16 win17) (parent_range_join _ _ 9216 win18 win19)) (parent_range_join _ _ 10240 (parent_range_join _ _ 10240 win20 win21) (parent_range_join _ _ 11264 win22 win23)))
private theorem blk1_3 : ParentRangeMatches K1Artifact.commitCode_1_3 12288 :=
  (parent_range_join _ _ 12288 (parent_range_join _ _ 12288 (parent_range_join _ _ 12288 win24 win25) (parent_range_join _ _ 13312 win26 win27)) (parent_range_join _ _ 14336 (parent_range_join _ _ 14336 win28 win29) (parent_range_join _ _ 15360 win30 win31)))
private theorem blk1_4 : ParentRangeMatches K1Artifact.commitCode_1_4 16384 :=
  (parent_range_join _ _ 16384 (parent_range_join _ _ 16384 (parent_range_join _ _ 16384 win32 win33) (parent_range_join _ _ 17408 win34 win35)) (parent_range_join _ _ 18432 (parent_range_join _ _ 18432 win36 win37) (parent_range_join _ _ 19456 win38 win39)))
private theorem blk1_5 : ParentRangeMatches K1Artifact.commitCode_1_5 20480 :=
  (parent_range_join _ _ 20480 (parent_range_join _ _ 20480 (parent_range_join _ _ 20480 win40 win41) (parent_range_join _ _ 21504 win42 win43)) (parent_range_join _ _ 22528 (parent_range_join _ _ 22528 win44 win45) (parent_range_join _ _ 23552 win46 win47)))
private theorem blk1_6 : ParentRangeMatches K1Artifact.commitCode_1_6 24576 :=
  (parent_range_join _ _ 24576 (parent_range_join _ _ 24576 (parent_range_join _ _ 24576 win48 win49) (parent_range_join _ _ 25600 win50 win51)) (parent_range_join _ _ 26624 (parent_range_join _ _ 26624 win52 win53) (parent_range_join _ _ 27648 win54 win55)))
private theorem blk1_7 : ParentRangeMatches K1Artifact.commitCode_1_7 28672 :=
  (parent_range_join _ _ 28672 (parent_range_join _ _ 28672 (parent_range_join _ _ 28672 win56 win57) (parent_range_join _ _ 29696 win58 win59)) (parent_range_join _ _ 30720 (parent_range_join _ _ 30720 win60 win61) (parent_range_join _ _ 31744 win62 win63)))
private theorem blk1_8 : ParentRangeMatches K1Artifact.commitCode_1_8 32768 :=
  (parent_range_join _ _ 32768 (parent_range_join _ _ 32768 (parent_range_join _ _ 32768 win64 win65) (parent_range_join _ _ 33792 win66 win67)) (parent_range_join _ _ 34816 (parent_range_join _ _ 34816 win68 win69) (parent_range_join _ _ 35840 win70 win71)))
private theorem blk1_9 : ParentRangeMatches K1Artifact.commitCode_1_9 36864 :=
  (parent_range_join _ _ 36864 (parent_range_join _ _ 36864 (parent_range_join _ _ 36864 win72 win73) (parent_range_join _ _ 37888 win74 win75)) (parent_range_join _ _ 38912 (parent_range_join _ _ 38912 win76 win77) (parent_range_join _ _ 39936 win78 win79)))
private theorem blk1_10 : ParentRangeMatches K1Artifact.commitCode_1_10 40960 :=
  (parent_range_join _ _ 40960 (parent_range_join _ _ 40960 (parent_range_join _ _ 40960 win80 win81) (parent_range_join _ _ 41984 win82 win83)) (parent_range_join _ _ 43008 (parent_range_join _ _ 43008 win84 win85) (parent_range_join _ _ 44032 win86 win87)))
private theorem blk1_11 : ParentRangeMatches K1Artifact.commitCode_1_11 45056 :=
  (parent_range_join _ _ 45056 (parent_range_join _ _ 45056 (parent_range_join _ _ 45056 win88 win89) (parent_range_join _ _ 46080 win90 win91)) (parent_range_join _ _ 47104 (parent_range_join _ _ 47104 win92 win93) (parent_range_join _ _ 48128 win94 win95)))
private theorem blk1_12 : ParentRangeMatches K1Artifact.commitCode_1_12 49152 :=
  (parent_range_join _ _ 49152 (parent_range_join _ _ 49152 (parent_range_join _ _ 49152 win96 win97) (parent_range_join _ _ 50176 win98 win99)) (parent_range_join _ _ 51200 (parent_range_join _ _ 51200 win100 win101) (parent_range_join _ _ 52224 win102 win103)))
private theorem blk1_13 : ParentRangeMatches K1Artifact.commitCode_1_13 53248 :=
  (parent_range_join _ _ 53248 (parent_range_join _ _ 53248 (parent_range_join _ _ 53248 win104 win105) (parent_range_join _ _ 54272 win106 win107)) (parent_range_join _ _ 55296 (parent_range_join _ _ 55296 win108 win109) (parent_range_join _ _ 56320 win110 win111)))
private theorem blk1_14 : ParentRangeMatches K1Artifact.commitCode_1_14 57344 :=
  (parent_range_join _ _ 57344 (parent_range_join _ _ 57344 (parent_range_join _ _ 57344 win112 win113) (parent_range_join _ _ 58368 win114 win115)) (parent_range_join _ _ 59392 (parent_range_join _ _ 59392 win116 win117) (parent_range_join _ _ 60416 win118 win119)))
private theorem blk1_15 : ParentRangeMatches K1Artifact.commitCode_1_15 61440 :=
  (parent_range_join _ _ 61440 (parent_range_join _ _ 61440 (parent_range_join _ _ 61440 win120 win121) (parent_range_join _ _ 62464 win122 win123)) (parent_range_join _ _ 63488 (parent_range_join _ _ 63488 win124 win125) (parent_range_join _ _ 64512 win126 win127)))
private theorem blk1_16 : ParentRangeMatches K1Artifact.commitCode_1_16 65536 :=
  (parent_range_join _ _ 65536 (parent_range_join _ _ 65536 (parent_range_join _ _ 65536 win128 win129) (parent_range_join _ _ 66560 win130 win131)) (parent_range_join _ _ 67584 (parent_range_join _ _ 67584 win132 win133) (parent_range_join _ _ 68608 win134 win135)))
private theorem blk1_17 : ParentRangeMatches K1Artifact.commitCode_1_17 69632 :=
  (parent_range_join _ _ 69632 (parent_range_join _ _ 69632 (parent_range_join _ _ 69632 win136 win137) (parent_range_join _ _ 70656 win138 win139)) (parent_range_join _ _ 71680 (parent_range_join _ _ 71680 win140 win141) (parent_range_join _ _ 72704 win142 win143)))
private theorem blk1_18 : ParentRangeMatches K1Artifact.commitCode_1_18 73728 :=
  (parent_range_join _ _ 73728 (parent_range_join _ _ 73728 (parent_range_join _ _ 73728 win144 win145) (parent_range_join _ _ 74752 win146 win147)) (parent_range_join _ _ 75776 (parent_range_join _ _ 75776 win148 win149) (parent_range_join _ _ 76800 win150 win151)))
private theorem blk1_19 : ParentRangeMatches K1Artifact.commitCode_1_19 77824 :=
  (parent_range_join _ _ 77824 (parent_range_join _ _ 77824 (parent_range_join _ _ 77824 win152 win153) (parent_range_join _ _ 78848 win154 win155)) (parent_range_join _ _ 79872 (parent_range_join _ _ 79872 win156 win157) (parent_range_join _ _ 80896 win158 win159)))
private theorem blk1_20 : ParentRangeMatches K1Artifact.commitCode_1_20 81920 :=
  (parent_range_join _ _ 81920 (parent_range_join _ _ 81920 (parent_range_join _ _ 81920 win160 win161) (parent_range_join _ _ 82944 win162 win163)) (parent_range_join _ _ 83968 (parent_range_join _ _ 83968 win164 win165) (parent_range_join _ _ 84992 win166 win167)))
private theorem blk1_21 : ParentRangeMatches K1Artifact.commitCode_1_21 86016 :=
  (parent_range_join _ _ 86016 (parent_range_join _ _ 86016 (parent_range_join _ _ 86016 win168 win169) (parent_range_join _ _ 87040 win170 win171)) (parent_range_join _ _ 88064 (parent_range_join _ _ 88064 win172 win173) (parent_range_join _ _ 89088 win174 win175)))
private theorem blk1_22 : ParentRangeMatches K1Artifact.commitCode_1_22 90112 :=
  (parent_range_join _ _ 90112 (parent_range_join _ _ 90112 (parent_range_join _ _ 90112 win176 win177) (parent_range_join _ _ 91136 win178 win179)) (parent_range_join _ _ 92160 (parent_range_join _ _ 92160 win180 win181) (parent_range_join _ _ 93184 win182 win183)))
private theorem blk1_23 : ParentRangeMatches K1Artifact.commitCode_1_23 94208 :=
  (parent_range_join _ _ 94208 (parent_range_join _ _ 94208 (parent_range_join _ _ 94208 win184 win185) (parent_range_join _ _ 95232 win186 win187)) (parent_range_join _ _ 96256 (parent_range_join _ _ 96256 win188 win189) (parent_range_join _ _ 97280 win190 win191)))
private theorem blk1_24 : ParentRangeMatches K1Artifact.commitCode_1_24 98304 :=
  (parent_range_join _ _ 98304 (parent_range_join _ _ 98304 (parent_range_join _ _ 98304 win192 win193) (parent_range_join _ _ 99328 win194 win195)) (parent_range_join _ _ 100352 (parent_range_join _ _ 100352 win196 win197) (parent_range_join _ _ 101376 win198 win199)))
private theorem blk1_25 : ParentRangeMatches K1Artifact.commitCode_1_25 102400 :=
  (parent_range_join _ _ 102400 (parent_range_join _ _ 102400 (parent_range_join _ _ 102400 win200 win201) (parent_range_join _ _ 103424 win202 win203)) (parent_range_join _ _ 104448 (parent_range_join _ _ 104448 win204 win205) (parent_range_join _ _ 105472 win206 win207)))
private theorem blk1_26 : ParentRangeMatches K1Artifact.commitCode_1_26 106496 :=
  (parent_range_join _ _ 106496 (parent_range_join _ _ 106496 (parent_range_join _ _ 106496 win208 win209) (parent_range_join _ _ 107520 win210 win211)) (parent_range_join _ _ 108544 (parent_range_join _ _ 108544 win212 win213) (parent_range_join _ _ 109568 win214 win215)))
private theorem blk1_27 : ParentRangeMatches K1Artifact.commitCode_1_27 110592 :=
  (parent_range_join _ _ 110592 (parent_range_join _ _ 110592 (parent_range_join _ _ 110592 win216 win217) (parent_range_join _ _ 111616 win218 win219)) (parent_range_join _ _ 112640 (parent_range_join _ _ 112640 win220 win221) (parent_range_join _ _ 113664 win222 win223)))
private theorem blk1_28 : ParentRangeMatches K1Artifact.commitCode_1_28 114688 :=
  (parent_range_join _ _ 114688 (parent_range_join _ _ 114688 (parent_range_join _ _ 114688 win224 win225) (parent_range_join _ _ 115712 win226 win227)) (parent_range_join _ _ 116736 (parent_range_join _ _ 116736 win228 win229) (parent_range_join _ _ 117760 win230 win231)))
private theorem blk1_29 : ParentRangeMatches K1Artifact.commitCode_1_29 118784 :=
  (parent_range_join _ _ 118784 (parent_range_join _ _ 118784 (parent_range_join _ _ 118784 win232 win233) (parent_range_join _ _ 119808 win234 win235)) (parent_range_join _ _ 120832 (parent_range_join _ _ 120832 win236 win237) (parent_range_join _ _ 121856 win238 win239)))
private theorem blk1_30 : ParentRangeMatches K1Artifact.commitCode_1_30 122880 :=
  (parent_range_join _ _ 122880 (parent_range_join _ _ 122880 (parent_range_join _ _ 122880 win240 win241) (parent_range_join _ _ 123904 win242 win243)) (parent_range_join _ _ 124928 (parent_range_join _ _ 124928 win244 win245) (parent_range_join _ _ 125952 win246 win247)))
private theorem blk1_31 : ParentRangeMatches K1Artifact.commitCode_1_31 126976 :=
  (parent_range_join _ _ 126976 (parent_range_join _ _ 126976 (parent_range_join _ _ 126976 win248 win249) (parent_range_join _ _ 128000 win250 win251)) (parent_range_join _ _ 129024 (parent_range_join _ _ 129024 win252 win253) (parent_range_join _ _ 130048 win254 win255)))
private theorem blk1_32 : ParentRangeMatches K1Artifact.commitCode_1_32 131072 :=
  (parent_range_join _ _ 131072 (parent_range_join _ _ 131072 (parent_range_join _ _ 131072 win256 win257) (parent_range_join _ _ 132096 win258 win259)) (parent_range_join _ _ 133120 (parent_range_join _ _ 133120 win260 win261) (parent_range_join _ _ 134144 win262 win263)))
private theorem blk1_33 : ParentRangeMatches K1Artifact.commitCode_1_33 135168 :=
  (parent_range_join _ _ 135168 (parent_range_join _ _ 135168 (parent_range_join _ _ 135168 win264 win265) (parent_range_join _ _ 136192 win266 win267)) (parent_range_join _ _ 137216 (parent_range_join _ _ 137216 win268 win269) (parent_range_join _ _ 138240 win270 win271)))
private theorem blk1_34 : ParentRangeMatches K1Artifact.commitCode_1_34 139264 :=
  (parent_range_join _ _ 139264 (parent_range_join _ _ 139264 (parent_range_join _ _ 139264 win272 win273) (parent_range_join _ _ 140288 win274 win275)) (parent_range_join _ _ 141312 (parent_range_join _ _ 141312 win276 win277) (parent_range_join _ _ 142336 win278 win279)))
private theorem blk1_35 : ParentRangeMatches K1Artifact.commitCode_1_35 143360 :=
  (parent_range_join _ _ 143360 (parent_range_join _ _ 143360 (parent_range_join _ _ 143360 win280 win281) (parent_range_join _ _ 144384 win282 win283)) (parent_range_join _ _ 145408 (parent_range_join _ _ 145408 win284 win285) (parent_range_join _ _ 146432 win286 win287)))
private theorem blk1_36 : ParentRangeMatches K1Artifact.commitCode_1_36 147456 :=
  (parent_range_join _ _ 147456 (parent_range_join _ _ 147456 (parent_range_join _ _ 147456 win288 win289) (parent_range_join _ _ 148480 win290 win291)) (parent_range_join _ _ 149504 (parent_range_join _ _ 149504 win292 win293) (parent_range_join _ _ 150528 win294 win295)))
private theorem blk1_37 : ParentRangeMatches K1Artifact.commitCode_1_37 151552 :=
  (parent_range_join _ _ 151552 (parent_range_join _ _ 151552 (parent_range_join _ _ 151552 win296 win297) (parent_range_join _ _ 152576 win298 win299)) (parent_range_join _ _ 153600 (parent_range_join _ _ 153600 win300 win301) (parent_range_join _ _ 154624 win302 win303)))
private theorem blk1_38 : ParentRangeMatches K1Artifact.commitCode_1_38 155648 :=
  (parent_range_join _ _ 155648 (parent_range_join _ _ 155648 (parent_range_join _ _ 155648 win304 win305) (parent_range_join _ _ 156672 win306 win307)) (parent_range_join _ _ 157696 (parent_range_join _ _ 157696 win308 win309) (parent_range_join _ _ 158720 win310 win311)))
private theorem blk1_39 : ParentRangeMatches K1Artifact.commitCode_1_39 159744 :=
  (parent_range_join _ _ 159744 (parent_range_join _ _ 159744 (parent_range_join _ _ 159744 win312 win313) (parent_range_join _ _ 160768 win314 win315)) (parent_range_join _ _ 161792 (parent_range_join _ _ 161792 win316 win317) (parent_range_join _ _ 162816 win318 win319)))
private theorem blk1_40 : ParentRangeMatches K1Artifact.commitCode_1_40 163840 :=
  (parent_range_join _ _ 163840 (parent_range_join _ _ 163840 (parent_range_join _ _ 163840 win320 win321) (parent_range_join _ _ 164864 win322 win323)) (parent_range_join _ _ 165888 (parent_range_join _ _ 165888 win324 win325) (parent_range_join _ _ 166912 win326 win327)))
private theorem blk1_41 : ParentRangeMatches K1Artifact.commitCode_1_41 167936 :=
  (parent_range_join _ _ 167936 (parent_range_join _ _ 167936 (parent_range_join _ _ 167936 win328 win329) (parent_range_join _ _ 168960 win330 win331)) (parent_range_join _ _ 169984 (parent_range_join _ _ 169984 win332 win333) (parent_range_join _ _ 171008 win334 win335)))
private theorem blk1_42 : ParentRangeMatches K1Artifact.commitCode_1_42 172032 :=
  (parent_range_join _ _ 172032 (parent_range_join _ _ 172032 (parent_range_join _ _ 172032 win336 win337) (parent_range_join _ _ 173056 win338 win339)) (parent_range_join _ _ 174080 (parent_range_join _ _ 174080 win340 win341) (parent_range_join _ _ 175104 win342 win343)))
private theorem blk1_43 : ParentRangeMatches K1Artifact.commitCode_1_43 176128 :=
  (parent_range_join _ _ 176128 (parent_range_join _ _ 176128 (parent_range_join _ _ 176128 win344 win345) (parent_range_join _ _ 177152 win346 win347)) (parent_range_join _ _ 178176 (parent_range_join _ _ 178176 win348 win349) (parent_range_join _ _ 179200 win350 win351)))
private theorem blk1_44 : ParentRangeMatches K1Artifact.commitCode_1_44 180224 :=
  (parent_range_join _ _ 180224 (parent_range_join _ _ 180224 (parent_range_join _ _ 180224 win352 win353) (parent_range_join _ _ 181248 win354 win355)) (parent_range_join _ _ 182272 (parent_range_join _ _ 182272 win356 win357) (parent_range_join _ _ 183296 win358 win359)))
private theorem blk1_45 : ParentRangeMatches K1Artifact.commitCode_1_45 184320 :=
  (parent_range_join _ _ 184320 (parent_range_join _ _ 184320 (parent_range_join _ _ 184320 win360 win361) (parent_range_join _ _ 185344 win362 win363)) (parent_range_join _ _ 186368 (parent_range_join _ _ 186368 win364 win365) (parent_range_join _ _ 187392 win366 win367)))
private theorem blk1_46 : ParentRangeMatches K1Artifact.commitCode_1_46 188416 :=
  (parent_range_join _ _ 188416 (parent_range_join _ _ 188416 (parent_range_join _ _ 188416 win368 win369) (parent_range_join _ _ 189440 win370 win371)) (parent_range_join _ _ 190464 (parent_range_join _ _ 190464 win372 win373) (parent_range_join _ _ 191488 win374 win375)))
private theorem blk1_47 : ParentRangeMatches K1Artifact.commitCode_1_47 192512 :=
  (parent_range_join _ _ 192512 (parent_range_join _ _ 192512 (parent_range_join _ _ 192512 win376 win377) (parent_range_join _ _ 193536 win378 win379)) (parent_range_join _ _ 194560 (parent_range_join _ _ 194560 win380 win381) (parent_range_join _ _ 195584 win382 win383)))
private theorem blk1_48 : ParentRangeMatches K1Artifact.commitCode_1_48 196608 :=
  (parent_range_join _ _ 196608 (parent_range_join _ _ 196608 (parent_range_join _ _ 196608 win384 win385) (parent_range_join _ _ 197632 win386 win387)) (parent_range_join _ _ 198656 (parent_range_join _ _ 198656 win388 win389) (parent_range_join _ _ 199680 win390 win391)))
private theorem blk1_49 : ParentRangeMatches K1Artifact.commitCode_1_49 200704 :=
  (parent_range_join _ _ 200704 (parent_range_join _ _ 200704 (parent_range_join _ _ 200704 win392 win393) (parent_range_join _ _ 201728 win394 win395)) (parent_range_join _ _ 202752 (parent_range_join _ _ 202752 win396 win397) (parent_range_join _ _ 203776 win398 win399)))
private theorem blk1_50 : ParentRangeMatches K1Artifact.commitCode_1_50 204800 :=
  (parent_range_join _ _ 204800 (parent_range_join _ _ 204800 (parent_range_join _ _ 204800 win400 win401) (parent_range_join _ _ 205824 win402 win403)) (parent_range_join _ _ 206848 (parent_range_join _ _ 206848 win404 win405) (parent_range_join _ _ 207872 win406 win407)))
private theorem blk1_51 : ParentRangeMatches K1Artifact.commitCode_1_51 208896 :=
  (parent_range_join _ _ 208896 (parent_range_join _ _ 208896 (parent_range_join _ _ 208896 win408 win409) (parent_range_join _ _ 209920 win410 win411)) (parent_range_join _ _ 210944 (parent_range_join _ _ 210944 win412 win413) (parent_range_join _ _ 211968 win414 win415)))
private theorem blk1_52 : ParentRangeMatches K1Artifact.commitCode_1_52 212992 :=
  (parent_range_join _ _ 212992 (parent_range_join _ _ 212992 (parent_range_join _ _ 212992 win416 win417) (parent_range_join _ _ 214016 win418 win419)) (parent_range_join _ _ 215040 (parent_range_join _ _ 215040 win420 win421) (parent_range_join _ _ 216064 win422 win423)))
private theorem blk1_53 : ParentRangeMatches K1Artifact.commitCode_1_53 217088 :=
  (parent_range_join _ _ 217088 (parent_range_join _ _ 217088 (parent_range_join _ _ 217088 win424 win425) (parent_range_join _ _ 218112 win426 win427)) (parent_range_join _ _ 219136 (parent_range_join _ _ 219136 win428 win429) (parent_range_join _ _ 220160 win430 win431)))
private theorem blk1_54 : ParentRangeMatches K1Artifact.commitCode_1_54 221184 :=
  (parent_range_join _ _ 221184 (parent_range_join _ _ 221184 (parent_range_join _ _ 221184 win432 win433) (parent_range_join _ _ 222208 win434 win435)) (parent_range_join _ _ 223232 (parent_range_join _ _ 223232 win436 win437) (parent_range_join _ _ 224256 win438 win439)))
private theorem blk1_55 : ParentRangeMatches K1Artifact.commitCode_1_55 225280 :=
  (parent_range_join _ _ 225280 (parent_range_join _ _ 225280 (parent_range_join _ _ 225280 win440 win441) (parent_range_join _ _ 226304 win442 win443)) (parent_range_join _ _ 227328 (parent_range_join _ _ 227328 win444 win445) (parent_range_join _ _ 228352 win446 win447)))
private theorem blk1_56 : ParentRangeMatches K1Artifact.commitCode_1_56 229376 :=
  (parent_range_join _ _ 229376 (parent_range_join _ _ 229376 (parent_range_join _ _ 229376 win448 win449) (parent_range_join _ _ 230400 win450 win451)) (parent_range_join _ _ 231424 (parent_range_join _ _ 231424 win452 win453) (parent_range_join _ _ 232448 win454 win455)))
private theorem blk1_57 : ParentRangeMatches K1Artifact.commitCode_1_57 233472 :=
  (parent_range_join _ _ 233472 (parent_range_join _ _ 233472 (parent_range_join _ _ 233472 win456 win457) (parent_range_join _ _ 234496 win458 win459)) (parent_range_join _ _ 235520 (parent_range_join _ _ 235520 win460 win461) (parent_range_join _ _ 236544 win462 win463)))
private theorem blk1_58 : ParentRangeMatches K1Artifact.commitCode_1_58 237568 :=
  (parent_range_join _ _ 237568 (parent_range_join _ _ 237568 (parent_range_join _ _ 237568 win464 win465) (parent_range_join _ _ 238592 win466 win467)) (parent_range_join _ _ 239616 (parent_range_join _ _ 239616 win468 win469) (parent_range_join _ _ 240640 win470 win471)))
private theorem blk1_59 : ParentRangeMatches K1Artifact.commitCode_1_59 241664 :=
  (parent_range_join _ _ 241664 (parent_range_join _ _ 241664 (parent_range_join _ _ 241664 win472 win473) (parent_range_join _ _ 242688 win474 win475)) (parent_range_join _ _ 243712 (parent_range_join _ _ 243712 win476 win477) (parent_range_join _ _ 244736 win478 win479)))
private theorem blk1_60 : ParentRangeMatches K1Artifact.commitCode_1_60 245760 :=
  (parent_range_join _ _ 245760 (parent_range_join _ _ 245760 (parent_range_join _ _ 245760 win480 win481) (parent_range_join _ _ 246784 win482 win483)) (parent_range_join _ _ 247808 (parent_range_join _ _ 247808 win484 win485) (parent_range_join _ _ 248832 win486 win487)))
private theorem blk1_61 : ParentRangeMatches K1Artifact.commitCode_1_61 249856 :=
  (parent_range_join _ _ 249856 (parent_range_join _ _ 249856 (parent_range_join _ _ 249856 win488 win489) (parent_range_join _ _ 250880 win490 win491)) (parent_range_join _ _ 251904 (parent_range_join _ _ 251904 win492 win493) (parent_range_join _ _ 252928 win494 win495)))
private theorem blk1_62 : ParentRangeMatches K1Artifact.commitCode_1_62 253952 :=
  (parent_range_join _ _ 253952 (parent_range_join _ _ 253952 (parent_range_join _ _ 253952 win496 win497) (parent_range_join _ _ 254976 win498 win499)) (parent_range_join _ _ 256000 (parent_range_join _ _ 256000 win500 win501) (parent_range_join _ _ 257024 win502 win503)))
private theorem blk1_63 : ParentRangeMatches K1Artifact.commitCode_1_63 258048 :=
  (parent_range_join _ _ 258048 (parent_range_join _ _ 258048 (parent_range_join _ _ 258048 win504 win505) (parent_range_join _ _ 259072 win506 win507)) (parent_range_join _ _ 260096 (parent_range_join _ _ 260096 win508 win509) (parent_range_join _ _ 261120 win510 win511)))
private theorem blk2_0 : ParentRangeMatches K1Artifact.commitCode_2_0 0 :=
  (parent_range_join _ _ 0 (parent_range_join _ _ 0 (parent_range_join _ _ 0 blk1_0 blk1_1) (parent_range_join _ _ 8192 blk1_2 blk1_3)) (parent_range_join _ _ 16384 (parent_range_join _ _ 16384 blk1_4 blk1_5) (parent_range_join _ _ 24576 blk1_6 blk1_7)))
private theorem blk2_1 : ParentRangeMatches K1Artifact.commitCode_2_1 32768 :=
  (parent_range_join _ _ 32768 (parent_range_join _ _ 32768 (parent_range_join _ _ 32768 blk1_8 blk1_9) (parent_range_join _ _ 40960 blk1_10 blk1_11)) (parent_range_join _ _ 49152 (parent_range_join _ _ 49152 blk1_12 blk1_13) (parent_range_join _ _ 57344 blk1_14 blk1_15)))
private theorem blk2_2 : ParentRangeMatches K1Artifact.commitCode_2_2 65536 :=
  (parent_range_join _ _ 65536 (parent_range_join _ _ 65536 (parent_range_join _ _ 65536 blk1_16 blk1_17) (parent_range_join _ _ 73728 blk1_18 blk1_19)) (parent_range_join _ _ 81920 (parent_range_join _ _ 81920 blk1_20 blk1_21) (parent_range_join _ _ 90112 blk1_22 blk1_23)))
private theorem blk2_3 : ParentRangeMatches K1Artifact.commitCode_2_3 98304 :=
  (parent_range_join _ _ 98304 (parent_range_join _ _ 98304 (parent_range_join _ _ 98304 blk1_24 blk1_25) (parent_range_join _ _ 106496 blk1_26 blk1_27)) (parent_range_join _ _ 114688 (parent_range_join _ _ 114688 blk1_28 blk1_29) (parent_range_join _ _ 122880 blk1_30 blk1_31)))
private theorem blk2_4 : ParentRangeMatches K1Artifact.commitCode_2_4 131072 :=
  (parent_range_join _ _ 131072 (parent_range_join _ _ 131072 (parent_range_join _ _ 131072 blk1_32 blk1_33) (parent_range_join _ _ 139264 blk1_34 blk1_35)) (parent_range_join _ _ 147456 (parent_range_join _ _ 147456 blk1_36 blk1_37) (parent_range_join _ _ 155648 blk1_38 blk1_39)))
private theorem blk2_5 : ParentRangeMatches K1Artifact.commitCode_2_5 163840 :=
  (parent_range_join _ _ 163840 (parent_range_join _ _ 163840 (parent_range_join _ _ 163840 blk1_40 blk1_41) (parent_range_join _ _ 172032 blk1_42 blk1_43)) (parent_range_join _ _ 180224 (parent_range_join _ _ 180224 blk1_44 blk1_45) (parent_range_join _ _ 188416 blk1_46 blk1_47)))
private theorem blk2_6 : ParentRangeMatches K1Artifact.commitCode_2_6 196608 :=
  (parent_range_join _ _ 196608 (parent_range_join _ _ 196608 (parent_range_join _ _ 196608 blk1_48 blk1_49) (parent_range_join _ _ 204800 blk1_50 blk1_51)) (parent_range_join _ _ 212992 (parent_range_join _ _ 212992 blk1_52 blk1_53) (parent_range_join _ _ 221184 blk1_54 blk1_55)))
private theorem blk2_7 : ParentRangeMatches K1Artifact.commitCode_2_7 229376 :=
  (parent_range_join _ _ 229376 (parent_range_join _ _ 229376 (parent_range_join _ _ 229376 blk1_56 blk1_57) (parent_range_join _ _ 237568 blk1_58 blk1_59)) (parent_range_join _ _ 245760 (parent_range_join _ _ 245760 blk1_60 blk1_61) (parent_range_join _ _ 253952 blk1_62 blk1_63)))

private theorem parent_packed_matches : ParentRangeMatches K1Artifact.commitCode 0 :=
  (parent_range_join _ _ 0 (parent_range_join _ _ 0 (parent_range_join _ _ 0 blk2_0 blk2_1) (parent_range_join _ _ 65536 blk2_2 blk2_3)) (parent_range_join _ _ 131072 (parent_range_join _ _ 131072 blk2_4 blk2_5) (parent_range_join _ _ 196608 blk2_6 blk2_7)))

def packedWideCommitImage : Image :=
  ⟨ArtifactEncoding.decode 32 K1Artifact.commitCode, ArtifactEncoding.decode 8 K1Artifact.commitData⟩

theorem packed_manifest_image : packedWideCommitImage = K1Artifact.submission.image .commit := by
  simp only [packedWideCommitImage,K1Artifact.submission]

private theorem wide_commit_code :
    packedWideCommitImage.code = ArtifactEncoding.decode 32 K1Artifact.commitCode := by
  simp only [packedWideCommitImage]

private theorem packed_index_fetch (state : MachineState) (index : Nat)
    (point : state.pc=BitVec.ofNat 64 (4096+4*index))
    (lower : (181047 : Nat) ≤ index) (upper : index < 262039) :
    fetch packedWideCommitImage state=decodeInstruction (expectedWord index) := by
  have pc : state.pc.toNat=4096+4*index := by
    rw [point,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have packed := parent_packed_matches ⟨index,upper⟩
    (by simpa only [Nat.zero_add,Fin.val_mk] using lower)
    (by simpa only [Nat.zero_add,Fin.val_mk] using upper)
  have word : packedWideCommitImage.code.getD index 0 = expectedWord index := by
    rw [wide_commit_code,ArtifactEncoding.getD_decode _ _ _ upper]
    simpa only [Nat.zero_add] using packed
  have inside : index<packedWideCommitImage.code.length := by
    rw [wide_commit_code,ArtifactEncoding.length_decode]
    exact upper
  have atIndex : packedWideCommitImage.code[index]? = some (expectedWord index) := by
    rw [List.getElem?_eq_getElem inside,←List.getD_eq_getElem _ _ inside,word]
  rw [fetch,pc,if_pos (by omega),
    show (4096+4*index-4096)/4=index by omega,atIndex]

private theorem l21_opcode (state : MachineState) (slot : Nat) (bounded : slot<8192) (part : Fin 3)
    (pc : state.pc=l21PC l21Base slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (l21Word part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(181054+3*slot+part.val)) := by
    rw [pc]
    change BitVec.ofNat 64 728312+BitVec.ofNat 64 (12*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (181054+3*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,if_neg (by omega),if_pos (by omega)]
  simp only [l21Word]
  have phase : ((181054+3*slot+part.val)-181054)%3=part.val%3 := by omega
  rw [phase]

theorem l21_words (slot : Nat) (bounded : slot<8192) :
    L21WordsAt packedWideCommitImage (l21PC l21Base slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · exact l21_opcode state slot bounded 0 (by simpa using pc)
  · exact l21_opcode state slot bounded 1 pc
  · exact l21_opcode state slot bounded 2 pc

private theorem bandA_opcode (state : MachineState) (slot : Nat) (bounded : slot<10240) (part : Fin 4)
    (pc : state.pc=kindPC recordKind bandABase slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (bandAWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(205639+4*slot+part.val)) := by
    rw [pc]
    change BitVec.ofNat 64 826652+BitVec.ofNat 64 (16*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (205639+4*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  simp only [bandAWord]
  have phase : ((205639+4*slot+part.val)-205639)%4=part.val%4 := by omega
  rw [phase]

theorem bandA_words (slot : Nat) (bounded : slot<10240) :
    PackedParentWordsAt packedWideCommitImage (kindPC recordKind bandABase slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · exact bandA_opcode state slot bounded 0 (by simpa using pc)
  · exact bandA_opcode state slot bounded 1 pc
  · exact bandA_opcode state slot bounded 2 pc
  · exact bandA_opcode state slot bounded 3 pc

private theorem bandB_opcode (state : MachineState) (slot : Nat) (bounded : slot<2570) (part : Fin 6)
    (pc : state.pc=kindPC t238Kind bandBBase slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (bandBWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(246602+6*slot+part.val)) := by
    rw [pc]
    change BitVec.ofNat 64 990504+BitVec.ofNat 64 (24*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (246602+6*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  simp only [bandBWord]
  have phase : ((246602+6*slot+part.val)-246602)%6=part.val%6 := by omega
  rw [phase]

theorem bandB_words (slot : Nat) (bounded : slot<2570) :
    T238WordsAt packedWideCommitImage (kindPC t238Kind bandBBase slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · exact bandB_opcode state slot bounded 0 (by simpa using pc)
  · exact bandB_opcode state slot bounded 1 pc
  · exact bandB_opcode state slot bounded 2 pc
  · exact bandB_opcode state slot bounded 3 pc
  · exact bandB_opcode state slot bounded 4 pc
  · exact bandB_opcode state slot bounded 5 pc

def l21Control : L21Control packedWideCommitImage l21Base 8192 where
  backOffset := 1998844
  backTarget := by decide
  branch state pc := packed_index_fetch state 205630 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 205631 pc (by decide) (by decide)

def bandAControl : BandControl packedWideCommitImage recordKind bandABase 10240 where
  backOffset := 1933308
  backTarget := by decide
  branch state pc := packed_index_fetch state 246599 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 246600 pc (by decide) (by decide)

def bandBControl : BandControl packedWideCommitImage t238Kind bandBBase 2570 where
  backOffset := 2035468
  backTarget := by decide
  branch state pc := packed_index_fetch state 262022 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 262023 pc (by decide) (by decide)

theorem fetch_l21_setup (s : MachineState) (i : Fin 7) (pc : s.pc=BitVec.ofNat 64 (4096+4*(181047+i.val))) :
    fetch packedWideCommitImage s=some (.base ((l21SetupOps[i]?).getD .EBREAK)) := by
  have hi := i.isLt
  rw [packed_index_fetch s _ pc (by omega) (by omega)]
  fin_cases i <;> rfl

theorem fetch_heap_setup (s : MachineState) (i : Fin 7) (pc : s.pc=BitVec.ofNat 64 (4096+4*(205632+i.val))) :
    fetch packedWideCommitImage s=some (.base ((heapSetupOps[i]?).getD .EBREAK)) := by
  have hi := i.isLt
  rw [packed_index_fetch s _ pc (by omega) (by omega)]
  fin_cases i <;> rfl

theorem fetch_mid (s : MachineState) (pc : s.pc=midPC) :
    fetch packedWideCommitImage s=some (.base (.ADDI .x7 .x9 32)) :=
  packed_index_fetch s 246601 pc (by decide) (by decide)

theorem root_parent_words (s : MachineState) :
    (s.pc=rootParentPC → fetch packedWideCommitImage s=some (.base .ECALL)) ∧
    (s.pc=rootParentPC+4 → fetch packedWideCommitImage s=some (.base (.LHU .x31 .x12 28))) ∧
    (s.pc=rootParentPC+8 → fetch packedWideCommitImage s=some (.base (.AND .x31 .x31 .x6))) ∧
    (s.pc=rootParentPC+12 → fetch packedWideCommitImage s=some (.base (.SW .x12 .x31 28))) :=
  ⟨fun pc => packed_index_fetch s 262024 pc (by decide) (by decide),
   fun pc => packed_index_fetch s 262025 pc (by decide) (by decide),
   fun pc => packed_index_fetch s 262026 pc (by decide) (by decide),
   fun pc => packed_index_fetch s 262027 pc (by decide) (by decide)⟩

private theorem wide_root_fetch (state : MachineState) (i : Nat) (inside : i < 11)
    (pc : state.pc=BitVec.ofNat 64 (1052208+4*i)) :
    fetch packedWideCommitImage state=some (.base ((rootOps[i]?).getD .ECALL)) := by
  have address : state.pc=BitVec.ofNat 64 (4096+4*(262028+i)) := by
    rw [pc]
    congr 1
    omega
  rw [packed_index_fetch state (262028+i) address (by omega) (by omega)]
  interval_cases i <;> rfl

attribute [local irreducible] execute

def l21StartPrefix (s : MachineState) (i : Nat) := (l21SetupOps.take i).foldl execInstrBr s
def heapStartPrefix (s : MachineState) (i : Nat) := (heapSetupOps.take i).foldl execInstrBr s

theorem l21Start_run (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*tailStart)) (fuel : Nat) :
    execute packedWideCommitImage (7+fuel) s true = (do
      let e ← execute packedWideCommitImage fuel (l21StartPrefix s l21SetupLen) true; return e.charge 7 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := l21StartPrefix s)
  intro i hi
  refine ⟨.base ((l21SetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (l21StartPrefix s i).pc=BitVec.ofNat 64 (4096+4*(181047+i)) := by
      interval_cases i <;> simp only [l21StartPrefix,l21SetupOps,List.take,List.foldl,execInstrBr,
        MachineState.setPC,pc,tailStart] <;> rfl
    have cell := fetch_l21_setup (l21StartPrefix s i) ⟨i,hi⟩ here
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem heapStart_run (s : MachineState) (pc : s.pc=heapSetupPC) (fuel : Nat) :
    execute packedWideCommitImage (7+fuel) s true = (do
      let e ← execute packedWideCommitImage fuel (heapStartPrefix s 7) true; return e.charge 7 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := heapStartPrefix s)
  intro i hi
  refine ⟨.base ((heapSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (heapStartPrefix s i).pc=BitVec.ofNat 64 (4096+4*(205632+i)) := by
      interval_cases i <;> simp only [heapStartPrefix,heapSetupOps,List.take,List.foldl,execInstrBr,
        MachineState.setPC,pc,heapSetupPC] <;> rfl
    have cell := fetch_heap_setup (heapStartPrefix s i) ⟨i,hi⟩ here
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

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

theorem execute_packed_root (state : MachineState) (pc : state.pc=rootPC)
    (heap : state.getReg .x9=4294971424) (out : state.getReg .x8=4294971392) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true = pure ⟨.success,rootPrefix state 10,11,0⟩ := by
  have prefixPC (i : Nat) (inside : i<11) :
      (rootPrefix state i).pc=BitVec.ofNat 64 (1052208+4*i) := by
    interval_cases i <;>
      simp only [rootPrefix,rootOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc,rootPC] <;> rfl
  have run (left : Nat) :
      execute packedWideCommitImage (10+left) state true =
        (do let result ← execute packedWideCommitImage left (rootPrefix state 10) true
            return result.charge 10 0) := by
    apply CommitGolfCandidate.execute_unit_steps (states := rootPrefix state)
    intro i inside
    refine ⟨.base ((rootOps[i]?).getD .ECALL),?_,?_,?_⟩
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
