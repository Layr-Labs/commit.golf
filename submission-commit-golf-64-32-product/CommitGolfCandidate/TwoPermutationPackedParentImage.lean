import CommitGolfCandidate.TwoPermutationWideParents
import CommitGolf.Artifact
import CommitGolfCandidate.TwoPermutationPackedParentControl
import CommitGolfCandidate.TwoPermutationCommitRun
import CommitGolfCandidate.C3PParents

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

private def fullWord (index : Nat) : BitVec 32 :=
  if index%3=0 then 0x73 else if index%3=1 then 0xe7050513 else 0xfe060613

private def packedWord (index : Nat) : BitVec 32 :=
  if index%4=0 then 0x73 else if index%4=1 then 0x00061f23 else if index%4=2 then 0xfc050513 else 0xfe060613

private def rootWords : List (BitVec 32) :=
  [0x0204bf83,0x01f43023,0x0284bf83,0x01f43423,0x0304bf83,0x01f43823,0x0384bf83,0x01f43c23,0x00100293,0x00000513,0x00000073]

private def expectedWord (i : Nat) : BitVec 32 :=
  if 53371 ≤ i ∧ i < 151675 then fullWord (i-53371)
  else if 151678 ≤ i ∧ i < 262058 then packedWord (i-151678)
  else if i = 53369 then 0x10000937
  else if i = 53370 then 0x00890933
  else if i = 151675 then 0x01260463
  else if i = 151676 then 0xffd9f06f
  else if i = 151677 then 0xe616b06f
  else if i = 262058 then 0x00960463
  else if i = 262059 then 0xb4c9406f
  else rootWords.getD (i-262060) 0

private def ParentRangeMatches {count : Nat} (packed : ArtifactEncoding.Packed count)
    (offset : Nat) : Prop :=
  ∀ i : Fin count, 53369≤offset+i.val → offset+i.val<262071 →
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

private theorem parent_range_before {count : Nat} (packed : ArtifactEncoding.Packed count)
    (offset : Nat) (last : offset+count ≤ 53369) : ParentRangeMatches packed offset := by
  intro i lower _
  have := i.isLt
  omega

private theorem full_window (packed : ArtifactEncoding.Packed 512) (offset phase : Nat)
    (alignment : (offset-53371)%3=phase%3)
    (inside : 53371≤offset) (ends : offset+512≤151675)
    (decode : ∀ i : Fin 512, packed.get 32 i=fullWord (phase+i.val)) :
    ParentRangeMatches packed offset := by
  intro i _ _
  have before := i.isLt
  rw [expectedWord,ite_eq_left (by omega),decode]
  simp only [fullWord]
  have same : (phase+i.val)%3=(offset+i.val-53371)%3 := by omega
  rw [same]

private theorem full_periodic_2 (i : Fin 512) :
    Artifact.commitCode_0_105.get 32 i=fullWord (2+i.val) := by
  fin_cases i <;> rfl

private theorem full_periodic_1 (i : Fin 512) :
    Artifact.commitCode_0_106.get 32 i=fullWord (1+i.val) := by
  fin_cases i <;> rfl

private theorem full_periodic_0 (i : Fin 512) :
    Artifact.commitCode_0_107.get 32 i=fullWord (0+i.val) := by
  fin_cases i <;> rfl

private theorem packed_window (packed : ArtifactEncoding.Packed 512) (offset phase : Nat)
    (alignment : (offset-151678)%4=phase%4)
    (inside : 151678≤offset) (ends : offset+512≤262058)
    (decode : ∀ i : Fin 512, packed.get 32 i=packedWord (phase+i.val)) :
    ParentRangeMatches packed offset := by
  intro i _ _
  have before := i.isLt
  rw [expectedWord,ite_eq_right (by omega), ite_eq_left (by omega),decode]
  simp only [packedWord]
  have same : (phase+i.val)%4=(offset+i.val-151678)%4 := by omega
  rw [same]

private theorem packed_periodic_2 (i : Fin 512) :
    Artifact.commitCode_0_297.get 32 i=packedWord (2+i.val) := by
  fin_cases i <;> rfl

private theorem parent_window_104 : ParentRangeMatches Artifact.commitCode_0_104 53248 := by
  unfold ParentRangeMatches expectedWord fullWord packedWord rootWords
  decide +kernel

private theorem parent_window_105 : ParentRangeMatches Artifact.commitCode_0_105 53760 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_106 : ParentRangeMatches Artifact.commitCode_0_106 54272 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_107 : ParentRangeMatches Artifact.commitCode_0_107 54784 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_108 : ParentRangeMatches Artifact.commitCode_0_108 55296 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_109 : ParentRangeMatches Artifact.commitCode_0_109 55808 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_110 : ParentRangeMatches Artifact.commitCode_0_110 56320 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_111 : ParentRangeMatches Artifact.commitCode_0_111 56832 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_112 : ParentRangeMatches Artifact.commitCode_0_112 57344 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_113 : ParentRangeMatches Artifact.commitCode_0_113 57856 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_114 : ParentRangeMatches Artifact.commitCode_0_114 58368 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_115 : ParentRangeMatches Artifact.commitCode_0_115 58880 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_116 : ParentRangeMatches Artifact.commitCode_0_116 59392 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_117 : ParentRangeMatches Artifact.commitCode_0_117 59904 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_118 : ParentRangeMatches Artifact.commitCode_0_118 60416 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_119 : ParentRangeMatches Artifact.commitCode_0_119 60928 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_120 : ParentRangeMatches Artifact.commitCode_0_120 61440 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_121 : ParentRangeMatches Artifact.commitCode_0_121 61952 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_122 : ParentRangeMatches Artifact.commitCode_0_122 62464 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_123 : ParentRangeMatches Artifact.commitCode_0_123 62976 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_124 : ParentRangeMatches Artifact.commitCode_0_124 63488 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_125 : ParentRangeMatches Artifact.commitCode_0_125 64000 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_126 : ParentRangeMatches Artifact.commitCode_0_126 64512 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_127 : ParentRangeMatches Artifact.commitCode_0_127 65024 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_128 : ParentRangeMatches Artifact.commitCode_0_128 65536 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_129 : ParentRangeMatches Artifact.commitCode_0_129 66048 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_130 : ParentRangeMatches Artifact.commitCode_0_130 66560 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_131 : ParentRangeMatches Artifact.commitCode_0_131 67072 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_132 : ParentRangeMatches Artifact.commitCode_0_132 67584 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_133 : ParentRangeMatches Artifact.commitCode_0_133 68096 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_134 : ParentRangeMatches Artifact.commitCode_0_134 68608 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_135 : ParentRangeMatches Artifact.commitCode_0_135 69120 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_136 : ParentRangeMatches Artifact.commitCode_0_136 69632 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_137 : ParentRangeMatches Artifact.commitCode_0_137 70144 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_138 : ParentRangeMatches Artifact.commitCode_0_138 70656 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_139 : ParentRangeMatches Artifact.commitCode_0_139 71168 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_140 : ParentRangeMatches Artifact.commitCode_0_140 71680 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_141 : ParentRangeMatches Artifact.commitCode_0_141 72192 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_142 : ParentRangeMatches Artifact.commitCode_0_142 72704 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_143 : ParentRangeMatches Artifact.commitCode_0_143 73216 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_144 : ParentRangeMatches Artifact.commitCode_0_144 73728 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_145 : ParentRangeMatches Artifact.commitCode_0_145 74240 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_146 : ParentRangeMatches Artifact.commitCode_0_146 74752 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_147 : ParentRangeMatches Artifact.commitCode_0_147 75264 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_148 : ParentRangeMatches Artifact.commitCode_0_148 75776 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_149 : ParentRangeMatches Artifact.commitCode_0_149 76288 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_150 : ParentRangeMatches Artifact.commitCode_0_150 76800 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_151 : ParentRangeMatches Artifact.commitCode_0_151 77312 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_152 : ParentRangeMatches Artifact.commitCode_0_152 77824 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_153 : ParentRangeMatches Artifact.commitCode_0_153 78336 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_154 : ParentRangeMatches Artifact.commitCode_0_154 78848 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_155 : ParentRangeMatches Artifact.commitCode_0_155 79360 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_156 : ParentRangeMatches Artifact.commitCode_0_156 79872 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_157 : ParentRangeMatches Artifact.commitCode_0_157 80384 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_158 : ParentRangeMatches Artifact.commitCode_0_158 80896 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_159 : ParentRangeMatches Artifact.commitCode_0_159 81408 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_160 : ParentRangeMatches Artifact.commitCode_0_160 81920 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_161 : ParentRangeMatches Artifact.commitCode_0_161 82432 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_162 : ParentRangeMatches Artifact.commitCode_0_162 82944 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_163 : ParentRangeMatches Artifact.commitCode_0_163 83456 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_164 : ParentRangeMatches Artifact.commitCode_0_164 83968 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_165 : ParentRangeMatches Artifact.commitCode_0_165 84480 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_166 : ParentRangeMatches Artifact.commitCode_0_166 84992 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_167 : ParentRangeMatches Artifact.commitCode_0_167 85504 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_168 : ParentRangeMatches Artifact.commitCode_0_168 86016 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_169 : ParentRangeMatches Artifact.commitCode_0_169 86528 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_170 : ParentRangeMatches Artifact.commitCode_0_170 87040 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_171 : ParentRangeMatches Artifact.commitCode_0_171 87552 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_172 : ParentRangeMatches Artifact.commitCode_0_172 88064 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_173 : ParentRangeMatches Artifact.commitCode_0_173 88576 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_174 : ParentRangeMatches Artifact.commitCode_0_174 89088 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_175 : ParentRangeMatches Artifact.commitCode_0_175 89600 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_176 : ParentRangeMatches Artifact.commitCode_0_176 90112 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_177 : ParentRangeMatches Artifact.commitCode_0_177 90624 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_178 : ParentRangeMatches Artifact.commitCode_0_178 91136 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_179 : ParentRangeMatches Artifact.commitCode_0_179 91648 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_180 : ParentRangeMatches Artifact.commitCode_0_180 92160 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_181 : ParentRangeMatches Artifact.commitCode_0_181 92672 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_182 : ParentRangeMatches Artifact.commitCode_0_182 93184 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_183 : ParentRangeMatches Artifact.commitCode_0_183 93696 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_184 : ParentRangeMatches Artifact.commitCode_0_184 94208 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_185 : ParentRangeMatches Artifact.commitCode_0_185 94720 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_186 : ParentRangeMatches Artifact.commitCode_0_186 95232 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_187 : ParentRangeMatches Artifact.commitCode_0_187 95744 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_188 : ParentRangeMatches Artifact.commitCode_0_188 96256 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_189 : ParentRangeMatches Artifact.commitCode_0_189 96768 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_190 : ParentRangeMatches Artifact.commitCode_0_190 97280 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_191 : ParentRangeMatches Artifact.commitCode_0_191 97792 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_192 : ParentRangeMatches Artifact.commitCode_0_192 98304 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_193 : ParentRangeMatches Artifact.commitCode_0_193 98816 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_194 : ParentRangeMatches Artifact.commitCode_0_194 99328 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_195 : ParentRangeMatches Artifact.commitCode_0_195 99840 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_196 : ParentRangeMatches Artifact.commitCode_0_196 100352 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_197 : ParentRangeMatches Artifact.commitCode_0_197 100864 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_198 : ParentRangeMatches Artifact.commitCode_0_198 101376 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_199 : ParentRangeMatches Artifact.commitCode_0_199 101888 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_200 : ParentRangeMatches Artifact.commitCode_0_200 102400 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_201 : ParentRangeMatches Artifact.commitCode_0_201 102912 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_202 : ParentRangeMatches Artifact.commitCode_0_202 103424 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_203 : ParentRangeMatches Artifact.commitCode_0_203 103936 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_204 : ParentRangeMatches Artifact.commitCode_0_204 104448 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_205 : ParentRangeMatches Artifact.commitCode_0_205 104960 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_206 : ParentRangeMatches Artifact.commitCode_0_206 105472 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_207 : ParentRangeMatches Artifact.commitCode_0_207 105984 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_208 : ParentRangeMatches Artifact.commitCode_0_208 106496 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_209 : ParentRangeMatches Artifact.commitCode_0_209 107008 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_210 : ParentRangeMatches Artifact.commitCode_0_210 107520 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_211 : ParentRangeMatches Artifact.commitCode_0_211 108032 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_212 : ParentRangeMatches Artifact.commitCode_0_212 108544 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_213 : ParentRangeMatches Artifact.commitCode_0_213 109056 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_214 : ParentRangeMatches Artifact.commitCode_0_214 109568 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_215 : ParentRangeMatches Artifact.commitCode_0_215 110080 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_216 : ParentRangeMatches Artifact.commitCode_0_216 110592 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_217 : ParentRangeMatches Artifact.commitCode_0_217 111104 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_218 : ParentRangeMatches Artifact.commitCode_0_218 111616 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_219 : ParentRangeMatches Artifact.commitCode_0_219 112128 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_220 : ParentRangeMatches Artifact.commitCode_0_220 112640 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_221 : ParentRangeMatches Artifact.commitCode_0_221 113152 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_222 : ParentRangeMatches Artifact.commitCode_0_222 113664 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_223 : ParentRangeMatches Artifact.commitCode_0_223 114176 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_224 : ParentRangeMatches Artifact.commitCode_0_224 114688 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_225 : ParentRangeMatches Artifact.commitCode_0_225 115200 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_226 : ParentRangeMatches Artifact.commitCode_0_226 115712 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_227 : ParentRangeMatches Artifact.commitCode_0_227 116224 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_228 : ParentRangeMatches Artifact.commitCode_0_228 116736 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_229 : ParentRangeMatches Artifact.commitCode_0_229 117248 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_230 : ParentRangeMatches Artifact.commitCode_0_230 117760 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_231 : ParentRangeMatches Artifact.commitCode_0_231 118272 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_232 : ParentRangeMatches Artifact.commitCode_0_232 118784 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_233 : ParentRangeMatches Artifact.commitCode_0_233 119296 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_234 : ParentRangeMatches Artifact.commitCode_0_234 119808 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_235 : ParentRangeMatches Artifact.commitCode_0_235 120320 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_236 : ParentRangeMatches Artifact.commitCode_0_236 120832 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_237 : ParentRangeMatches Artifact.commitCode_0_237 121344 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_238 : ParentRangeMatches Artifact.commitCode_0_238 121856 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_239 : ParentRangeMatches Artifact.commitCode_0_239 122368 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_240 : ParentRangeMatches Artifact.commitCode_0_240 122880 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_241 : ParentRangeMatches Artifact.commitCode_0_241 123392 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_242 : ParentRangeMatches Artifact.commitCode_0_242 123904 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_243 : ParentRangeMatches Artifact.commitCode_0_243 124416 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_244 : ParentRangeMatches Artifact.commitCode_0_244 124928 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_245 : ParentRangeMatches Artifact.commitCode_0_245 125440 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_246 : ParentRangeMatches Artifact.commitCode_0_246 125952 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_247 : ParentRangeMatches Artifact.commitCode_0_247 126464 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_248 : ParentRangeMatches Artifact.commitCode_0_248 126976 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_249 : ParentRangeMatches Artifact.commitCode_0_249 127488 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_250 : ParentRangeMatches Artifact.commitCode_0_250 128000 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_251 : ParentRangeMatches Artifact.commitCode_0_251 128512 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_252 : ParentRangeMatches Artifact.commitCode_0_252 129024 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_253 : ParentRangeMatches Artifact.commitCode_0_253 129536 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_254 : ParentRangeMatches Artifact.commitCode_0_254 130048 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_255 : ParentRangeMatches Artifact.commitCode_0_255 130560 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_256 : ParentRangeMatches Artifact.commitCode_0_256 131072 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_257 : ParentRangeMatches Artifact.commitCode_0_257 131584 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_258 : ParentRangeMatches Artifact.commitCode_0_258 132096 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_259 : ParentRangeMatches Artifact.commitCode_0_259 132608 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_260 : ParentRangeMatches Artifact.commitCode_0_260 133120 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_261 : ParentRangeMatches Artifact.commitCode_0_261 133632 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_262 : ParentRangeMatches Artifact.commitCode_0_262 134144 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_263 : ParentRangeMatches Artifact.commitCode_0_263 134656 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_264 : ParentRangeMatches Artifact.commitCode_0_264 135168 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_265 : ParentRangeMatches Artifact.commitCode_0_265 135680 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_266 : ParentRangeMatches Artifact.commitCode_0_266 136192 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_267 : ParentRangeMatches Artifact.commitCode_0_267 136704 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_268 : ParentRangeMatches Artifact.commitCode_0_268 137216 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_269 : ParentRangeMatches Artifact.commitCode_0_269 137728 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_270 : ParentRangeMatches Artifact.commitCode_0_270 138240 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_271 : ParentRangeMatches Artifact.commitCode_0_271 138752 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_272 : ParentRangeMatches Artifact.commitCode_0_272 139264 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_273 : ParentRangeMatches Artifact.commitCode_0_273 139776 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_274 : ParentRangeMatches Artifact.commitCode_0_274 140288 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_275 : ParentRangeMatches Artifact.commitCode_0_275 140800 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_276 : ParentRangeMatches Artifact.commitCode_0_276 141312 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_277 : ParentRangeMatches Artifact.commitCode_0_277 141824 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_278 : ParentRangeMatches Artifact.commitCode_0_278 142336 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_279 : ParentRangeMatches Artifact.commitCode_0_279 142848 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_280 : ParentRangeMatches Artifact.commitCode_0_280 143360 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_281 : ParentRangeMatches Artifact.commitCode_0_281 143872 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_282 : ParentRangeMatches Artifact.commitCode_0_282 144384 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_283 : ParentRangeMatches Artifact.commitCode_0_283 144896 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_284 : ParentRangeMatches Artifact.commitCode_0_284 145408 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_285 : ParentRangeMatches Artifact.commitCode_0_285 145920 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_286 : ParentRangeMatches Artifact.commitCode_0_286 146432 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_287 : ParentRangeMatches Artifact.commitCode_0_287 146944 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_288 : ParentRangeMatches Artifact.commitCode_0_288 147456 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_289 : ParentRangeMatches Artifact.commitCode_0_289 147968 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_290 : ParentRangeMatches Artifact.commitCode_0_290 148480 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_291 : ParentRangeMatches Artifact.commitCode_0_291 148992 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_292 : ParentRangeMatches Artifact.commitCode_0_292 149504 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_293 : ParentRangeMatches Artifact.commitCode_0_293 150016 := by
  exact full_window _ _ 0 (by decide) (by decide) (by decide) full_periodic_0

private theorem parent_window_294 : ParentRangeMatches Artifact.commitCode_0_294 150528 := by
  exact full_window _ _ 2 (by decide) (by decide) (by decide) full_periodic_2

private theorem parent_window_295 : ParentRangeMatches Artifact.commitCode_0_295 151040 := by
  exact full_window _ _ 1 (by decide) (by decide) (by decide) full_periodic_1

private theorem parent_window_296 : ParentRangeMatches Artifact.commitCode_0_296 151552 := by
  unfold ParentRangeMatches expectedWord fullWord packedWord rootWords
  decide +kernel

private theorem parent_window_297 : ParentRangeMatches Artifact.commitCode_0_297 152064 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_298 : ParentRangeMatches Artifact.commitCode_0_298 152576 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_299 : ParentRangeMatches Artifact.commitCode_0_299 153088 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_300 : ParentRangeMatches Artifact.commitCode_0_300 153600 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_301 : ParentRangeMatches Artifact.commitCode_0_301 154112 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_302 : ParentRangeMatches Artifact.commitCode_0_302 154624 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_303 : ParentRangeMatches Artifact.commitCode_0_303 155136 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_304 : ParentRangeMatches Artifact.commitCode_0_304 155648 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_305 : ParentRangeMatches Artifact.commitCode_0_305 156160 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_306 : ParentRangeMatches Artifact.commitCode_0_306 156672 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_307 : ParentRangeMatches Artifact.commitCode_0_307 157184 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_308 : ParentRangeMatches Artifact.commitCode_0_308 157696 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_309 : ParentRangeMatches Artifact.commitCode_0_309 158208 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_310 : ParentRangeMatches Artifact.commitCode_0_310 158720 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_311 : ParentRangeMatches Artifact.commitCode_0_311 159232 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_312 : ParentRangeMatches Artifact.commitCode_0_312 159744 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_313 : ParentRangeMatches Artifact.commitCode_0_313 160256 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_314 : ParentRangeMatches Artifact.commitCode_0_314 160768 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_315 : ParentRangeMatches Artifact.commitCode_0_315 161280 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_316 : ParentRangeMatches Artifact.commitCode_0_316 161792 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_317 : ParentRangeMatches Artifact.commitCode_0_317 162304 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_318 : ParentRangeMatches Artifact.commitCode_0_318 162816 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_319 : ParentRangeMatches Artifact.commitCode_0_319 163328 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_320 : ParentRangeMatches Artifact.commitCode_0_320 163840 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_321 : ParentRangeMatches Artifact.commitCode_0_321 164352 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_322 : ParentRangeMatches Artifact.commitCode_0_322 164864 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_323 : ParentRangeMatches Artifact.commitCode_0_323 165376 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_324 : ParentRangeMatches Artifact.commitCode_0_324 165888 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_325 : ParentRangeMatches Artifact.commitCode_0_325 166400 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_326 : ParentRangeMatches Artifact.commitCode_0_326 166912 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_327 : ParentRangeMatches Artifact.commitCode_0_327 167424 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_328 : ParentRangeMatches Artifact.commitCode_0_328 167936 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_329 : ParentRangeMatches Artifact.commitCode_0_329 168448 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_330 : ParentRangeMatches Artifact.commitCode_0_330 168960 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_331 : ParentRangeMatches Artifact.commitCode_0_331 169472 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_332 : ParentRangeMatches Artifact.commitCode_0_332 169984 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_333 : ParentRangeMatches Artifact.commitCode_0_333 170496 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_334 : ParentRangeMatches Artifact.commitCode_0_334 171008 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_335 : ParentRangeMatches Artifact.commitCode_0_335 171520 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_336 : ParentRangeMatches Artifact.commitCode_0_336 172032 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_337 : ParentRangeMatches Artifact.commitCode_0_337 172544 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_338 : ParentRangeMatches Artifact.commitCode_0_338 173056 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_339 : ParentRangeMatches Artifact.commitCode_0_339 173568 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_340 : ParentRangeMatches Artifact.commitCode_0_340 174080 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_341 : ParentRangeMatches Artifact.commitCode_0_341 174592 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_342 : ParentRangeMatches Artifact.commitCode_0_342 175104 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_343 : ParentRangeMatches Artifact.commitCode_0_343 175616 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_344 : ParentRangeMatches Artifact.commitCode_0_344 176128 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_345 : ParentRangeMatches Artifact.commitCode_0_345 176640 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_346 : ParentRangeMatches Artifact.commitCode_0_346 177152 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_347 : ParentRangeMatches Artifact.commitCode_0_347 177664 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_348 : ParentRangeMatches Artifact.commitCode_0_348 178176 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_349 : ParentRangeMatches Artifact.commitCode_0_349 178688 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_350 : ParentRangeMatches Artifact.commitCode_0_350 179200 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_351 : ParentRangeMatches Artifact.commitCode_0_351 179712 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_352 : ParentRangeMatches Artifact.commitCode_0_352 180224 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_353 : ParentRangeMatches Artifact.commitCode_0_353 180736 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_354 : ParentRangeMatches Artifact.commitCode_0_354 181248 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_355 : ParentRangeMatches Artifact.commitCode_0_355 181760 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_356 : ParentRangeMatches Artifact.commitCode_0_356 182272 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_357 : ParentRangeMatches Artifact.commitCode_0_357 182784 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_358 : ParentRangeMatches Artifact.commitCode_0_358 183296 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_359 : ParentRangeMatches Artifact.commitCode_0_359 183808 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_360 : ParentRangeMatches Artifact.commitCode_0_360 184320 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_361 : ParentRangeMatches Artifact.commitCode_0_361 184832 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_362 : ParentRangeMatches Artifact.commitCode_0_362 185344 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_363 : ParentRangeMatches Artifact.commitCode_0_363 185856 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_364 : ParentRangeMatches Artifact.commitCode_0_364 186368 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_365 : ParentRangeMatches Artifact.commitCode_0_365 186880 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_366 : ParentRangeMatches Artifact.commitCode_0_366 187392 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_367 : ParentRangeMatches Artifact.commitCode_0_367 187904 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_368 : ParentRangeMatches Artifact.commitCode_0_368 188416 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_369 : ParentRangeMatches Artifact.commitCode_0_369 188928 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_370 : ParentRangeMatches Artifact.commitCode_0_370 189440 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_371 : ParentRangeMatches Artifact.commitCode_0_371 189952 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_372 : ParentRangeMatches Artifact.commitCode_0_372 190464 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_373 : ParentRangeMatches Artifact.commitCode_0_373 190976 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_374 : ParentRangeMatches Artifact.commitCode_0_374 191488 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_375 : ParentRangeMatches Artifact.commitCode_0_375 192000 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_376 : ParentRangeMatches Artifact.commitCode_0_376 192512 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_377 : ParentRangeMatches Artifact.commitCode_0_377 193024 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_378 : ParentRangeMatches Artifact.commitCode_0_378 193536 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_379 : ParentRangeMatches Artifact.commitCode_0_379 194048 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_380 : ParentRangeMatches Artifact.commitCode_0_380 194560 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_381 : ParentRangeMatches Artifact.commitCode_0_381 195072 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_382 : ParentRangeMatches Artifact.commitCode_0_382 195584 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_383 : ParentRangeMatches Artifact.commitCode_0_383 196096 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_384 : ParentRangeMatches Artifact.commitCode_0_384 196608 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_385 : ParentRangeMatches Artifact.commitCode_0_385 197120 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_386 : ParentRangeMatches Artifact.commitCode_0_386 197632 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_387 : ParentRangeMatches Artifact.commitCode_0_387 198144 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_388 : ParentRangeMatches Artifact.commitCode_0_388 198656 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_389 : ParentRangeMatches Artifact.commitCode_0_389 199168 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_390 : ParentRangeMatches Artifact.commitCode_0_390 199680 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_391 : ParentRangeMatches Artifact.commitCode_0_391 200192 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_392 : ParentRangeMatches Artifact.commitCode_0_392 200704 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_393 : ParentRangeMatches Artifact.commitCode_0_393 201216 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_394 : ParentRangeMatches Artifact.commitCode_0_394 201728 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_395 : ParentRangeMatches Artifact.commitCode_0_395 202240 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_396 : ParentRangeMatches Artifact.commitCode_0_396 202752 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_397 : ParentRangeMatches Artifact.commitCode_0_397 203264 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_398 : ParentRangeMatches Artifact.commitCode_0_398 203776 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_399 : ParentRangeMatches Artifact.commitCode_0_399 204288 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_400 : ParentRangeMatches Artifact.commitCode_0_400 204800 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_401 : ParentRangeMatches Artifact.commitCode_0_401 205312 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_402 : ParentRangeMatches Artifact.commitCode_0_402 205824 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_403 : ParentRangeMatches Artifact.commitCode_0_403 206336 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_404 : ParentRangeMatches Artifact.commitCode_0_404 206848 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_405 : ParentRangeMatches Artifact.commitCode_0_405 207360 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_406 : ParentRangeMatches Artifact.commitCode_0_406 207872 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_407 : ParentRangeMatches Artifact.commitCode_0_407 208384 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_408 : ParentRangeMatches Artifact.commitCode_0_408 208896 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_409 : ParentRangeMatches Artifact.commitCode_0_409 209408 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_410 : ParentRangeMatches Artifact.commitCode_0_410 209920 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_411 : ParentRangeMatches Artifact.commitCode_0_411 210432 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_412 : ParentRangeMatches Artifact.commitCode_0_412 210944 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_413 : ParentRangeMatches Artifact.commitCode_0_413 211456 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_414 : ParentRangeMatches Artifact.commitCode_0_414 211968 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_415 : ParentRangeMatches Artifact.commitCode_0_415 212480 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_416 : ParentRangeMatches Artifact.commitCode_0_416 212992 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_417 : ParentRangeMatches Artifact.commitCode_0_417 213504 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_418 : ParentRangeMatches Artifact.commitCode_0_418 214016 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_419 : ParentRangeMatches Artifact.commitCode_0_419 214528 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_420 : ParentRangeMatches Artifact.commitCode_0_420 215040 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_421 : ParentRangeMatches Artifact.commitCode_0_421 215552 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_422 : ParentRangeMatches Artifact.commitCode_0_422 216064 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_423 : ParentRangeMatches Artifact.commitCode_0_423 216576 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_424 : ParentRangeMatches Artifact.commitCode_0_424 217088 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_425 : ParentRangeMatches Artifact.commitCode_0_425 217600 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_426 : ParentRangeMatches Artifact.commitCode_0_426 218112 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_427 : ParentRangeMatches Artifact.commitCode_0_427 218624 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_428 : ParentRangeMatches Artifact.commitCode_0_428 219136 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_429 : ParentRangeMatches Artifact.commitCode_0_429 219648 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_430 : ParentRangeMatches Artifact.commitCode_0_430 220160 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_431 : ParentRangeMatches Artifact.commitCode_0_431 220672 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_432 : ParentRangeMatches Artifact.commitCode_0_432 221184 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_433 : ParentRangeMatches Artifact.commitCode_0_433 221696 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_434 : ParentRangeMatches Artifact.commitCode_0_434 222208 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_435 : ParentRangeMatches Artifact.commitCode_0_435 222720 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_436 : ParentRangeMatches Artifact.commitCode_0_436 223232 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_437 : ParentRangeMatches Artifact.commitCode_0_437 223744 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_438 : ParentRangeMatches Artifact.commitCode_0_438 224256 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_439 : ParentRangeMatches Artifact.commitCode_0_439 224768 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_440 : ParentRangeMatches Artifact.commitCode_0_440 225280 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_441 : ParentRangeMatches Artifact.commitCode_0_441 225792 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_442 : ParentRangeMatches Artifact.commitCode_0_442 226304 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_443 : ParentRangeMatches Artifact.commitCode_0_443 226816 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_444 : ParentRangeMatches Artifact.commitCode_0_444 227328 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_445 : ParentRangeMatches Artifact.commitCode_0_445 227840 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_446 : ParentRangeMatches Artifact.commitCode_0_446 228352 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_447 : ParentRangeMatches Artifact.commitCode_0_447 228864 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_448 : ParentRangeMatches Artifact.commitCode_0_448 229376 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_449 : ParentRangeMatches Artifact.commitCode_0_449 229888 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_450 : ParentRangeMatches Artifact.commitCode_0_450 230400 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_451 : ParentRangeMatches Artifact.commitCode_0_451 230912 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_452 : ParentRangeMatches Artifact.commitCode_0_452 231424 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_453 : ParentRangeMatches Artifact.commitCode_0_453 231936 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_454 : ParentRangeMatches Artifact.commitCode_0_454 232448 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_455 : ParentRangeMatches Artifact.commitCode_0_455 232960 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_456 : ParentRangeMatches Artifact.commitCode_0_456 233472 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_457 : ParentRangeMatches Artifact.commitCode_0_457 233984 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_458 : ParentRangeMatches Artifact.commitCode_0_458 234496 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_459 : ParentRangeMatches Artifact.commitCode_0_459 235008 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_460 : ParentRangeMatches Artifact.commitCode_0_460 235520 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_461 : ParentRangeMatches Artifact.commitCode_0_461 236032 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_462 : ParentRangeMatches Artifact.commitCode_0_462 236544 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_463 : ParentRangeMatches Artifact.commitCode_0_463 237056 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_464 : ParentRangeMatches Artifact.commitCode_0_464 237568 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_465 : ParentRangeMatches Artifact.commitCode_0_465 238080 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_466 : ParentRangeMatches Artifact.commitCode_0_466 238592 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_467 : ParentRangeMatches Artifact.commitCode_0_467 239104 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_468 : ParentRangeMatches Artifact.commitCode_0_468 239616 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_469 : ParentRangeMatches Artifact.commitCode_0_469 240128 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_470 : ParentRangeMatches Artifact.commitCode_0_470 240640 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_471 : ParentRangeMatches Artifact.commitCode_0_471 241152 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_472 : ParentRangeMatches Artifact.commitCode_0_472 241664 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_473 : ParentRangeMatches Artifact.commitCode_0_473 242176 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_474 : ParentRangeMatches Artifact.commitCode_0_474 242688 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_475 : ParentRangeMatches Artifact.commitCode_0_475 243200 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_476 : ParentRangeMatches Artifact.commitCode_0_476 243712 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_477 : ParentRangeMatches Artifact.commitCode_0_477 244224 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_478 : ParentRangeMatches Artifact.commitCode_0_478 244736 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_479 : ParentRangeMatches Artifact.commitCode_0_479 245248 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_480 : ParentRangeMatches Artifact.commitCode_0_480 245760 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_481 : ParentRangeMatches Artifact.commitCode_0_481 246272 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_482 : ParentRangeMatches Artifact.commitCode_0_482 246784 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_483 : ParentRangeMatches Artifact.commitCode_0_483 247296 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_484 : ParentRangeMatches Artifact.commitCode_0_484 247808 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_485 : ParentRangeMatches Artifact.commitCode_0_485 248320 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_486 : ParentRangeMatches Artifact.commitCode_0_486 248832 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_487 : ParentRangeMatches Artifact.commitCode_0_487 249344 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_488 : ParentRangeMatches Artifact.commitCode_0_488 249856 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_489 : ParentRangeMatches Artifact.commitCode_0_489 250368 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_490 : ParentRangeMatches Artifact.commitCode_0_490 250880 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_491 : ParentRangeMatches Artifact.commitCode_0_491 251392 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_492 : ParentRangeMatches Artifact.commitCode_0_492 251904 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_493 : ParentRangeMatches Artifact.commitCode_0_493 252416 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_494 : ParentRangeMatches Artifact.commitCode_0_494 252928 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_495 : ParentRangeMatches Artifact.commitCode_0_495 253440 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_496 : ParentRangeMatches Artifact.commitCode_0_496 253952 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_497 : ParentRangeMatches Artifact.commitCode_0_497 254464 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_498 : ParentRangeMatches Artifact.commitCode_0_498 254976 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_499 : ParentRangeMatches Artifact.commitCode_0_499 255488 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_500 : ParentRangeMatches Artifact.commitCode_0_500 256000 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_501 : ParentRangeMatches Artifact.commitCode_0_501 256512 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_502 : ParentRangeMatches Artifact.commitCode_0_502 257024 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_503 : ParentRangeMatches Artifact.commitCode_0_503 257536 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_504 : ParentRangeMatches Artifact.commitCode_0_504 258048 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_505 : ParentRangeMatches Artifact.commitCode_0_505 258560 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_506 : ParentRangeMatches Artifact.commitCode_0_506 259072 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_507 : ParentRangeMatches Artifact.commitCode_0_507 259584 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_508 : ParentRangeMatches Artifact.commitCode_0_508 260096 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_509 : ParentRangeMatches Artifact.commitCode_0_509 260608 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_510 : ParentRangeMatches Artifact.commitCode_0_510 261120 := by
  exact packed_window _ _ 2 (by decide) (by decide) (by decide) packed_periodic_2

private theorem parent_window_511 : ParentRangeMatches Artifact.commitCode_0_511 261632 := by
  unfold ParentRangeMatches expectedWord fullWord packedWord rootWords
  decide +kernel

private theorem parent_packed_matches : ParentRangeMatches Artifact.commitCode 0 := by
  exact (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_before _ _ (by decide)) (parent_range_join _ _ _ (parent_range_before _ _ (by decide)) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_before _ _ (by decide)) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_104 parent_window_105) (parent_range_join _ _ _ parent_window_106 parent_window_107)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_108 parent_window_109) (parent_range_join _ _ _ parent_window_110 parent_window_111)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_112 parent_window_113) (parent_range_join _ _ _ parent_window_114 parent_window_115)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_116 parent_window_117) (parent_range_join _ _ _ parent_window_118 parent_window_119))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_120 parent_window_121) (parent_range_join _ _ _ parent_window_122 parent_window_123)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_124 parent_window_125) (parent_range_join _ _ _ parent_window_126 parent_window_127))))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_128 parent_window_129) (parent_range_join _ _ _ parent_window_130 parent_window_131)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_132 parent_window_133) (parent_range_join _ _ _ parent_window_134 parent_window_135))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_136 parent_window_137) (parent_range_join _ _ _ parent_window_138 parent_window_139)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_140 parent_window_141) (parent_range_join _ _ _ parent_window_142 parent_window_143)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_144 parent_window_145) (parent_range_join _ _ _ parent_window_146 parent_window_147)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_148 parent_window_149) (parent_range_join _ _ _ parent_window_150 parent_window_151))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_152 parent_window_153) (parent_range_join _ _ _ parent_window_154 parent_window_155)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_156 parent_window_157) (parent_range_join _ _ _ parent_window_158 parent_window_159))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_160 parent_window_161) (parent_range_join _ _ _ parent_window_162 parent_window_163)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_164 parent_window_165) (parent_range_join _ _ _ parent_window_166 parent_window_167))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_168 parent_window_169) (parent_range_join _ _ _ parent_window_170 parent_window_171)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_172 parent_window_173) (parent_range_join _ _ _ parent_window_174 parent_window_175)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_176 parent_window_177) (parent_range_join _ _ _ parent_window_178 parent_window_179)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_180 parent_window_181) (parent_range_join _ _ _ parent_window_182 parent_window_183))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_184 parent_window_185) (parent_range_join _ _ _ parent_window_186 parent_window_187)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_188 parent_window_189) (parent_range_join _ _ _ parent_window_190 parent_window_191)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_192 parent_window_193) (parent_range_join _ _ _ parent_window_194 parent_window_195)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_196 parent_window_197) (parent_range_join _ _ _ parent_window_198 parent_window_199))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_200 parent_window_201) (parent_range_join _ _ _ parent_window_202 parent_window_203)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_204 parent_window_205) (parent_range_join _ _ _ parent_window_206 parent_window_207)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_208 parent_window_209) (parent_range_join _ _ _ parent_window_210 parent_window_211)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_212 parent_window_213) (parent_range_join _ _ _ parent_window_214 parent_window_215))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_216 parent_window_217) (parent_range_join _ _ _ parent_window_218 parent_window_219)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_220 parent_window_221) (parent_range_join _ _ _ parent_window_222 parent_window_223))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_224 parent_window_225) (parent_range_join _ _ _ parent_window_226 parent_window_227)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_228 parent_window_229) (parent_range_join _ _ _ parent_window_230 parent_window_231))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_232 parent_window_233) (parent_range_join _ _ _ parent_window_234 parent_window_235)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_236 parent_window_237) (parent_range_join _ _ _ parent_window_238 parent_window_239)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_240 parent_window_241) (parent_range_join _ _ _ parent_window_242 parent_window_243)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_244 parent_window_245) (parent_range_join _ _ _ parent_window_246 parent_window_247))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_248 parent_window_249) (parent_range_join _ _ _ parent_window_250 parent_window_251)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_252 parent_window_253) (parent_range_join _ _ _ parent_window_254 parent_window_255)))))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_256 parent_window_257) (parent_range_join _ _ _ parent_window_258 parent_window_259)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_260 parent_window_261) (parent_range_join _ _ _ parent_window_262 parent_window_263))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_264 parent_window_265) (parent_range_join _ _ _ parent_window_266 parent_window_267)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_268 parent_window_269) (parent_range_join _ _ _ parent_window_270 parent_window_271)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_272 parent_window_273) (parent_range_join _ _ _ parent_window_274 parent_window_275)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_276 parent_window_277) (parent_range_join _ _ _ parent_window_278 parent_window_279))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_280 parent_window_281) (parent_range_join _ _ _ parent_window_282 parent_window_283)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_284 parent_window_285) (parent_range_join _ _ _ parent_window_286 parent_window_287))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_288 parent_window_289) (parent_range_join _ _ _ parent_window_290 parent_window_291)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_292 parent_window_293) (parent_range_join _ _ _ parent_window_294 parent_window_295))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_296 parent_window_297) (parent_range_join _ _ _ parent_window_298 parent_window_299)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_300 parent_window_301) (parent_range_join _ _ _ parent_window_302 parent_window_303)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_304 parent_window_305) (parent_range_join _ _ _ parent_window_306 parent_window_307)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_308 parent_window_309) (parent_range_join _ _ _ parent_window_310 parent_window_311))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_312 parent_window_313) (parent_range_join _ _ _ parent_window_314 parent_window_315)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_316 parent_window_317) (parent_range_join _ _ _ parent_window_318 parent_window_319)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_320 parent_window_321) (parent_range_join _ _ _ parent_window_322 parent_window_323)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_324 parent_window_325) (parent_range_join _ _ _ parent_window_326 parent_window_327))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_328 parent_window_329) (parent_range_join _ _ _ parent_window_330 parent_window_331)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_332 parent_window_333) (parent_range_join _ _ _ parent_window_334 parent_window_335)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_336 parent_window_337) (parent_range_join _ _ _ parent_window_338 parent_window_339)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_340 parent_window_341) (parent_range_join _ _ _ parent_window_342 parent_window_343))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_344 parent_window_345) (parent_range_join _ _ _ parent_window_346 parent_window_347)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_348 parent_window_349) (parent_range_join _ _ _ parent_window_350 parent_window_351))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_352 parent_window_353) (parent_range_join _ _ _ parent_window_354 parent_window_355)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_356 parent_window_357) (parent_range_join _ _ _ parent_window_358 parent_window_359))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_360 parent_window_361) (parent_range_join _ _ _ parent_window_362 parent_window_363)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_364 parent_window_365) (parent_range_join _ _ _ parent_window_366 parent_window_367)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_368 parent_window_369) (parent_range_join _ _ _ parent_window_370 parent_window_371)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_372 parent_window_373) (parent_range_join _ _ _ parent_window_374 parent_window_375))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_376 parent_window_377) (parent_range_join _ _ _ parent_window_378 parent_window_379)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_380 parent_window_381) (parent_range_join _ _ _ parent_window_382 parent_window_383))))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_384 parent_window_385) (parent_range_join _ _ _ parent_window_386 parent_window_387)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_388 parent_window_389) (parent_range_join _ _ _ parent_window_390 parent_window_391))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_392 parent_window_393) (parent_range_join _ _ _ parent_window_394 parent_window_395)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_396 parent_window_397) (parent_range_join _ _ _ parent_window_398 parent_window_399)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_400 parent_window_401) (parent_range_join _ _ _ parent_window_402 parent_window_403)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_404 parent_window_405) (parent_range_join _ _ _ parent_window_406 parent_window_407))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_408 parent_window_409) (parent_range_join _ _ _ parent_window_410 parent_window_411)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_412 parent_window_413) (parent_range_join _ _ _ parent_window_414 parent_window_415))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_416 parent_window_417) (parent_range_join _ _ _ parent_window_418 parent_window_419)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_420 parent_window_421) (parent_range_join _ _ _ parent_window_422 parent_window_423))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_424 parent_window_425) (parent_range_join _ _ _ parent_window_426 parent_window_427)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_428 parent_window_429) (parent_range_join _ _ _ parent_window_430 parent_window_431)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_432 parent_window_433) (parent_range_join _ _ _ parent_window_434 parent_window_435)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_436 parent_window_437) (parent_range_join _ _ _ parent_window_438 parent_window_439))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_440 parent_window_441) (parent_range_join _ _ _ parent_window_442 parent_window_443)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_444 parent_window_445) (parent_range_join _ _ _ parent_window_446 parent_window_447)))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_448 parent_window_449) (parent_range_join _ _ _ parent_window_450 parent_window_451)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_452 parent_window_453) (parent_range_join _ _ _ parent_window_454 parent_window_455))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_456 parent_window_457) (parent_range_join _ _ _ parent_window_458 parent_window_459)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_460 parent_window_461) (parent_range_join _ _ _ parent_window_462 parent_window_463)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_464 parent_window_465) (parent_range_join _ _ _ parent_window_466 parent_window_467)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_468 parent_window_469) (parent_range_join _ _ _ parent_window_470 parent_window_471))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_472 parent_window_473) (parent_range_join _ _ _ parent_window_474 parent_window_475)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_476 parent_window_477) (parent_range_join _ _ _ parent_window_478 parent_window_479))))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_480 parent_window_481) (parent_range_join _ _ _ parent_window_482 parent_window_483)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_484 parent_window_485) (parent_range_join _ _ _ parent_window_486 parent_window_487))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_488 parent_window_489) (parent_range_join _ _ _ parent_window_490 parent_window_491)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_492 parent_window_493) (parent_range_join _ _ _ parent_window_494 parent_window_495)))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_496 parent_window_497) (parent_range_join _ _ _ parent_window_498 parent_window_499)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_500 parent_window_501) (parent_range_join _ _ _ parent_window_502 parent_window_503))) (parent_range_join _ _ _ (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_504 parent_window_505) (parent_range_join _ _ _ parent_window_506 parent_window_507)) (parent_range_join _ _ _ (parent_range_join _ _ _ parent_window_508 parent_window_509) (parent_range_join _ _ _ parent_window_510 parent_window_511)))))))))

def packedWideCommitImage : Image :=
  ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩

theorem packed_manifest_image : packedWideCommitImage = Artifact.submission.image .commit := by
  simp only [packedWideCommitImage,Artifact.submission]

private theorem wide_commit_code :
    packedWideCommitImage.code = ArtifactEncoding.decode 32 Artifact.commitCode := by
  simp only [packedWideCommitImage]

theorem packed_index_fetch (state : MachineState) (index : Nat)
    (point : state.pc=BitVec.ofNat 64 (4096+4*index))
    (lower : (53369 : Nat) ≤ index) (upper : index < 262071) :
    fetch packedWideCommitImage state=decodeInstruction (expectedWord index) := by
  have pc : state.pc.toNat=4096+4*index := by
    rw [point,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inPacked : index<262071 := by omega
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




private theorem full_parent_opcode (state : MachineState) (slot : Nat)
    (bounded : slot<32768) (part : Fin 3)
    (pc : state.pc=wideParentPC 217580 slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (fullWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(53371+3*slot+part.val)) := by
    rw [pc,wideParentPC]
    change BitVec.ofNat 64 217580+BitVec.ofNat 64 (12*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (53371+3*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,ite_eq_left (by omega)]
  simp only [fullWord]
  have phase : ((53371+3*slot+part.val)-53371)%3=part.val%3 := by omega
  rw [phase]

theorem hybrid_full_words (slot : Nat) (bounded : slot<32768) :
    ParentWordsAtP packedWideCommitImage (wideParentPC 217580 slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · exact full_parent_opcode state slot bounded 0  (by simpa using pc)
  · exact full_parent_opcode state slot bounded 1 pc
  · exact full_parent_opcode state slot bounded 2 pc

private theorem packed_parent_opcode (state : MachineState) (slot : Nat)
    (bounded : slot<27595) (part : Fin 4)
    (pc : state.pc=packedParentPC 610808 slot+BitVec.ofNat 64 (4*part.val)) :
    fetch packedWideCommitImage state=decodeInstruction (packedWord part.val) := by
  have inside := part.isLt
  have address : state.pc=BitVec.ofNat 64 (4096+4*(151678+4*slot+part.val)) := by
    rw [pc,packedParentPC]
    change BitVec.ofNat 64 610808+BitVec.ofNat 64 (16*slot)+BitVec.ofNat 64 (4*part.val)=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rw [packed_index_fetch state (151678+4*slot+part.val) address (by omega) (by omega)]
  rw [expectedWord,ite_eq_right (by omega),ite_eq_left (by omega)]
  simp only [packedWord]
  have phase : ((151678+4*slot+part.val)-151678)%4=part.val%4 := by omega
  rw [phase]

theorem packed_parent_words (slot : Nat) (bounded : slot<27595) :
    PackedParentWordsAt packedWideCommitImage (packedParentPC 610808 slot) := by
  refine ⟨fun state pc => ?_,fun state pc => ?_,fun state pc => ?_,fun state pc => ?_⟩
  · exact packed_parent_opcode state slot bounded 0  (by simpa using pc)
  · exact packed_parent_opcode state slot bounded 1 pc
  · exact packed_parent_opcode state slot bounded 2 pc
  · exact packed_parent_opcode state slot bounded 3 pc

theorem hybrid_threshold_lui (state : MachineState) (pc : state.pc=217572) :
    fetch packedWideCommitImage state=some (.base (.LUI .x18 65536)) :=
  packed_index_fetch state 53369 pc (by decide) (by decide)

theorem hybrid_threshold_add (state : MachineState) (pc : state.pc=217576) :
    fetch packedWideCommitImage state=some (.base (.ADD .x18 .x18 .x8)) :=
  packed_index_fetch state 53370 pc (by decide) (by decide)

theorem hybrid_lower_branch (state : MachineState) (pc : state.pc=610796) :
    fetch packedWideCommitImage state=some (.base (.BEQ .x12 .x18 8)) :=
  packed_index_fetch state 151675 pc (by decide) (by decide)

theorem hybrid_lower_back (state : MachineState) (pc : state.pc=610800) :
    fetch packedWideCommitImage state=some (.base (.JAL .x0 1703932)) :=
  packed_index_fetch state 151676 pc (by decide) (by decide)

theorem hybrid_skip (state : MachineState) (pc : state.pc=610804) :
    fetch packedWideCommitImage state=some (.base (.JAL .x0 1490528)) :=
  packed_index_fetch state 151677 pc (by decide) (by decide)

def fixedWideParentControl : PackedParentControl packedWideCommitImage 610808 27595 where
  backOffset := 1655628
  backTarget := by decide
  branch state pc := packed_index_fetch state 262058 pc (by decide) (by decide)
  jump state pc := packed_index_fetch state 262059 pc (by decide) (by decide)

private theorem wide_root_fetch (state : MachineState) (i : Nat) (inside : i < 11)
    (pc : state.pc=BitVec.ofNat 64 (1052336+4*i)) :
    fetch packedWideCommitImage state=some (.base ((rootOps[i]?).getD .ECALL)) := by
  have address : state.pc=BitVec.ofNat 64 (4096+4*(262060+i)) := by
    rw [pc]
    congr 1
    omega
  rw [packed_index_fetch state (262060+i) address (by omega) (by omega)]
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

theorem execute_packed_root (state : MachineState) (pc : state.pc=1052336)
    (heap : state.getReg .x9=4294971424) (out : state.getReg .x8=4294971392) (fuel : Nat) :
    execute packedWideCommitImage (11+fuel) state true = pure ⟨.success,rootPrefix state 10,11,0⟩ := by
  have prefixPC (i : Nat) (inside : i<11) :
      (rootPrefix state i).pc=BitVec.ofNat 64 (1052336+4*i) := by
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

end TwoPermutationPrototype.RV64

