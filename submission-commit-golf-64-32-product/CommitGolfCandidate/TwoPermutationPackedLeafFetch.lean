import CommitGolfCandidate.TwoPermutationPackedParentImage

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def packed_wideCodeWord (index : Nat) : BitVec 32 :=
  if inCode : index < 262071 then Artifact.commitCode.get 32 ⟨index,inCode⟩ else 0

theorem packed_wide_fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 262071) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index)=some instruction) :
    fetch packedWideCommitImage state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : packedWideCommitImage.code=ArtifactEncoding.decode 32 Artifact.commitCode := by
    simp only [packedWideCommitImage]
  have length : index<packedWideCommitImage.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : packedWideCommitImage.code[index]?=some (Artifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (Artifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [packed_wideCodeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (Artifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all

theorem packed_wide_fetch_leaf_branch (state : MachineState) (pc : state.pc=184720) :
    fetch packedWideCommitImage state=some (.base (.BEQ .x20 .x21 64)) :=
  packed_wide_fetch_decoded state 45156 (by decide) pc _ rfl

/-! The paired entry checks its setup, block and exit words in `C3PCommitFetch`. -/

end TwoPermutationPrototype.RV64
