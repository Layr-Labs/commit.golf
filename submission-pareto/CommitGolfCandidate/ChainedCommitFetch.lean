import CommitGolf.Artifact
import CommitGolfCandidate.ChainedCommitGeometry
import CommitGolfCandidate.ChainedContinuationEntry
import CommitGolfCandidate.ChainedFirstPackExecution

/-! Exact fetches from the changed delivered commitment, not a standalone image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

def chainedCommitImage : Image := Artifact.submission.image .commit

theorem chained_commit_code : chainedCommitImage.code = ArtifactEncoding.decode 32 Artifact.commitCode := by
  simp only [chainedCommitImage,Artifact.submission]

theorem chained_parent_manifest_word : ∀ i : Fin 550,
    Artifact.commitCode.get 32 ⟨45133+i.val,by omega⟩ = (chainedParentWords[i.val]?).getD 0 := by
  decide +kernel

theorem chained_parent_at : ChainedParentAt chainedCommitImage 184628 := by
  intro i s pc
  have numeric : s.pc.toNat = 4096+4*(45133+i.val) := by
    rw [pc]
    change (BitVec.ofNat 64 184628+BitVec.ofNat 64 (4*i.val)).toNat = _
    rw [←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    omega
  have inside : 45133+i.val < chainedCommitImage.code.length := by
    rw [chained_commit_code,ArtifactEncoding.length_decode]
    have := i.isLt
    omega
  have word : chainedCommitImage.code.getD (45133+i.val) 0 = (chainedParentWords[i.val]?).getD 0 := by
    rw [chained_commit_code,ArtifactEncoding.getD_decode _ _ _ (by have := i.isLt; omega)]
    exact chained_parent_manifest_word i
  have entry : chainedCommitImage.code[45133+i.val]? = some ((chainedParentWords[i.val]?).getD 0) := by
    rw [List.getElem?_eq_getElem inside,←List.getD_eq_getElem _ _ inside,word]
  have decoded := chained_parent_decode i
  have inWords : i.val < chainedParentWords.length := by
    rw [chained_parent_lengths.1]
    exact i.isLt
  rw [List.getElem?_eq_getElem inWords] at decoded
  rw [fetch,numeric,ite_eq_left (by omega),
    show (4096+4*(45133+i.val)-4096)/4 = 45133+i.val by omega,entry]
  simpa only [List.getElem?_eq_getElem inWords,Option.getD_some,Option.bind_some] using decoded

theorem chained_first_pack_at : FirstPackAt chainedCommitImage 186628 := by
  intro i s pc
  have opcode : chainedParentOp (500+i.val) = firstPackOp i.val := by
    fin_cases i <;> rfl
  have point : s.pc = (184628 : Word)+BitVec.ofNat 64 (4*(500+i.val)) := by
    rw [pc]
    change BitVec.ofNat 64 186628+BitVec.ofNat 64 (4*i.val) =
      BitVec.ofNat 64 184628+BitVec.ofNat 64 (4*(500+i.val))
    simp only [←BitVec.ofNat_add]
    congr 1
    omega
  simpa only [opcode] using chained_parent_at ⟨500+i.val,by have := i.isLt; omega⟩ s point

theorem chained_continuation_at : ContinuationAt chainedCommitImage 186752 := by
  intro i s pc
  have opcode : chainedParentOp (531+i.val) = continuationOp i.val := by
    fin_cases i <;> rfl
  have point : s.pc = (184628 : Word)+BitVec.ofNat 64 (4*(531+i.val)) := by
    rw [pc]
    change BitVec.ofNat 64 186752+BitVec.ofNat 64 (4*i.val) =
      BitVec.ofNat 64 184628+BitVec.ofNat 64 (4*(531+i.val))
    simp only [←BitVec.ofNat_add]
    congr 1
    omega
  simpa only [opcode] using chained_parent_at ⟨531+i.val,by have := i.isLt; omega⟩ s point

theorem chained_commit_fuel : Artifact.submission.steps .commit = 2^31 := rfl

theorem scratch_access : ∀ k : Fin 8,
    accessValid ((256 : Word)+BitVec.ofNat 64 (8*k.val)) 8 = true := by
  decide +kernel

theorem delivered_continuation_execution (remaining : Nat) (small : remaining ≤ 7)
    (s : MachineState) (args : LoopArgs s 256)
    (counter : s.getReg .x18 = BitVec.ofNat 64 remaining) (pc : s.pc = 186752)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (continuationInstructions remaining+fuel) s coins =
      (do let out ← continuationFullTrace 186752 256 remaining s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (continuationCycles remaining) remaining) :=
  continuation_entry_execution chainedCommitImage 186752 256 chained_continuation_at remaining small
    s args counter pc scratch_access fuel coins

theorem delivered_first_pack_execution (s : MachineState) (pc : s.pc = 186628)
    (buffer : s.getReg .x10 = 256)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (31+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (firstPackPrefix s 31) coins
          return result.charge 31 0) := by
  apply first_pack_execution chainedCommitImage 186628 chained_first_pack_at s pc inputs
  intro k
  rw [buffer]
  exact scratch_access k

end CommitGolfCandidate.Chained.Native
