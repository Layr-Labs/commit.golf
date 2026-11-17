import CommitGolfCandidate.Group341Schedule
import CommitGolfCandidate.Group341Encoding
import CommitGolfCandidate.ParentGroupTree
import CommitGolfCandidate.ParentSequenceSlots
import CommitGolfCandidate.OctImage

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem group341_image_entry : ParentGroupBranchFetched (submission.image .commit) 4752 8 := by
  intro state pc
  apply commit_fetch state 164 _ (by decide) pc
  rfl

private theorem group341_image_triple (block : Nat) (bounded : block<83886) :
    ParentTripleFetched (submission.image .commit) (4760+BitVec.ofNat 64 (12*block)) := by
  intro state
  refine ⟨?_,?_,?_⟩
  · intro pc
    apply commit_fetch state (166+3*block) _ (by omega)
    · rw [pc]
      change BitVec.ofNat 64 4760+BitVec.ofNat 64 (12*block)=_
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    · change (group341ImageWords[166+3*block]?).bind decodeInstruction=some (.base .ECALL)
      rw [show 166+3*block=166+3*block+0 by omega,group341_main_word block 0 bounded (by decide)]
      rfl
  · intro pc
    apply commit_fetch state (167+3*block) _ (by omega)
    · rw [pc]
      change BitVec.ofNat 64 4760+BitVec.ofNat 64 (12*block)+BitVec.ofNat 64 4=_
      rw [← BitVec.ofNat_add,← BitVec.ofNat_add]
      congr 1
      omega
    · change (group341ImageWords[167+3*block]?).bind decodeInstruction=some (.base (.ADDI .x10 .x10 4032))
      rw [show 167+3*block=166+3*block+1 by omega,group341_main_word block 1 bounded (by decide)]
      rfl
  · intro pc
    apply commit_fetch state (168+3*block) _ (by omega)
    · rw [pc]
      change BitVec.ofNat 64 4760+BitVec.ofNat 64 (12*block)+BitVec.ofNat 64 8=_
      rw [← BitVec.ofNat_add,← BitVec.ofNat_add]
      congr 1
      omega
    · change (group341ImageWords[168+3*block]?).bind decodeInstruction=some (.base (.ADDI .x12 .x12 4064))
      rw [show 168+3*block=166+3*block+2 by omega,group341_main_word block 2 bounded (by decide)]
      rfl

theorem group341_image_sequence : ParentSequenceFetched (submission.image .commit) 4760 83886 :=
  parent_sequence_slots _ _ _ group341_image_triple

theorem group341_image_branch : ParentGroupBranchFetched (submission.image .commit) 1011392 8 := by
  intro state pc
  apply commit_fetch state 251824 _ (by decide) pc
  change (group341ImageWords[251824]?).bind decodeInstruction=some (.base (.BNE .x12 .x9 8))
  rw [group341_end_word 0]
  rfl

theorem group341_image_exit : ParentGroupExitFetched (submission.image .commit) 1011396 1090168 := by
  intro state pc
  apply commit_fetch state 251825 _ (by decide) pc
  change (group341ImageWords[251825]?).bind decodeInstruction=some (.base (.JAL .x0 1090168))
  rw [show 251825=251824+1 by decide,group341_end_word 1]
  rfl

theorem group341_image_loop : ParentGroupExitFetched (submission.image .commit) 1011400 1090512 := by
  intro state pc
  apply commit_fetch state 251826 _ (by decide) pc
  change (group341ImageWords[251826]?).bind decodeInstruction=some (.base (.JAL .x0 1090512))
  rw [show 251826=251824+2 by decide,group341_end_word 2]
  rfl

theorem group341_image_plan : ParentPlan.Fetched (submission.image .commit) group341Schedule.initialPlan := by
  exact ⟨⟨fused_image_peeled,trivial⟩,fused_image_peel_branch,rfl,by decide,
    quad_image_pair,quad_image_entry_branch,rfl,by decide,
    quad_image_sequence,oct_image_first_branch,rfl,by decide,
    oct_image_sequence,group341_image_entry,rfl,by decide,trivial⟩

theorem group341_image_fetched : group341Schedule.Fetched (submission.image .commit) :=
  ⟨group341_image_plan,group341_image_sequence,group341_image_branch,group341_image_loop,group341_image_exit⟩

end CommitGolfCandidate
