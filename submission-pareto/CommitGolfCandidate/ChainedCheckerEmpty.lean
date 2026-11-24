import CommitGolfCandidate.ChainedCheckerArtifact

/-! The delivered zero-position, zero-length path performs no buffer access. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne

def checkerEmptyIndices : List Nat :=
  [0,1,2,3,4,5,7,8,9,11,12,13,14,15,17,2359,2360,2361,3009,3010]

def checkerEmptyOps : List Instr :=
  [.SLLI .x2 .x16 9,.SLLI .x3 .x16 5,.SUB .x2 .x2 .x3,
   .SLLI .x3 .x16 1,.ADD .x2 .x2 .x3,.BGEU .x17 .x2 8,
   .ADDI .x3 .x2 1888,.ADDI .x3 .x3 1888,.BGEU .x3 .x17 8,
   .ADDI .x12 .x0 1,.SLLI .x12 .x12 33,.ADD .x12 .x12 .x15,
   .BNE .x16 .x0 16,.BEQ .x17 .x0 8,.JAL .x0 9368,
   .ADDI .x15 .x12 0,.ADDI .x17 .x0 0,.BEQ .x16 .x0 2592,
   .ADDI .x5 .x0 1,.ADDI .x10 .x0 0]

@[irreducible] def checkerEmptyState (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i previous => execInstrBr previous (checkerEmptyOps.getD i .EBREAK)) n

theorem checker_empty_state_zero (s : MachineState) : checkerEmptyState 0 s=s := by
  unfold checkerEmptyState
  rfl

theorem checker_empty_state_succ (n : Nat) (s : MachineState) :
    checkerEmptyState (n+1) s=execInstrBr (checkerEmptyState n s) (checkerEmptyOps.getD n .EBREAK) := by
  unfold checkerEmptyState
  rfl

private theorem empty_instruction (i : Fin 20) :
    chainedCheckerOps.getD (checkerEmptyIndices.getD i.val 0) .EBREAK=
      checkerEmptyOps.getD i.val .EBREAK := by
  fin_cases i <;> rfl

private theorem empty_index_small (i : Fin 20) : checkerEmptyIndices.getD i.val 0<3012 := by
  fin_cases i <;> decide +kernel

@[local simp] private theorem empty_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem empty_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem empty_pc_reg (s : MachineState) (r : Reg) (value : Word) :
    (s.setReg r value).pc=s.pc := by cases r <;> rfl
@[local simp] private theorem empty_reg_pc (s : MachineState) (pc : Word) (r : Reg) :
    (s.setPC pc).getReg r=s.getReg r := by cases r <;> rfl

theorem checker_empty_pc (s : MachineState) (n : Nat) (small : n≤20) (pc : s.pc=4096)
    (empty : s.getReg .x16=0#64) (length : s.getReg .x17=0#64) :
    (checkerEmptyState n s).pc=4096+BitVec.ofNat 64 (4*(checkerEmptyIndices.getD n 3011)) := by
  interval_cases n <;>
    simp [checker_empty_state_zero,checker_empty_state_succ,checkerEmptyOps,checkerEmptyIndices,
      execInstrBr,signExtend12,signExtend13,signExtend21,pc,empty,length]

private theorem empty_project_memory (before after : MachineState) (target query : Word)
    (same : after=before.setPC target) : after.getMem query=before.getMem query :=
  (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC

private theorem empty_branch_memory (s : MachineState) (condition : Prop) [Decidable condition]
    (left right query : Word) :
    (if condition then s.setPC left else s.setPC right).getMem query=s.getMem query := by
  by_cases branch : condition
  · exact empty_project_memory s _ left query (ite_eq_left branch)
  · exact empty_project_memory s _ right query (ite_eq_right branch)

private theorem empty_bgeu_memory (s : MachineState) (left right : Reg) (offset : BitVec 13) (query : Word) :
    (execInstrBr s (.BGEU left right offset)).getMem query=s.getMem query :=
  empty_branch_memory s _ _ _ query

private theorem empty_beq_memory (s : MachineState) (left right : Reg) (offset : BitVec 13) (query : Word) :
    (execInstrBr s (.BEQ left right offset)).getMem query=s.getMem query :=
  empty_branch_memory s _ _ _ query

private theorem empty_bne_memory (s : MachineState) (left right : Reg) (offset : BitVec 13) (query : Word) :
    (execInstrBr s (.BNE left right offset)).getMem query=s.getMem query :=
  empty_branch_memory s _ _ _ query

private theorem empty_jump_memory (s : MachineState) (offset : BitVec 21) (query : Word) :
    (execInstrBr s (.JAL .x0 offset)).getMem query=s.getMem query := rfl

private theorem empty_step_memory (s : MachineState) (i : Fin 20) (query : Word) :
    (execInstrBr s (checkerEmptyOps.getD i.val .EBREAK)).getMem query=s.getMem query := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact empty_bgeu_memory s _ _ _ query
  · rfl
  · rfl
  · exact empty_bgeu_memory s _ _ _ query
  · rfl
  · rfl
  · rfl
  · exact empty_bne_memory s _ _ _ query
  · exact empty_beq_memory s _ _ _ query
  · exact empty_jump_memory s _ query
  · rfl
  · rfl
  · exact empty_beq_memory s _ _ _ query
  · rfl
  · rfl

theorem checker_empty_memory (s : MachineState) (n : Nat) (small : n≤20) (query : Word) :
    (checkerEmptyState n s).getMem query=s.getMem query := by
  induction n with
  | zero => rw [checker_empty_state_zero]
  | succ n ih => rw [checker_empty_state_succ,empty_step_memory _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_empty_byte (s : MachineState) (n : Nat) (small : n≤20) (query : Word) :
    (checkerEmptyState n s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_empty_memory s n small]

theorem checker_empty_execution (s : MachineState) (pc : s.pc=4096)
    (empty : s.getReg .x16=0#64) (length : s.getReg .x17=0#64) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (21+fuel) s coins=pure ⟨.success,checkerEmptyState 20 s,21,0⟩ := by
  have block (rest : Nat) : execute chainedCheckerImage (20+rest) s coins=
      (do let result ← execute chainedCheckerImage rest (checkerEmptyState 20 s) coins
          return result.charge 20 0) := by
    conv_lhs => rw [←checker_empty_state_zero s]
    apply execute_unit_steps (states := fun n => checkerEmptyState n s)
    intro index inside
    refine ⟨.base (checkerEmptyOps.getD index .EBREAK),?_,?_,?_⟩
    · rw [←empty_instruction ⟨index,inside⟩]
      apply chained_checker_ops_at _ (by rw [chained_checker_ops_length]; exact empty_index_small ⟨index,inside⟩)
      have differentDefault : checkerEmptyIndices.getD index 3011=checkerEmptyIndices.getD index 0 := by
        have bounded : index<checkerEmptyIndices.length := by change index<20; exact inside
        simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bounded,Option.getD_some]
      rw [←differentDefault]
      exact checker_empty_pc s index (by omega) pc empty length
    · rw [checker_empty_state_succ]
      interval_cases index <;> rfl
    · interval_cases index <;> rfl
  have fetched : fetch chainedCheckerImage (checkerEmptyState 20 s)=some (.base .ECALL) :=
    chained_checker_ops_at 3011 (by rw [chained_checker_ops_length]; decide) _
      (checker_empty_pc s 20 (by decide) pc empty length)
  have halt : (checkerEmptyState 20 s).getReg .x5=1 := by
    rw [checker_empty_state_succ]
    change (checkerEmptyState 19 s).getReg .x5=1
    rw [checker_empty_state_succ]
    rfl
  have success : (checkerEmptyState 20 s).getReg .x10=0 := by
    rw [checker_empty_state_succ]
    rfl
  rw [show 21+fuel=20+(fuel+1) by omega,block]
  unfold execute
  rw [fetched]
  simp only [halt,success]
  rfl

theorem artifact_checking_empty (s : MachineState) (pc : s.pc=4096)
    (empty : s.getReg .x16=0#64) (length : s.getReg .x17=0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (21+fuel) s coins=
      pure ⟨.success,checkerEmptyState 20 s,21,0⟩ := by
  rw [checking_manifest_image]
  exact checker_empty_execution s pc empty length fuel coins

end CommitGolfCandidate.Chained.Native
