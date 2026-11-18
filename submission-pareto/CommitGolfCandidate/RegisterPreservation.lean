import CommitGolfCandidate.Execution
import CommitGolfCandidate.TwoPermutationPackedOpeningImage

/-! A register that no instruction of an image writes keeps its value through every
possible execution of that image, for all oracle replies and private coins. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Whether an instruction may change register `r`: its destination register for
register-writing instructions; never for stores, branches, `FENCE`, `ECALL`, `EBREAK`;
conservatively always for `CSRS`. -/
def writesReg : Instruction → Reg → Bool
  | .word _ rd _ _, r => rd == r
  | .sraiw rd _ _, r => rd == r
  | .base i, r =>
    match i with
    | .ADD rd _ _ | .SUB rd _ _ | .SLL rd _ _ | .SRL rd _ _ | .SRA rd _ _
    | .AND rd _ _ | .OR rd _ _ | .XOR rd _ _ | .SLT rd _ _ | .SLTU rd _ _ => rd == r
    | .ADDI rd _ _ | .ANDI rd _ _ | .ORI rd _ _ | .XORI rd _ _ | .SLTI rd _ _
    | .SLTIU rd _ _ | .SLLI rd _ _ | .SRLI rd _ _ | .SRAI rd _ _ => rd == r
    | .LUI rd _ | .AUIPC rd _ => rd == r
    | .LD rd _ _ | .LW rd _ _ | .LWU rd _ _ | .LB rd _ _ | .LH rd _ _
    | .LBU rd _ _ | .LHU rd _ _ => rd == r
    | .SD .. | .SW .. | .SB .. | .SH .. => false
    | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => false
    | .JAL rd _ | .JALR rd _ _ => rd == r
    | .MV rd _ | .LI rd _ => rd == r
    | .NOP => false
    | .ADDIW rd _ _ | .SUBW rd _ _ | .SRLW rd _ _ | .SLLIW rd _ _ | .SRLIW rd _ _ => rd == r
    | .ECALL | .FENCE | .EBREAK => false
    | .MUL rd _ _ | .MULH rd _ _ | .MULHSU rd _ _ | .MULHU rd _ _
    | .DIV rd _ _ | .DIVU rd _ _ | .REM rd _ _ | .REMU rd _ _ => rd == r
    | .CSRS .. => true

private theorem getReg_setReg_of_beq (s : MachineState) (rd r : Reg) (v : Word)
    (h : (rd == r) = false) : (s.setReg rd v).getReg r = s.getReg r :=
  MachineState.getReg_setReg_ne s rd r v (by simpa using h)

/-- One ordinary instruction leaves every register it does not write unchanged. -/
theorem ordinary_step_keeps (s n : MachineState) (i : Instruction) (r : Reg)
    (step : ordinaryStep s i = some n) (h : writesReg i r = false) :
    n.getReg r = s.getReg r := by
  cases i with
  | word op rd rs1 rs2 =>
    simp only [ordinaryStep, Option.some.injEq] at step
    subst n
    simp only [writesReg] at h
    rw [MachineState.getReg_setPC, getReg_setReg_of_beq _ _ _ _ h]
  | sraiw rd rs shift =>
    simp only [ordinaryStep, Option.some.injEq] at step
    subst n
    simp only [writesReg] at h
    rw [MachineState.getReg_setPC, getReg_setReg_of_beq _ _ _ _ h]
  | base instruction =>
    cases instruction <;>
      simp only [ordinaryStep, reduceCtorEq, Option.ite_none_right_eq_some,
        Option.some.injEq] at step <;>
      simp only [writesReg] at h <;>
      obtain ⟨_, rfl⟩ := step <;>
      simp only [execInstrBr] <;>
      (try split) <;>
      simp only [MachineState.getReg_setPC] <;>
      first
        | rfl
        | exact getReg_setReg_of_beq _ _ _ _ h

/-- An image none of whose decodable words writes `r`. -/
def imageAvoids (image : Image) (r : Reg) : Bool :=
  image.code.all (fun w => match decodeInstruction w with
    | some i => !writesReg i r
    | none => true)

theorem fetch_avoids (image : Image) (r : Reg) (h : imageAvoids image r = true)
    (s : MachineState) (i : Instruction) (f : fetch image s = some i) :
    writesReg i r = false := by
  unfold fetch at f
  split at f
  · split at f
    · rename_i word hword
      have hmem : word ∈ image.code := List.mem_of_getElem? hword
      have := List.all_eq_true.mp h word hmem
      rw [f] at this
      simpa using this
    · exact absurd f (by simp)
  · exact absurd f (by simp)

/-- Every possible execution of an image that never writes `r` preserves `r`. -/
theorem execute_keeps_register (image : Image) (r : Reg) (h : imageAvoids image r = true) :
    ∀ (steps : Nat) (s : MachineState) (coins : Bool),
      ∀ result ∈ support (execute image steps s coins), result.state.getReg r = s.getReg r := by
  intro steps
  induction steps with
  | zero =>
    intro s coins result hres
    simp only [execute, support_pure, Set.mem_singleton_iff] at hres
    subst result
    rfl
  | succ steps ih =>
    intro s coins result hres
    simp only [execute] at hres
    split at hres
    · simp only [support_pure, Set.mem_singleton_iff] at hres
      subst result
      rfl
    · split at hres
      · split at hres
        · simp only [support_pure, Set.mem_singleton_iff] at hres
          subst result
          rfl
        · rename_i input _
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
          obtain ⟨answer, _, next, hnext, rfl⟩ := hres
          rw [show (next.charge _ _).state = next.state from rfl, ih _ _ _ hnext]
          rcases input with q | q | q <;> exact writeBits_register _ _ _ _
      · split at hres
        · simp only [support_pure, Set.mem_singleton_iff] at hres
          subst result
          rfl
        · split at hres
          · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
            obtain ⟨answer, _, next, hnext, rfl⟩ := hres
            rw [show (next.charge _ _).state = next.state from rfl, ih _ _ _ hnext]
            exact writeBits_register _ _ _ _
          · simp only [support_pure, Set.mem_singleton_iff] at hres
            subst result
            rfl
    · split at hres
      · simp only [support_pure, Set.mem_singleton_iff] at hres
        subst result
        rfl
      · rename_i next stepped
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
        obtain ⟨final, hfinal, rfl⟩ := hres
        rw [show (final.charge _ _).state = final.state from rfl, ih _ _ _ hfinal]
        exact ordinary_step_keeps _ _ _ _ stepped (fetch_avoids image r h s _ (by assumption))

set_option maxRecDepth 100000 in
example : imageAvoids TwoPermutationPrototype.PackedOpening.openingImage .x16 = true := by
  decide +kernel

end CommitGolfCandidate
