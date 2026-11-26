import CommitGolfCandidate.ChainedNodeStore

/-! The two descending-cursor instructions, separately from the conditional branch. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
attribute [local irreducible] execute

def cursorOps : List Instr := [.ADDI .x6 .x6 4032,.ADDI .x7 .x7 4064]
def cursorPrefix (s : MachineState) (count : Nat) : MachineState :=
  (cursorOps.take count).foldl execInstrBr s
def cursorPC (h : Height) : Word := 184628+BitVec.ofNat 64 (4*(21+20*h.val))
def branchPC (h : Height) : Word := 184628+BitVec.ofNat 64 (4*(23+20*h.val))
def shiftPC (h : Height) : Word := 184628+BitVec.ofNat 64 (4*(24+20*h.val))

theorem cursor_pc_eq (h : Height) : cursorPC h = copyPC h+32 := by fin_cases h <;> rfl

theorem cursor_prefix_pc (s : MachineState) (count : Nat) (small : count ≤ 2) :
    (cursorPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [cursorPrefix,cursorOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem cursor_source (s : MachineState) : (cursorPrefix s 2).getReg .x6 = s.getReg .x6-64 := by
  change s.getReg .x6+signExtend12 4032 = _
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem cursor_target (s : MachineState) : (cursorPrefix s 2).getReg .x7 = s.getReg .x7-32 := by
  change s.getReg .x7+signExtend12 4064 = _
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem cursor_register (s : MachineState) (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
    (cursorPrefix s 2).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (not6 rfl).elim | exact (not7 rfl).elim | rfl

theorem cursor_memory (s : MachineState) (query : Word) :
    (cursorPrefix s 2).getMem query = s.getMem query := by rfl

private theorem cursor_fetch (h : Height) (i : Fin 2) (s : MachineState)
    (pc : s.pc = 184628+BitVec.ofNat 64 (4*(21+20*h.val+i.val))) :
    fetch chainedCommitImage s = some (.base ((cursorOps[i.val]?).getD .EBREAK)) := by
  have opEq : chainedParentOp (21+20*h.val+i.val) = (cursorOps[i.val]?).getD .EBREAK := by
    fin_cases h <;> fin_cases i <;> rfl
  simpa only [opEq] using chained_parent_at ⟨21+20*h.val+i.val,by have := h.isLt; have := i.isLt; omega⟩ s pc

theorem cursor_execution (s : MachineState) (h : Height) (pc : s.pc = cursorPC h)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (2+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (cursorPrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := cursorPrefix s)
  intro i inside
  refine ⟨.base ((cursorOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply cursor_fetch h ⟨i,inside⟩
    rw [cursor_prefix_pc s i (by omega),pc]
    unfold cursorPC
    rw [BitVec.add_assoc,←BitVec.ofNat_add,
      show 4*(21+20*h.val)+4*i = 4*(21+20*h.val+i) by omega]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cursor_branch_pc (s : MachineState) (h : Height) (pc : s.pc = cursorPC h) :
    (cursorPrefix s 2).pc = branchPC h := by
  rw [cursor_prefix_pc s 2 (by decide),pc]
  fin_cases h <;> rfl

end CommitGolfCandidate.Chained.Native
