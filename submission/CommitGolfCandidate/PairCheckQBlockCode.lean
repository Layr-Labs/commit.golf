-- Pair-heads copy of QuartetCheckBlockCode (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCheckerSteps
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.TwoPermutationOpeningBlocks

/-! Straight-line pieces of the variant-B quartet block: word 58 and the jump at word 59, the slot
setup at 367–372, the three slot heads, the proof-cursor advances, the call setup at 489, the exit at
491–493 and the restored lower-loop setup at 60–62. -/

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem q_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem q_mem_set_reg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl
@[local simp] private theorem q_mem_set_pc (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl
@[local simp] private theorem q_set_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl

def straight (code : List Instr) (s : MachineState) (n : Nat) : MachineState :=
  (code.take n).foldl execInstrBr s

def qEnterCode : List Instr := [.ADDI .x21 .x21 16, .JAL .x0 1232]
def qSlotCode : List Instr :=
  [.LUI .x10 3, .ADDI .x10 .x10 1024, .ANDI .x7 .x6 3, .XORI .x28 .x7 0, .SLLI .x28 .x28 5, .ADD .x28 .x10 .x28]
def qHeadCode (j : Nat) : List Instr := [.XORI .x28 .x7 (BitVec.ofNat 12 j), .SLLI .x28 .x28 5, .ADD .x28 .x10 .x28]
def qAdvanceCode : List Instr := [.ADDI .x21 .x21 32]
def qCallCode : List Instr := [.ADDI .x12 .x23 0]
def qExitCode : List Instr := [.SRLI .x6 .x6 2, .ADD .x6 .x6 .x20, .JAL .x0 0x1ff93c]
def qLowerCode : List Instr := [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x29 .x0 14]

/-- Word index of slot head `j` (1, 2, 3), its halfword copy, and the cursor advance after it. -/
def qHeadStart (j : Nat) : Nat := 381 + 36*(j-1)

theorem execute_q_enter (s : MachineState) (pc : s.pc = 0x10e8) :
    GroupHop s (straight qEnterCode s 2) 2 := by
  intro fuel
  apply execute_unit_steps (states := straight qEnterCode s)
  intro i inside
  refine ⟨.base (qEnterCode[i]?.getD .EBREAK), fetch_at _ (58+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [straight, qEnterCode, execInstrBr, pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_enter_post (s : MachineState) (pc : s.pc = 0x10e8) :
    let t := straight qEnterCode s 2
    t.pc = BitVec.ofNat 64 (4096+4*367) ∧ t.mem = s.mem ∧ t.getReg .x21 = s.getReg .x21 + 16 ∧
      ∀ r, r ≠ .x21 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · (simp [straight, qEnterCode, execInstrBr, pc, signExtend21]) <;> (try rfl)
  · simp [straight, qEnterCode, execInstrBr]
  · (simp [straight, qEnterCode, execInstrBr, signExtend12]) <;> (try rfl)
  · intro r a
    simp [straight, qEnterCode, execInstrBr, Ne.symm a]

theorem execute_q_slot (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*367)) :
    GroupHop s (straight qSlotCode s 6) 6 := by
  intro fuel
  apply execute_unit_steps (states := straight qSlotCode s)
  intro i inside
  refine ⟨.base (qSlotCode[i]?.getD .EBREAK), fetch_at _ (367+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> (simp [straight, qSlotCode, execInstrBr, pc]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_slot_post (s : MachineState) :
    let t := straight qSlotCode s 6
    t.pc = s.pc + 24 ∧ t.mem = s.mem ∧ t.getReg .x10 = 13312 ∧ t.getReg .x7 = s.getReg .x6 &&& 3 ∧
      t.getReg .x28 = 13312 + ((s.getReg .x6 &&& 3) ^^^ 0) <<< 5 ∧
      ∀ r, r ≠ .x10 → r ≠ .x7 → r ≠ .x28 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [straight, qSlotCode, execInstrBr, BitVec.add_assoc]
  · simp [straight, qSlotCode, execInstrBr]
  · (simp [straight, qSlotCode, execInstrBr, signExtend12]) <;> (try rfl)
  · simp [straight, qSlotCode, execInstrBr, signExtend12]
  · (simp [straight, qSlotCode, execInstrBr, signExtend12]) <;> (try rfl)
  · intro r a b c
    simp [straight, qSlotCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

theorem execute_q_head (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*qHeadStart j)) :
    GroupHop s (straight (qHeadCode j) s 3) 3 := by
  intro fuel
  apply execute_unit_steps (states := straight (qHeadCode j) s)
  intro i inside
  obtain ⟨lo, hi⟩ := valid
  refine ⟨.base ((qHeadCode j)[i]?.getD .EBREAK), fetch_at _ (qHeadStart j+i) _ (by unfold qHeadStart; omega) ?_ ?_, ?_, ?_⟩
  · interval_cases j <;> interval_cases i <;> (simp [straight, qHeadCode, execInstrBr, pc, qHeadStart]) <;> (try rfl)
  · interval_cases j <;> interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_head_post (j : Nat) (s : MachineState) :
    let t := straight (qHeadCode j) s 3
    t.pc = s.pc + 12 ∧ t.mem = s.mem ∧
      t.getReg .x28 = s.getReg .x10 + ((s.getReg .x7 ^^^ (BitVec.ofNat 12 j).signExtend 64) <<< 5) ∧
      ∀ r, r ≠ .x28 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [straight, qHeadCode, execInstrBr, BitVec.add_assoc]
  · simp [straight, qHeadCode, execInstrBr]
  · simp [straight, qHeadCode, execInstrBr, signExtend12]
  · intro r a
    simp [straight, qHeadCode, execInstrBr, Ne.symm a]

theorem execute_q_advance (j : Nat) (valid : 1 ≤ j ∧ j ≤ 3) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(qHeadStart j+35))) :
    GroupHop s (straight qAdvanceCode s 1) 1 := by
  intro fuel
  apply execute_unit_steps (states := straight qAdvanceCode s)
  intro i inside
  obtain ⟨lo, hi⟩ := valid
  refine ⟨.base (qAdvanceCode[i]?.getD .EBREAK), fetch_at _ (qHeadStart j+35+i) _ (by unfold qHeadStart; omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [straight, qAdvanceCode, execInstrBr, pc]
  · interval_cases j <;> interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_advance_post (s : MachineState) :
    let t := straight qAdvanceCode s 1
    t.pc = s.pc + 4 ∧ t.mem = s.mem ∧ t.getReg .x21 = s.getReg .x21 + 32 ∧
      ∀ r, r ≠ .x21 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [straight, qAdvanceCode, execInstrBr]
  · simp [straight, qAdvanceCode, execInstrBr]
  · (simp [straight, qAdvanceCode, execInstrBr, signExtend12]) <;> (try rfl)
  · intro r a
    simp [straight, qAdvanceCode, execInstrBr, Ne.symm a]

theorem execute_q_call_setup (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*489)) :
    GroupHop s (straight qCallCode s 1) 1 := by
  intro fuel
  apply execute_unit_steps (states := straight qCallCode s)
  intro i inside
  refine ⟨.base (qCallCode[i]?.getD .EBREAK), fetch_at _ (489+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [straight, qCallCode, execInstrBr, pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_call_setup_post (s : MachineState) :
    let t := straight qCallCode s 1
    t.pc = s.pc + 4 ∧ t.mem = s.mem ∧ t.getReg .x12 = s.getReg .x23 ∧
      ∀ r, r ≠ .x12 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [straight, qCallCode, execInstrBr]
  · simp [straight, qCallCode, execInstrBr]
  · simp [straight, qCallCode, execInstrBr, signExtend12]
  · intro r a
    simp [straight, qCallCode, execInstrBr, Ne.symm a]

theorem q_call_fetch (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*490)) :
    fetch pairImage s = some (.base .ECALL) :=
  fetch_at s 490 .ECALL (by decide) pc rfl

theorem execute_q_exit (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*491)) :
    GroupHop s (straight qExitCode s 3) 3 := by
  intro fuel
  apply execute_unit_steps (states := straight qExitCode s)
  intro i inside
  refine ⟨.base (qExitCode[i]?.getD .EBREAK), fetch_at _ (491+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> (simp [straight, qExitCode, execInstrBr, pc]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_exit_post (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*491)) :
    let t := straight qExitCode s 3
    t.pc = 4336 ∧ t.mem = s.mem ∧ t.getReg .x6 = (s.getReg .x6 >>> 2) + s.getReg .x20 ∧
      ∀ r, r ≠ .x6 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · (simp [straight, qExitCode, execInstrBr, pc, signExtend21]) <;> (try rfl)
  · simp [straight, qExitCode, execInstrBr]
  · simp [straight, qExitCode, execInstrBr]
  · intro r a
    simp [straight, qExitCode, execInstrBr, Ne.symm a]

theorem execute_q_lower (s : MachineState) (pc : s.pc = 4336) :
    GroupHop s (straight qLowerCode s 3) 3 := by
  intro fuel
  apply execute_unit_steps (states := straight qLowerCode s)
  intro i inside
  refine ⟨.base (qLowerCode[i]?.getD .EBREAK), fetch_at _ (60+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> (simp [straight, qLowerCode, execInstrBr, pc]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_lower_post (s : MachineState) (pc : s.pc = 4336) :
    let t := straight qLowerCode s 3
    t.pc = 4348 ∧ t.mem = s.mem ∧ t.getReg .x11 = 64 ∧ t.getReg .x13 = 0 ∧ t.getReg .x29 = 14 ∧
      ∀ r, r ≠ .x11 → r ≠ .x13 → r ≠ .x29 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · (simp [straight, qLowerCode, execInstrBr, pc]) <;> (try rfl)
  · simp [straight, qLowerCode, execInstrBr]
  · (simp [straight, qLowerCode, execInstrBr, signExtend12]) <;> (try rfl)
  · (simp [straight, qLowerCode, execInstrBr, signExtend12]) <;> (try rfl)
  · (simp [straight, qLowerCode, execInstrBr, signExtend12]) <;> (try rfl)
  · intro r a b c
    simp [straight, qLowerCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

end TwoPermutationPrototype.PairCk.Packed.Checker
