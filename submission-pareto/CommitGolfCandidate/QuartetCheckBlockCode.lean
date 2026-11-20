import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks

/-! Straight-line pieces of the quartet block: word 58 and the jump at word 59, the slot setup at
367–372, the three slot heads, the proof-cursor advances, the parity block (`xori x6,x6,4` at 489, the
jump at 490, words 567–570: the call output is `x23` for an even group and `x23-168` for an odd group),
the call at 571, the return at 572, the exit at 491–493 (heap node `2^22 + (⌊i/4⌋ ^^^ 1)`) and the
restored lower-loop setup at 60–62. -/

namespace TwoPermutationPrototype.Packed.Checker
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
/-- Words 489–490 and 567–568: bit 2 of the index flipped, the jump to the parity block, the flipped
parity `(x6 ^ 4) & 4` (zero for an odd group), and the even-group call output `x23`. -/
def qParityCode : List Instr := [.XORI .x6 .x6 4, .JAL .x0 308, .ANDI .x28 .x6 4, .ADDI .x12 .x23 0]
/-- Word 570 (odd groups only): the call output `x23-168`. -/
def qOddCode : List Instr := [.ADDI .x12 .x23 0xf58]
/-- Words 491–493. -/
def qExitCode : List Instr := [.SRLI .x6 .x6 2, .ADD .x6 .x6 .x20, .JAL .x0 0x1ff93c]
/-- Word 572 (`jal` back to 491) only moves the PC. -/
def qReturn (s : MachineState) : MachineState := s.setPC (BitVec.ofNat 64 (4096+4*491))
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

theorem execute_q_parity (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*489)) :
    GroupHop s (straight qParityCode s 4) 4 := by
  intro fuel
  apply execute_unit_steps (states := straight qParityCode s)
  intro i inside
  refine ⟨.base (qParityCode[i]?.getD .EBREAK), fetch_at _ (if i < 2 then 489+i else 565+i) _ (by split <;> omega) ?_ ?_,
    ?_, ?_⟩
  · interval_cases i <;> (simp [straight, qParityCode, execInstrBr, pc, signExtend21]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_parity_post (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*489)) :
    let t := straight qParityCode s 4
    t.pc = BitVec.ofNat 64 (4096+4*569) ∧ t.mem = s.mem ∧ t.getReg .x6 = s.getReg .x6 ^^^ 4 ∧
      t.getReg .x28 = (s.getReg .x6 ^^^ 4) &&& 4 ∧ t.getReg .x12 = s.getReg .x23 ∧
      ∀ r, r ≠ .x6 → r ≠ .x28 → r ≠ .x12 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · (simp [straight, qParityCode, execInstrBr, pc, signExtend21]) <;> (try rfl)
  · simp [straight, qParityCode, execInstrBr]
  · (simp [straight, qParityCode, execInstrBr, signExtend12]) <;> (try rfl)
  · (simp [straight, qParityCode, execInstrBr, signExtend12]) <;> (try rfl)
  · simp [straight, qParityCode, execInstrBr, signExtend12]
  · intro r a b c
    simp [straight, qParityCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

/-- The branch at word 569 on the flipped group parity in `x28` (nonzero for an even group). -/
def qBranch (s : MachineState) : MachineState := execInstrBr s (.BNE .x28 .x0 8)

theorem execute_q_branch (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*569)) :
    GroupHop s (qBranch s) 1 := by
  intro fuel
  have fetched : fetch packedImage s = some (.base (.BNE .x28 .x0 8)) := fetch_at s 569 _ (by omega) pc rfl
  have step := execute_ordinary_step packedImage (.base (.BNE .x28 .x0 8)) s (qBranch s) fuel false fetched rfl
  rw [show 1+fuel = fuel+1 by omega, step]
  rfl

theorem q_branch_post (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*569)) :
    (qBranch s).pc = (if s.getReg .x28 = 0 then BitVec.ofNat 64 (4096+4*570) else BitVec.ofNat 64 (4096+4*571)) ∧
      (qBranch s).mem = s.mem ∧ ∀ r, (qBranch s).getReg r = s.getReg r := by
  have zero : s.getReg .x0 = 0 := rfl
  by_cases even : s.getReg .x28 = 0
  · have miss : (s.getReg .x28 != s.getReg .x0) = false := by rw [even, zero]; rfl
    have shape : qBranch s = s.setPC (s.pc + 4) := by
      simp only [qBranch, execInstrBr, miss]; rfl
    rw [shape, if_pos even, pc]
    exact ⟨rfl, rfl, fun r => MachineState.getReg_setPC⟩
  · have hit : (s.getReg .x28 != s.getReg .x0) = true := by
      rw [zero]; simpa using even
    have shape : qBranch s = s.setPC (s.pc + signExtend13 8) := by
      simp only [qBranch, execInstrBr, hit]; rfl
    rw [shape, if_neg even, pc]
    exact ⟨rfl, rfl, fun r => MachineState.getReg_setPC⟩

theorem execute_q_odd (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*570)) :
    GroupHop s (straight qOddCode s 1) 1 := by
  intro fuel
  apply execute_unit_steps (states := straight qOddCode s)
  intro i inside
  refine ⟨.base (qOddCode[i]?.getD .EBREAK), fetch_at _ (570+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [straight, qOddCode, execInstrBr, pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem q_odd_post (s : MachineState) :
    let t := straight qOddCode s 1
    t.pc = s.pc + 4 ∧ t.mem = s.mem ∧ t.getReg .x12 = s.getReg .x23 + signExtend12 0xf58 ∧
      ∀ r, r ≠ .x12 → t.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [straight, qOddCode, execInstrBr]
  · simp [straight, qOddCode, execInstrBr]
  · simp [straight, qOddCode, execInstrBr]
  · intro r a
    simp [straight, qOddCode, execInstrBr, Ne.symm a]

theorem q_call_fetch (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*571)) :
    fetch packedImage s = some (.base .ECALL) :=
  fetch_at s 571 .ECALL (by decide) pc rfl

private theorem return_pc : BitVec.ofNat 64 (4096+4*572) + signExtend21 0x1ffebc = BitVec.ofNat 64 (4096+4*491) := by
  decide

theorem execute_q_return (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*572)) :
    GroupHop s (qReturn s) 1 := by
  intro fuel
  have fetched : fetch packedImage s = some (.base (.JAL .x0 0x1ffebc)) := fetch_at s 572 _ (by decide) pc rfl
  have shape : execInstrBr s (.JAL .x0 0x1ffebc) = qReturn s := by
    rw [show execInstrBr s (.JAL .x0 0x1ffebc) = s.setPC (s.pc + signExtend21 0x1ffebc) from rfl, pc, return_pc]
    rfl
  have step := execute_ordinary_step packedImage (.base (.JAL .x0 0x1ffebc)) s (qReturn s) fuel false fetched
    (by rw [← shape]; rfl)
  rw [show 1+fuel = fuel+1 by omega, step]
  rfl

theorem q_return_post (s : MachineState) :
    (qReturn s).pc = BitVec.ofNat 64 (4096+4*491) ∧ (qReturn s).mem = s.mem ∧ ∀ r, (qReturn s).getReg r = s.getReg r :=
  ⟨rfl, rfl, fun _ => MachineState.getReg_setPC⟩

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

end TwoPermutationPrototype.Packed.Checker
