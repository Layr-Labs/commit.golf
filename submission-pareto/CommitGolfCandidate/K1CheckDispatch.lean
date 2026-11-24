import CommitGolfCandidate.TwoPermutationPackedRecordLeafPrelude
import CommitGolfCandidate.TaggedPinnedModel

/-! # The K1 rank dispatcher (check words 22 and 494–499)

Word 22 jumps to word 494, which loads the position `i` into `x6`, computes the salt-group rank
`(i mod 4096) mod 11` into `x7` (with `x29 = 11`) and branches: rank 0 continues at word 500 (the
A leaf), any other rank jumps back to word 23, where the record's leaf continues. On that path the
state at word 28 is the record's `beginRecord` state of a start state whose only differences are
`x7` and `x29` (`sf_setup_eq`), so the record's leaf lemmas apply to it unchanged. -/
namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (beginRecordCode beginRecord record_setup_post record_setup_register
  record_setup_mem)
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem sx0 : signExtend12 0 = 0 := by decide
@[local simp] private theorem sx11 : signExtend12 11 = 11 := by decide
@[local simp] private theorem get_mem_set_pc (s : MachineState) (v a : Word) :
    (s.setPC v).getMem a = s.getMem a := rfl
@[local simp] private theorem pc_set_pc (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl

/-- Compose ordinary instructions of any cost. -/
theorem execute_costed_steps (image : Image) (count fuel : Nat)
    (states : Nat → MachineState) (cost : Nat → Nat) (allowCoins : Bool)
    (trace : ∀ i < count, ∃ instruction,
      fetch image (states i) = some instruction ∧
      ordinaryStep (states i) instruction = some (states (i + 1)) ∧
      instructionCycles instruction = cost i) :
    execute image (count + fuel) (states 0) allowCoins =
      (do let result ← execute image fuel (states count) allowCoins
          return result.charge (∑ i ∈ Finset.range count, cost i) 0) := by
  induction count generalizing states cost with
  | zero => simp [Execution.charge]
  | succ count ih =>
    obtain ⟨instruction, fetched, stepped, priced⟩ := trace 0 (by omega)
    rw [Nat.succ_add, execute_ordinary_step image instruction _ _ _ _ fetched stepped, priced]
    have tail := ih (fun i => states (i + 1)) (fun i => cost (i + 1)) (by
      intro i hi
      exact trace (i + 1) (by omega))
    simp only [tail, bind_assoc, pure_bind]
    simp [Execution.charge, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Word 22 and words 494–497. -/
def dispatchCode : List Instr :=
  [.JAL .x0 1888, .LD .x6 .x8 0, .REMU .x7 .x6 .x26, .ADDI .x29 .x0 11, .REMU .x7 .x7 .x29]

def dispatchCost (i : Nat) : Nat := if i = 2 ∨ i = 4 then 4 else 1

def dispatchPrefix (s : MachineState) (count : Nat) : MachineState :=
  (dispatchCode.take count).foldl execInstrBr s

/-- The state at word 498, before the branch. -/
def dispatched (s : MachineState) : MachineState := dispatchPrefix s 5

/-- The salt-group rank of a position index, as the machine computes it. -/
def machineRank (i : Nat) : Nat := (i % 4096) % 11

theorem machine_rank_ahead (index : Index) : (machineRank index.val = 0) ↔ isAHead index = true := by
  unfold machineRank isAHead
  simp

theorem execute_dispatch (s : MachineState) (pc : s.pc = 0x1058)
    (access : accessValid (s.getReg .x8) 8 = true) (fuel : Nat) :
    execute packedImage (5+fuel) s false =
      (do let result ← execute packedImage fuel (dispatched s) false
          return result.charge 11 0) := by
  have run := execute_costed_steps packedImage 5 fuel (dispatchPrefix s) dispatchCost false (by
    intro i bounded
    refine ⟨.base (dispatchCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
    · apply fetch_at _ (if i = 0 then 22 else 493+i) _ (by split <;> omega)
      · interval_cases i <;> simp [dispatchPrefix, dispatchCode, execInstrBr, MachineState.setPC, pc,
          signExtend21] <;> rfl
      · interval_cases i <;> rfl
    · interval_cases i <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, dispatchPrefix, dispatchCode,
        signExtend12, access] <;> assumption
    · interval_cases i <;> rfl)
  simpa [dispatched, dispatchPrefix, dispatchCost, Finset.sum_range_succ] using run

theorem dispatched_post (s : MachineState) :
    let d := dispatched s
    d.getReg .x6 = s.getMem (s.getReg .x8) ∧
    d.getReg .x7 = rv64_remu (rv64_remu (s.getMem (s.getReg .x8)) (s.getReg .x26)) 11 ∧
    d.getReg .x29 = 11 ∧ d.mem = s.mem ∧ d.pc = s.pc + 1888 + 16 ∧
    ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x29 → d.getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dispatched, dispatchPrefix, dispatchCode, execInstrBr, signExtend12]
  · simp [dispatched, dispatchPrefix, dispatchCode, execInstrBr, signExtend12] <;> rfl
  · simp [dispatched, dispatchPrefix, dispatchCode, execInstrBr, signExtend12] <;> rfl
  · rfl
  · simp [dispatched, dispatchPrefix, dispatchCode, execInstrBr, signExtend21, BitVec.add_assoc] <;> rfl
  · intro r a b c
    simp [dispatched, dispatchPrefix, dispatchCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

theorem dispatched_rank (s : MachineState) (i : Nat) (bound : i < 2^24)
    (loaded : s.getMem (s.getReg .x8) = BitVec.ofNat 64 i) (groups : s.getReg .x26 = 4096) :
    (dispatched s).getReg .x7 = BitVec.ofNat 64 (machineRank i) := by
  rw [(dispatched_post s).2.1, loaded, groups]
  have h1 : ((4096 : Word) == 0#64) = false := by decide
  have h2 : ((11 : Word) == 0#64) = false := by decide
  unfold rv64_remu machineRank
  simp only [h1, h2, Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_toNat_eq
  have t1 : (4096 : Word).toNat = 4096 := rfl
  have t2 : (11 : Word).toNat = 11 := rfl
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, t1, t2]
  omega

/-! ### The salt-first path -/

/-- The register writes of the dispatcher, made at the record's entry PC: the start state of the
record leaf on the salt-first path. -/
def sfPre (s : MachineState) : MachineState := (dispatched s).setPC s.pc

def sfReturnCode : List Instr := [.BEQ .x7 .x0 8, .JAL .x0 0x1ff890]

/-- The state at word 23 on the salt-first path. -/
def sfReturned (s : MachineState) : MachineState := sfReturnCode.foldl execInstrBr (dispatched s)

/-- The state at word 28 on the salt-first path. -/
def sfSetup (s : MachineState) : MachineState :=
  (beginRecordCode.drop 1).foldl execInstrBr (sfReturned s)

private theorem set_reg_self_x6 (s : MachineState) : s.setReg .x6 (s.getReg .x6) = s := by
  cases s with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    simp only [MachineState.setReg, MachineState.getReg]
    congr 1
    funext r
    cases r <;> rfl

/-- The branch at word 498 falls through and word 499 jumps to word 23: the state there is the
record's state after its index load at word 22, started from the dispatcher's registers. -/
theorem return_eq (d : MachineState) (p : Word) (rank : d.getReg .x7 ≠ 0)
    (back : d.pc + 4 + signExtend21 0x1ff890 = p + 4)
    (loaded : d.getMem (d.getReg .x8 + signExtend12 0) = d.getReg .x6) :
    execInstrBr (execInstrBr d (.BEQ .x7 .x0 8)) (.JAL .x0 0x1ff890) = execInstrBr (d.setPC p) (.LD .x6 .x8 0) := by
  have miss : (d.getReg .x7 == d.getReg .x0) = false := by
    rw [show d.getReg .x0 = 0 from rfl]
    simpa using rank
  have beq : execInstrBr d (.BEQ .x7 .x0 8) = d.setPC (d.pc + 4) := by
    simp only [execInstrBr, miss]; rfl
  rw [beq]
  change d.setPC (d.pc + 4 + signExtend21 0x1ff890) =
    ((d.setPC p).setReg .x6 (d.getMem (d.getReg .x8 + signExtend12 0))).setPC (p + 4)
  rw [back, loaded]
  change d.setPC (p + 4) = ((d.setReg .x6 (d.getReg .x6)).setPC p).setPC (p + 4)
  rw [set_reg_self_x6]
  rfl

theorem sf_returned_eq (s : MachineState) (pc : s.pc = 0x1058)
    (rank : (dispatched s).getReg .x7 ≠ 0) :
    sfReturned s = execInstrBr (sfPre s) (.LD .x6 .x8 0) := by
  obtain ⟨x6, _, _, mem, dpc, kept⟩ := dispatched_post s
  have back : (dispatched s).pc + 4 + signExtend21 0x1ff890 = s.pc + 4 := by
    rw [dpc, pc]; decide
  have loaded : (dispatched s).getMem ((dispatched s).getReg .x8 + signExtend12 0) = (dispatched s).getReg .x6 := by
    rw [kept .x8 (by decide) (by decide) (by decide), x6, sx0]
    simp [MachineState.getMem, mem]
  rw [show sfPre s = (dispatched s).setPC s.pc from rfl]
  exact return_eq (dispatched s) s.pc rank back loaded

theorem sf_setup_eq (s : MachineState) (pc : s.pc = 0x1058)
    (rank : (dispatched s).getReg .x7 ≠ 0) :
    sfSetup s = beginRecord (sfPre s) 6 := by
  unfold sfSetup beginRecord
  rw [sf_returned_eq s pc rank]
  simp only [beginRecordCode, List.drop, List.take, List.foldl]

theorem execute_sf_setup (s : MachineState) (pc : s.pc = 0x1058)
    (access : accessValid (s.getReg .x8) 8 = true) (rank : (dispatched s).getReg .x7 ≠ 0) (fuel : Nat) :
    execute packedImage (12+fuel) s false =
      (do let result ← execute packedImage fuel (beginRecord (sfPre s) 6) false
          return result.charge 18 0) := by
  obtain ⟨_, _, _, _, dpc, _⟩ := dispatched_post s
  have miss : ((dispatched s).getReg .x7 == (dispatched s).getReg .x0) = false := by
    rw [show (dispatched s).getReg .x0 = 0 from rfl]
    simpa using rank
  let states : Nat → MachineState := fun i =>
    ((sfReturnCode ++ beginRecordCode.drop 1).take i).foldl execInstrBr (dispatched s)
  have tail := execute_unit_steps packedImage 7 fuel states false (by
    intro i bounded
    refine ⟨.base ((sfReturnCode ++ beginRecordCode.drop 1)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
    · apply fetch_at _ (if i < 2 then 498+i else 21+i) _ (by split <;> omega)
      · interval_cases i <;> simp [states, sfReturnCode, beginRecordCode, execInstrBr, MachineState.setPC,
          dpc, pc, miss, signExtend13, signExtend21] <;> rfl
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl)
  have last : states 7 = sfSetup s := by
    simp only [states, sfSetup, sfReturned, sfReturnCode, beginRecordCode, List.drop, List.take,
      List.cons_append, List.nil_append, List.foldl]
  rw [show 12+fuel = 5+(7+fuel) by omega, execute_dispatch s pc access, show dispatched s = states 0 from rfl,
    tail, last, sf_setup_eq s pc rank]
  simp [Execution.charge, ← Nat.add_assoc]

theorem sf_pre_register (s : MachineState) (r : Reg) (h7 : r ≠ .x7) (h29 : r ≠ .x29) (h6 : r ≠ .x6) :
    (sfPre s).getReg r = s.getReg r := by
  simp only [sfPre, MachineState.getReg_setPC]
  exact (dispatched_post s).2.2.2.2.2 r h6 h7 h29

theorem sf_pre_mem (s : MachineState) : (sfPre s).mem = s.mem := rfl

theorem sf_pre_pc (s : MachineState) : (sfPre s).pc = s.pc := rfl

theorem sf_pre_x6 (s : MachineState) : (sfPre s).getReg .x6 = s.getMem (s.getReg .x8) := by
  simp only [sfPre, MachineState.getReg_setPC]
  exact (dispatched_post s).1

/-! ### The A path: the branch to word 500 -/

/-- The state at word 500 on the A path. -/
def aEntry (s : MachineState) : MachineState := execInstrBr (dispatched s) (.BEQ .x7 .x0 8)

theorem execute_a_dispatch (s : MachineState) (pc : s.pc = 0x1058)
    (access : accessValid (s.getReg .x8) 8 = true) (rank : (dispatched s).getReg .x7 = 0) (fuel : Nat) :
    execute packedImage (6+fuel) s false =
      (do let result ← execute packedImage fuel (aEntry s) false
          return result.charge 12 0) := by
  obtain ⟨_, _, _, _, dpc, _⟩ := dispatched_post s
  have fetched : fetch packedImage (dispatched s) = some (.base (.BEQ .x7 .x0 8)) := by
    apply fetch_at _ 498 _ (by omega)
    · rw [dpc, pc]; rfl
    · rfl
  have step := execute_ordinary_step packedImage (.base (.BEQ .x7 .x0 8)) (dispatched s) (aEntry s) fuel false
    fetched rfl
  rw [show 6+fuel = 5+(fuel+1) by omega, execute_dispatch s pc access, step]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem a_entry_post (s : MachineState) (pc : s.pc = 0x1058) (rank : (dispatched s).getReg .x7 = 0) :
    let e := aEntry s
    e.pc = BitVec.ofNat 64 (4096+4*500) ∧ e.mem = s.mem ∧
    e.getReg .x6 = s.getMem (s.getReg .x8) ∧
    ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x29 → e.getReg r = s.getReg r := by
  obtain ⟨x6, _, _, mem, dpc, kept⟩ := dispatched_post s
  have hit : ((dispatched s).getReg .x7 == (dispatched s).getReg .x0) = true := by
    rw [rank]; rfl
  have shape : aEntry s = (dispatched s).setPC ((dispatched s).pc + signExtend13 8) := by
    simp only [aEntry, execInstrBr, hit]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [shape]; change (dispatched s).pc + signExtend13 8 = _; rw [dpc, pc]; decide
  · rw [shape]; exact mem
  · rw [shape, MachineState.getReg_setPC]; exact x6
  · intro r a b c
    rw [shape, MachineState.getReg_setPC]; exact kept r a b c

end TwoPermutationPrototype.Packed.RecordLeaf
