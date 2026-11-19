import CommitGolfCandidate.TwoPermutationPackedUnrolledMarks
import CommitGolfCandidate.TwoPermutationPackedOpeningCapMoves

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

open Opening (markParentPrefix markMachine markBase machineMarks markParent mark_addresses
  markWord mark_word_parent nat_address_injective capMarkInstructions)

attribute [local irreducible] markParentPrefix
set_option maxRecDepth 4096

open Opening.Postorder
open Opening (cap_span_root getReg_setReg getReg_setMem)
attribute [local simp] getReg_setReg getReg_setMem
attribute [local irreducible] Opening.Postorder.eval

def cursorEntry (state : MachineState) : MachineState :=
  (state.setReg .x6 1).setPC 0x19dc

/-- Start the cap cursor at the root after all parent marks are set. -/
theorem execute_cursor_entry (state : MachineState) (pc : state.pc = 0x19d8)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (cursorEntry state) allowCoins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 630 (.ADDI .x6 .x0 1) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x6 .x0 1)) = some (cursorEntry state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      cursorEntry, pc, show state.getReg .x0 = 0#64 from rfl]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

def capPreparation (state : MachineState) : MachineState :=
  cursorEntry ((Opening.Postorder.eval (unrollEnter state) 1 8 0).setPC 0x19d8)

/-- The unrolled cap sweep and the root cursor entry take 770 cycles. -/
theorem execute_cap_preparation (state : MachineState) (pc : state.pc = 0x19ac)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (770 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (capPreparation state) allowCoins
          return result.charge 770 0) := by
  let first := unrollEnter state
  have mid : first.getReg .x6 = 6143#64 := by
    change state.getReg .x26 + 2047 = _
    rw [base]; rfl
  have entered := entry_run state pc (768+fuel) allowCoins
  have sweep := Opening.Postorder.run first 1 8 0 684 (2+fuel) allowCoins Opening.Postorder.code_at_root
    cap_span_root (by decide) (by decide) mid rfl
  have jump := return_run _ (Opening.Postorder.eval_pc first 1 8 0 684 rfl) (1+fuel) allowCoins
  have cursor := execute_cursor_entry ((Opening.Postorder.eval first 1 8 0).setPC 0x19d8) rfl fuel allowCoins
  rw [show 770+fuel = 2+(768+fuel) by omega, entered,
      show 768+fuel = Opening.Postorder.cost 8+(2+fuel) by change 768+fuel = 766+(2+fuel); omega,
      sweep, show 2+fuel = 1+(1+fuel) by omega, jump, cursor]
  simp [capPreparation, Execution.charge, ← Nat.add_assoc, first, Opening.Postorder.cost]

/-- The packed cap enters the exact traversal with the same marks, heap and output cursor. -/
theorem cap_preparation_context (state : MachineState) (groups : List Nat) (dest : Nat)
    (markBaseReg : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (heap : state.getReg .x25 = BitVec.ofNat 64 Opening.trapdoorBase)
    (leaves : state.getReg .x27 = 256#64)
    (proofStart : state.getReg .x20 = BitVec.ofNat 64 Opening.proofBase)
    (pointer : state.getReg .x21 = BitVec.ofNat 64 dest)
    (marks : ∀ node, 255 < node → node < 512 → machineMarks state node = markWord groups node) :
    let after := capPreparation state
    after.pc = 0x19dc ∧ CapPosition groups after 1 dest := by
  let first := unrollEnter state
  have preserve (reg : Reg) (m : reg ∈ ([.x20,.x21,.x25,.x26,.x27] : List Reg)) :
      (capPreparation state).getReg reg = state.getReg reg := by
    have ne : reg ≠ .x6 := by intro eq; subst reg; simp at m
    unfold capPreparation cursorEntry
    simp only [MachineState.getReg_setPC, getReg_setReg, Ne.symm ne, false_and, ite_false]
    rw [pass_register _ reg m]
    unfold unrollEnter
    simp [Ne.symm ne]
  refine ⟨rfl, ⟨⟨(preserve .x25 (by decide)).trans heap,
      (preserve .x26 (by decide)).trans markBaseReg,
      (preserve .x27 (by decide)).trans leaves,
      (preserve .x20 (by decide)).trans proofStart, ?_⟩, rfl,
    (preserve .x21 (by decide)).trans pointer⟩⟩
  intro node positive inside
  change machineMarks (Opening.Postorder.eval first 1 8 0) node = markWord groups node
  apply Opening.Postorder.root_marks first (markWord groups) (fun k lo hi => marks k (by omega) hi) _ node positive inside
  intro k lo hi
  exact mark_word_parent groups ⟨k,hi⟩ lo

end TwoPermutationPrototype.PackedOpening
