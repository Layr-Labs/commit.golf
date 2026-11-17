import CommitGolfCandidate.TwoPermutationOpeningRecordGroups
import CommitGolfCandidate.TwoPermutationUnrolledMarks

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem
attribute [local irreducible] markPass

@[local simp] private theorem prep_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

structure CapContext (groups : List Nat) (state : MachineState) : Prop where
  heap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  markBaseWord : state.getReg .x26 = BitVec.ofNat 64 markBase
  capLeavesWord : state.getReg .x27 = 256#64
  proofStart : state.getReg .x20 = BitVec.ofNat 64 proofBase
  markValue : ∀ node, 0 < node → node < 512 → machineMarks state node = markWord groups node

def capPreparation (state : MachineState) : MachineState :=
  cursorEntry ((markPass (unrollEnter state) 255).setPC 0x10dc)

/-- The unrolled cap sweep and the root cursor entry take 1,024 cycles. -/
theorem execute_cap_preparation (state : MachineState) (pc : state.pc = 0x10b0)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1024 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (capPreparation state) allowCoins
          return result.charge 1024 0) := by
  let first := unrollEnter state
  have mid : first.getReg .x6 = 6143#64 := by
    change state.getReg .x26 + 2047 = _
    rw [base]; rfl
  have entered := entry_run state pc (1022+fuel) allowCoins
  have sweep := run_pass first 255 (2+fuel) allowCoins (by decide) rfl mid
  have jump := return_run _ (pass_end first 255 (by decide) rfl) (1+fuel) allowCoins
  have cursor := execute_cursor_entry ((markPass first 255).setPC 0x10dc) rfl fuel allowCoins
  rw [show 1024+fuel = 2+(1022+fuel) by omega, entered,
      show 1022+fuel = 4*255+(2+fuel) by omega, sweep, show 2+fuel = 1+(1+fuel) by omega, jump, cursor]
  simp [capPreparation, Execution.charge, ← Nat.add_assoc, first]

/-- The concrete prepared cap starts at the root with every mark populated by the
same grouping as the transcript. -/
theorem cap_preparation_context (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState)
    (boundary : RecordBoundary s trapdoor positions state positions.card)
    (marks : RecordMarks positions state positions.card) :
    let after := capPreparation state
    after.pc = 0x10e0 ∧ after.getReg .x6 = 1#64 ∧
    after.getReg .x21 = BitVec.ofNat 64 (recordBase positions.card) ∧
    CapContext (groupsBefore positions positions.card) after := by
  let first := unrollEnter state
  let groups := groupsBefore positions positions.card
  have mid : first.getReg .x6 = 6143#64 := by
    change state.getReg .x26 + 2047 = _
    rw [boundary.marks]; rfl
  have preserve (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29) :
      (capPreparation state).getReg reg = state.getReg reg := by
    unfold capPreparation cursorEntry
    simp only [MachineState.getReg_setPC, getReg_setReg, Ne.symm a, false_and, ite_false]
    rw [pass_register _ _ reg c d]
    unfold unrollEnter
    simp [Ne.symm a]
  refine ⟨rfl, rfl, (preserve .x21 (by decide) (by decide) (by decide) (by decide)).trans boundary.dest,
    ⟨(preserve .x25 (by decide) (by decide) (by decide) (by decide)).trans boundary.capHeap,
     (preserve .x26 (by decide) (by decide) (by decide) (by decide)).trans boundary.marks,
     (preserve .x27 (by decide) (by decide) (by decide) (by decide)).trans boundary.capLeaves,
     (preserve .x20 (by decide) (by decide) (by decide) (by decide)).trans boundary.proofBegin, ?_⟩⟩
  have initial (node : Nat) (leaf : 255 < node) (inside : node < 512) :
      machineMarks first node = markWord groups node := by
    change machineMarks state node = markWord groups node
    rw [marks node inside]
    exact (mark_word_leaf groups ⟨node, inside⟩ (show 256 ≤ node by omega)).symm
  intro node positive inside
  change machineMarks (markPass first 255) node = markWord groups node
  exact pass_marks first groups 255 (by decide) mid initial node positive inside

end TwoPermutationPrototype.Opening
