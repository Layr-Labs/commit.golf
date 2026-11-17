import CommitGolfCandidate.TwoPermutationOpeningRecordGroups
import CommitGolfCandidate.TwoPermutationUnrolledMarks

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem
attribute [local irreducible] Postorder.eval

@[local simp] private theorem prep_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

structure CapContext (groups : List Nat) (state : MachineState) : Prop where
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  markBaseWord : state.getReg .x26 = BitVec.ofNat 64 markBase
  capLeavesWord : state.getReg .x27 = 256#64
  proofStart : state.getReg .x20 = BitVec.ofNat 64 proofBase
  markValue : ∀ node, 0 < node → node < 512 → machineMarks state node = markWord groups node

def capPreparation (state : MachineState) : MachineState :=
  cursorEntry ((Postorder.eval (unrollEnter state) 1 8 0).setPC 0x13e0)

/-- The unrolled cap sweep and the root cursor entry take 770 cycles. -/
theorem execute_cap_preparation (state : MachineState) (pc : state.pc = 0x13b4)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase) (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (770 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (capPreparation state) allowCoins
          return result.charge 770 0) := by
  let first := unrollEnter state
  have mid : first.getReg .x6 = 6143#64 := by
    change state.getReg .x26 + 2047 = _
    rw [base]; rfl
  have entered := entry_run state pc (768+fuel) allowCoins
  have sweep := Postorder.run first 1 8 0 280 (2+fuel) allowCoins Postorder.code_at_root
    cap_span_root (by decide) (by decide) mid rfl
  have jump := return_run _ (Postorder.eval_pc first 1 8 0 280 rfl) (1+fuel) allowCoins
  have cursor := execute_cursor_entry ((Postorder.eval first 1 8 0).setPC 0x13e0) rfl fuel allowCoins
  rw [show 770+fuel = 2+(768+fuel) by omega, entered,
      show 768+fuel = Postorder.cost 8+(2+fuel) by change 768+fuel = 766+(2+fuel); omega,
      sweep, show 2+fuel = 1+(1+fuel) by omega, jump, cursor]
  simp [capPreparation, Execution.charge, ← Nat.add_assoc, first, Postorder.cost]

/-- The concrete prepared cap starts at the root with every mark populated by the
same grouping as the transcript. -/
theorem cap_preparation_context (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState)
    (boundary : RecordBoundary s trapdoor positions state positions.card)
    (marks : RecordMarks positions state positions.card) :
    let after := capPreparation state
    after.pc = 0x13e4 ∧ after.getReg .x6 = 1#64 ∧
    after.getReg .x21 = BitVec.ofNat 64 (recordBase positions.card) ∧
    CapContext (groupsBefore positions positions.card) after := by
  let first := unrollEnter state
  let groups := groupsBefore positions positions.card
  have preserve (reg : Reg) (m : reg ∈ ([.x20,.x21,.x9,.x26,.x27] : List Reg)) :
      (capPreparation state).getReg reg = state.getReg reg := by
    have ne : reg ≠ .x6 := by intro eq; subst reg; simp at m
    unfold capPreparation cursorEntry
    simp only [MachineState.getReg_setPC, getReg_setReg, Ne.symm ne, false_and, ite_false]
    rw [pass_register _ reg m]
    unfold unrollEnter
    simp [Ne.symm ne]
  refine ⟨rfl, rfl, (preserve .x21 (by decide)).trans boundary.dest,
    ⟨(preserve .x9 (by decide)).trans boundary.capHeap,
     (preserve .x26 (by decide)).trans boundary.marks,
     (preserve .x27 (by decide)).trans boundary.capLeaves,
     (preserve .x20 (by decide)).trans boundary.proofBegin, ?_⟩⟩
  have initial (node : Nat) (leaf : 255 < node) (inside : node < 512) :
      machineMarks first node = markWord groups node := by
    change machineMarks state node = markWord groups node
    rw [marks node inside]
    exact (mark_word_leaf groups ⟨node, inside⟩ (show 256 ≤ node by omega)).symm
  intro node positive inside
  change machineMarks (Postorder.eval first 1 8 0) node = markWord groups node
  apply Postorder.root_marks first (markWord groups) (fun k lo hi => initial k (by omega) hi) _ node positive inside
  intro k lo hi
  exact mark_word_parent groups ⟨k,hi⟩ lo

end TwoPermutationPrototype.Opening
