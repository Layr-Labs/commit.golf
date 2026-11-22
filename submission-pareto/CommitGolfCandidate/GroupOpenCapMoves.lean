import CommitGolfCandidate.GroupOpenCapFlow

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

open Opening (CapSpan markBase cap_span_is_leaf cap_span_node
  cap_span_is_internal nat_address_injective)

attribute [local simp] at_parity_test at_parent_step
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem moves_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem moves_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem mem_setReg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by cases reg <;> rfl

attribute [local simp] mem_setReg

def RunsOpeningBlock (before after : MachineState) (cycles : Nat) : Prop :=
  ∀ fuel allowCoins, execute openingImage (cycles + fuel) before allowCoins =
    (do let result ← execute openingImage fuel after allowCoins
        return result.charge cycles 0)

attribute [local irreducible] execute

theorem RunsOpeningBlock.next {first middle last : MachineState} {a b : Nat}
    (head : RunsOpeningBlock first middle a) (tail : RunsOpeningBlock middle last b) :
    RunsOpeningBlock first last (a + b) := by
  intro fuel coins
  rw [Nat.add_assoc, head (b+fuel) coins, tail fuel coins]
  simp [Execution.charge, ← Nat.add_assoc]

structure CapPosition (groups : List Nat) (state : MachineState) (node dest : Nat) : Prop where
  context : CapContext groups state
  nodeWord : state.getReg .x6 = BitVec.ofNat 64 node
  destWord : state.getReg .x21 = BitVec.ofNat 64 dest

private theorem context_memory {groups : List Nat} {before after : MachineState}
    (context : CapContext groups before)
    (register : ∀ r, r ∈ ([.x25,.x26,.x27,.x20,.x23] : List Reg) → after.getReg r = before.getReg r)
    (memory : after.mem = before.mem) : CapContext groups after :=
  context.of_preserved register (fun n _ _ => congrFun memory (BitVec.ofNat 64 (markBase+8*n)))

/-- A marked level-5 node (`x16 = 8 node ≥ 256`) leaves the walk for the chunk jump at 708. -/
theorem cap_chunk_step (groups : List Nat) (state : MachineState) (node dest : Nat)
    (position : CapPosition groups state node dest) (span : CapSpan node 3)
    (level : state.getReg .x16 = BitVec.ofNat 64 (8 * node)) (pc : state.pc = 0x1a64) :
    RunsOpeningBlock state (state.setPC 0x1b10) 1 ∧
    CapPosition groups (state.setPC 0x1b10) node dest ∧
    (state.setPC 0x1b10).getReg .x16 = BitVec.ofNat 64 (8 * node) := by
  have bounded := (cap_span_node node 3 span).2
  have low := span.start
  have comparison : BitVec.ult (state.getReg .x16) (state.getReg .x27) = false := by
    rw [level, position.context.capLeavesWord, BitVec.ult_eq_decide]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * node < 2 ^ 64)]
    simp only [decide_eq_false_iff_not, Nat.reducePow, Nat.reduceMod] at low ⊢
    omega
  have next := cursor_chunk_post state pc comparison
  refine ⟨fun fuel coins => by rw [← next]; exact execute_cursor_chunk _ pc fuel coins, ?_, level⟩
  exact ⟨context_memory position.context (fun _ _ => rfl) rfl, position.nodeWord, position.destWord⟩

/-- A marked internal node descends to the left child with no output. -/
theorem cap_descend_step (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (position : CapPosition groups state node dest) (span : CapSpan node (height + 4))
    (level : state.getReg .x16 = BitVec.ofNat 64 (8 * node)) (pc : state.pc = 0x1a64) :
    RunsOpeningBlock state (cursorKnownPrefix state 3) 3 ∧
    (cursorKnownPrefix state 3).pc = 0x1a54 ∧
    CapPosition groups (cursorKnownPrefix state 3) (2 * node) dest ∧
    (cursorKnownPrefix state 3).mem = state.mem := by
  have high : node < 32 := by
    have finish := span.finish
    have pow : 16 ≤ 2 ^ (height + 4) := by
      rw [pow_add]; have := Nat.one_le_two_pow (n := height); norm_num; omega
    have : (node + 1) * 16 ≤ (node + 1) * 2 ^ (height + 4) := Nat.mul_le_mul_left _ pow
    omega
  have comparison : BitVec.ult (state.getReg .x16) (state.getReg .x27) = true := by
    rw [level, position.context.capLeavesWord, BitVec.ult_eq_decide]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * node < 2 ^ 64)]
    simp only [decide_eq_true_eq, Nat.reducePow, Nat.reduceMod]
    omega
  have ⟨target, nodeAfter, destAfter, memAfter⟩ := cursor_descend_post state pc comparison
  refine ⟨fun fuel coins => execute_cursor_descend _ pc fuel coins comparison, target, ⟨?_, ?_, ?_⟩, memAfter⟩
  · apply context_memory position.context _ memAfter
    intro r member
    have notNode : r ≠ .x6 := by intro same; subst r; simp at member
    simp [cursorKnownPrefix, capWalkInstructions, execInstrBr, comparison, Ne.symm notNode]
  · rw [nodeAfter, position.nodeWord, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 node * BitVec.ofNat 64 2 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm node]
  · exact destAfter.trans position.destWord

private theorem parity_check_mem (state : MachineState) :
    (advancePrefix state 43 2).mem = state.mem := by
  by_cases even : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend12, even]
  all_goals rfl

private theorem parity_check_reg (state : MachineState) (reg : Reg) (distinct : reg ≠ .x7) :
    (advancePrefix state 43 2).getReg reg = state.getReg reg := by
  by_cases even : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend12, even, Ne.symm distinct]

private theorem up_reg (state : MachineState) (reg : Reg) (different : reg ≠ .x6) :
    (advancePrefix state 45 2).getReg reg = state.getReg reg := by
  by_cases taken : state.getReg .x6 >>> 1 = state.getReg .x23 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend13, taken, Ne.symm different]

/-- The parity test at 703/704 (two cycles); there is no root test on entry. -/
def afterAdvanceChecks (state : MachineState) : MachineState :=
  advancePrefix state 43 2

theorem advance_checks (groups : List Nat) (state : MachineState) (node dest : Nat)
    (position : CapPosition groups state node dest) (bounded : node < 512)
    (pc : state.pc = 0x1afc) :
    RunsOpeningBlock state (afterAdvanceChecks state) 2 ∧
    (afterAdvanceChecks state).pc = (if node % 2 = 0 then 0x1a50 else 0x1b04) ∧
    CapPosition groups (afterAdvanceChecks state) node dest ∧
    (afterAdvanceChecks state).mem = state.mem := by
  have memory : (afterAdvanceChecks state).mem = state.mem := parity_check_mem state
  have saved (reg : Reg) (different : reg ≠ .x7) :
      (afterAdvanceChecks state).getReg reg = state.getReg reg :=
    parity_check_reg state reg different
  refine ⟨fun fuel coins => execute_advance_parity_test state pc fuel coins, ?_,
    ⟨?_, (saved .x6 (by decide)).trans position.nodeWord, (saved .x21 (by decide)).trans position.destWord⟩,
    memory⟩
  · unfold afterAdvanceChecks
    rw [advance_parity_target state pc, position.nodeWord]
    have lowBits : (BitVec.ofNat 64 node &&& 1#64) = BitVec.ofNat 64 (node % 2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : node < 2 ^ 64)]
      have small : node % 2 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt small]
      exact Nat.and_two_pow_sub_one_eq_mod _ 1
    rw [lowBits]
    have zero : BitVec.ofNat 64 (node % 2) = 0#64 ↔ node % 2 = 0 := by
      constructor
      · exact nat_address_injective (left := node%2) (right := 0) (by omega) (by decide)
      · intro h
        rw [h]
    simp only [zero]
  · apply context_memory position.context _ memory
    intro r member
    have different : r ≠ .x7 := by intro same; subst r; simp at member
    exact saved r different

/-- An even node steps to its right sibling through row 660 (three cycles in all). -/
def advanceRight (state : MachineState) : MachineState :=
  advanceRightStep (afterAdvanceChecks state)

/-- An odd node climbs to its parent (four cycles in all). -/
def advanceUp (state : MachineState) : MachineState :=
  advancePrefix (afterAdvanceChecks state) 45 2

theorem advance_left_to_right (groups : List Nat) (state : MachineState) (parent dest : Nat)
    (positive : 0 < parent) (bounded : 2 * parent < 512)
    (position : CapPosition groups state (2 * parent) dest) (pc : state.pc = 0x1afc) :
    RunsOpeningBlock state (advanceRight state) 3 ∧
    (advanceRight state).pc = 0x1a54 ∧
    CapPosition groups (advanceRight state) (2 * parent + 1) dest ∧
    (advanceRight state).mem = state.mem := by
  have ⟨checks, target, pos, memory⟩ :=
    advance_checks groups state (2*parent) dest position bounded pc
  have right : (afterAdvanceChecks state).pc = 0x1a50 := by simpa [show (2*parent) % 2 = 0 by omega] using target
  have ⟨nextPC, nextNode, nextDest, nextMem⟩ := advance_right_post _ right
  refine ⟨checks.next (fun fuel coins => execute_advance_right _ right fuel coins), nextPC,
    ⟨?_, ?_, nextDest.trans pos.destWord⟩, nextMem.trans memory⟩
  · apply context_memory pos.context _ nextMem
    intro reg member
    have different : reg ≠ .x6 := by intro same; subst reg; simp at member
    simp [advanceRight, advanceRightStep, execInstrBr, Ne.symm different]
  · rw [advanceRight, nextNode, pos.nodeWord]
    exact (BitVec.ofNat_add (n := 64) (2*parent) 1).symm

private theorem climb_word (parent : Nat) (bounded : 2 * parent + 1 < 512) :
    BitVec.ofNat 64 (2*parent+1) >>> 1 = BitVec.ofNat 64 parent := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2*parent+1 < 2^64), Nat.mod_eq_of_lt (by omega : parent < 2^64)]
  omega

/-- The climb at 705/706 from an odd node `2·parent+1`: back to 703 unless the parent is the root. -/
private theorem advance_climb (groups : List Nat) (state : MachineState) (parent dest : Nat)
    (bounded : 2 * parent + 1 < 512)
    (position : CapPosition groups state (2 * parent + 1) dest) (pc : state.pc = 0x1afc) :
    RunsOpeningBlock state (advanceUp state) 4 ∧
    (advanceUp state).pc = (if parent = 1 then 0x1b0c else 0x1afc) ∧
    CapPosition groups (advanceUp state) parent dest ∧
    (advanceUp state).mem = state.mem := by
  have ⟨checks, target, pos, memory⟩ :=
    advance_checks groups state (2*parent+1) dest position bounded pc
  have up : (afterAdvanceChecks state).pc = 0x1b04 := by
    simpa [show (2 * parent + 1) % 2 ≠ 0 by omega] using target
  have ⟨nextPC, nextNode, nextDest, nextMem⟩ := advance_up_post _ up
  have half : (afterAdvanceChecks state).getReg .x6 >>> 1 = BitVec.ofNat 64 parent := by
    rw [pos.nodeWord]
    exact climb_word parent bounded
  have rootTest : ((afterAdvanceChecks state).getReg .x6 >>> 1 = (afterAdvanceChecks state).getReg .x23) ↔
      parent = 1 := by
    rw [half, pos.context.one]
    constructor
    · exact nat_address_injective (left := parent) (right := 1) (by omega) (by decide)
    · intro h
      rw [h]
  refine ⟨checks.next (fun fuel coins => execute_advance_up _ up fuel coins), ?_,
    ⟨?_, ?_, nextDest.trans pos.destWord⟩, nextMem.trans memory⟩
  · change (advancePrefix (afterAdvanceChecks state) 45 2).pc = _
    rw [nextPC]
    by_cases root : parent = 1
    · rw [if_pos (rootTest.mpr root), if_pos root]
    · rw [if_neg (fun h => root (rootTest.mp h)), if_neg root]
  · apply context_memory pos.context _ nextMem
    intro reg member
    have different : reg ≠ .x6 := by intro same; subst reg; simp at member
    exact up_reg _ reg different
  · change (advancePrefix (afterAdvanceChecks state) 45 2).getReg .x6 = _
    rw [nextNode]
    exact half

theorem advance_right_to_parent (groups : List Nat) (state : MachineState) (parent dest : Nat)
    (nonroot : 1 < parent) (bounded : 2 * parent + 1 < 512)
    (position : CapPosition groups state (2 * parent + 1) dest) (pc : state.pc = 0x1afc) :
    RunsOpeningBlock state (advanceUp state) 4 ∧
    (advanceUp state).pc = 0x1afc ∧
    CapPosition groups (advanceUp state) parent dest ∧
    (advanceUp state).mem = state.mem := by
  have ⟨ran, target, pos, memory⟩ := advance_climb groups state parent dest bounded position pc
  exact ⟨ran, by rw [target, if_neg (show ¬ parent = 1 by omega)], pos, memory⟩

/- V2b: V1's root exit through the `jal` at 707 (`advance_right_to_root`) is removed with
`GroupOpenCapAdvance.execute_advance_exit`; the V2b cap stage owns the walk. -/

end TwoPermutationPrototype.GroupedOpening
