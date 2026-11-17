import CommitGolfCandidate.TwoPermutationOpeningSiblingStep
import CommitGolfCandidate.TwoPermutationOpeningFootprint

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem lower_pc_set (s : MachineState) (pc : Word) :
    (s.setPC pc).pc = pc := rfl

@[local simp] private theorem lower_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl

theorem sibling_control (state : MachineState) (level : Nat) :
    let after := siblingPrefix state level 12
    after.getReg .x9 = state.getReg .x9 ∧
    after.getReg .x21 = state.getReg .x21 ∧
    after.getReg .x6 = state.getReg .x6 >>> 1 := by
  simp [siblingPrefix, siblingInstructions, execInstrBr, signExtend12]

theorem sibling_address (state : MachineState) (node : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (value : state.getReg .x6 = BitVec.ofNat 64 node) :
    siblingSource state = BitVec.ofNat 64 (trapdoorBase + 32 * (node ^^^ 1)) := by
  rw [siblingSource, base, value]
  rw [← BitVec.ofNat_xor, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 trapdoorBase + BitVec.ofNat 64 (node ^^^ 1) * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (node ^^^ 1)]

/-- State of the lower loop after completing the indicated number of levels. -/
structure LowerControl (state : MachineState) (index : Index) (ordinal level : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096 + 4*(38 + 12*level))
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  destination : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  node : state.getReg .x6 = BitVec.ofNat 64 (lowerNode index level)

theorem sibling_target (state : MachineState) (index : Index) (ordinal level : Nat)
    (h : LowerControl state index ordinal level) :
    siblingDestWord state level = BitVec.ofNat 64 (siblingDest ordinal level) := by
  rw [siblingDestWord, h.destination, ← BitVec.ofNat_add]
  congr 1
  unfold siblingDest
  omega

attribute [local irreducible] siblingPrefix execute

theorem lower_control_next (state : MachineState) (index : Index) (ordinal level : Nat)
    (inside : level < 16) (control : LowerControl state index ordinal level) :
    LowerControl (siblingPrefix state level 12) index ordinal (level + 1) := by
  have post := sibling_control state level
  refine ⟨?_, post.1.trans control.heap, ?_, ?_⟩
  · rw [sibling_pc _ _ _ (by decide), control.pc, ← BitVec.ofNat_add]
    congr 1
  · exact post.2.1.trans control.destination
  · rw [post.2.2, control.node, lower_node_next]
    apply BitVec.eq_of_toNat_eq
    have left : lowerNode index level < 2 ^ 64 :=
      (lower_node_bound _ _).trans (by decide)
    have right : lowerNode index level / 2 < 2 ^ 64 := (Nat.div_le_self _ _).trans_lt left
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt left, Nat.mod_eq_of_lt right]

/-- Every real sibling step on an admitted record has valid heap and output addresses. -/
theorem execute_lower_level (state : MachineState) (index : Index)
    (ordinal level fuel : Nat) (allowCoins : Bool) (ordinalBound : ordinal < LENGTH)
    (inside : level < 16) (control : LowerControl state index ordinal level) :
    execute openingImage (12 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (siblingPrefix state level 12) allowCoins
          return result.charge 12 0) := by
  have src := sibling_address state (lowerNode index level) control.heap control.node
  have ⟨srcAligned, dstAligned, separated, fits⟩ :=
    ordinal_sibling_geometry index ordinal level ordinalBound inside
  apply execute_sibling _ ⟨level, inside⟩ control.pc
  · intro j
    rw [src, word_at]
    have small := j.isLt
    apply aligned_access _ (by omega) (by omega)
  · intro j
    rw [sibling_target _ _ _ _ control, word_at]
    have small := j.isLt
    apply aligned_access _ (by omega) (by omega)

def lowerPathMachine (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => lowerPathMachine (siblingPrefix state (15 - remaining) 12) remaining

theorem lower_path_control (state : MachineState) (index : Index) (ordinal level remaining : Nat)
    (final : level + remaining = 16) (control : LowerControl state index ordinal level) :
    LowerControl (lowerPathMachine state remaining) index ordinal 16 := by
  induction remaining generalizing state level with
  | zero =>
    have done : level = 16 := by omega
    subst level
    exact control
  | succ remaining ih =>
    simp only [lowerPathMachine, show 15 - remaining = level by omega]
    apply ih _ (level + 1) (by omega)
    exact lower_control_next state index ordinal level (by omega) control

/-- Starting at the first sibling, the concrete loop executes 208 instructions. -/
theorem execute_lower_path (state : MachineState) (index : Index)
    (ordinal level remaining fuel : Nat) (allowCoins : Bool)
    (ordinalBound : ordinal < LENGTH) (final : level + remaining = 16)
    (control : LowerControl state index ordinal level) :
    execute openingImage (12 * remaining + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (lowerPathMachine state remaining) allowCoins
          return result.charge (12 * remaining) 0) := by
  induction remaining generalizing state level with
  | zero => simp [lowerPathMachine, Execution.charge]
  | succ remaining ih =>
    have one := execute_lower_level state index ordinal level (12 * remaining + fuel)
      allowCoins ordinalBound (by omega) control
    have next := lower_control_next state index ordinal level (by omega) control
    rw [show 12 * (remaining + 1) + fuel = 12 + (12 * remaining + fuel) by omega,
      one, ih _ (level + 1) (by omega) next]
    simp [lowerPathMachine, show 15 - remaining = level by omega, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 12]

end TwoPermutationPrototype.Opening
