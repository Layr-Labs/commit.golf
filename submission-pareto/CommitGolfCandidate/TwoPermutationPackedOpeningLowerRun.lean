import CommitGolfCandidate.TwoPermutationPackedOpeningNonceRun

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (proofBase)

def lowerRun (level : Nat) : Nat → MachineState → MachineState
  | 0, state => state
  | left+1, state =>
    if live : level < 16 then lowerRun (level+1) left (siblingBlock ⟨level,live⟩ state) else state

def lowerCost (level : Nat) : Nat → Nat
  | 0 => 0
  | left+1 => 5+copyWidth level+lowerCost (level+1) left

theorem lower_total_cost : lowerCost 0 16 = 562 := rfl

theorem destination_mono (ordinal : Nat) : Monotone (siblingDestination ordinal) := by
  apply monotone_nat_of_le_succ
  intro level
  unfold siblingDestination
  rw [sibling_offset_next]
  omega

theorem field_outside {before after : MachineState} {source dest size : Nat}
    (copy : ByteCopy before after source dest size) (address : Nat)
    (fit : address < 2^64) (endFit : dest+size ≤ 2^64)
    (outside : address < dest ∨ dest+size ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  apply copy.frame
  intro i inside equal
  have same := Opening.nat_address_injective fit (by omega) equal
  omega

/-- End of the bytes touched by `count` sibling copies from `first`. Only a lone
leaf-level copy reaches two bytes past the next level's destination. -/
def lowerReach (ordinal first count : Nat) : Nat :=
  siblingDestination ordinal (first+count) + (if first = 0 ∧ count = 1 then 2 else 0)

structure LowerTrace (before after : MachineState) (index : Index) (ordinal first count : Nat) : Prop where
  run : RunsOpeningBlock before after (lowerCost first count)
  next : LowerCursor after index ordinal (first+count)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 →
    after.getReg reg = before.getReg reg
  input : ∀ address < proofBase,
    after.getMem (BitVec.ofNat 64 address) = before.getMem (BitVec.ofNat 64 address)
  frame : ∀ address < 2^64,
    address < siblingDestination ordinal first ∨ lowerReach ordinal first count ≤ address →
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address)
  fields : ∀ level, first ≤ level → level < first+count → ∀ byte < siblingWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      before.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))

theorem execute_lower (state : MachineState) (index : Index) (ordinal first count : Nat)
    (ordinalBound : ordinal < LENGTH) (limit : first+count ≤ 16)
    (cursor : LowerCursor state index ordinal first) :
    LowerTrace state (lowerRun first count state) index ordinal first count := by
  induction count generalizing first state with
  | zero =>
    refine ⟨?_, by simpa only [lowerRun, Nat.add_zero] using cursor, ?_, ?_, ?_, ?_⟩
    · intro fuel coins
      simp [lowerCost, lowerRun, Execution.charge]
    · intros
      rfl
    · intros
      rfl
    · intro address _ outside
      rfl
    · intro level lower upper
      omega
  | succ count ih =>
    have live : first < 16 := by omega
    let level : Fin 16 := ⟨first,live⟩
    let middle := siblingBlock level state
    have step := execute_sibling state index ordinal ordinalBound level cursor
    have rest := ih middle (first+1) (by omega) step.next
    have total : first+(count+1) = first+1+count := by omega
    have width : siblingDestination ordinal (first+1) =
        siblingDestination ordinal first+30 := by
      simp only [siblingDestination, siblingOffset]
      omega
    have levels := destination_mono ordinal
    have endFit := all_record_ends_fit ordinal ordinalBound
    have within (l : Nat) (hl : l ≤ 16) : siblingDestination ordinal l ≤ MEMORY_BYTES := by
      exact (levels hl).trans ((record_end ordinal).le.trans endFit)
    have ram : MEMORY_BYTES < 2^64 := by decide
    have writeEnd := (all_sibling_copies_fit index ordinal first ordinalBound live).2.2.2
    have writeFit : siblingDestination ordinal first+copyWidth first ≤ 2^64 := by omega
    have data : ByteCopy state middle (siblingAddress index first) (siblingDestination ordinal first)
        (copyWidth first) := step.bytes
    simp only [lowerRun, dite_eq_left live]
    refine ⟨step.run.next rest.run, by rw [total]; exact rest.next,
      fun reg a b c d => (rest.register reg a b c d).trans (step.register reg a b c d),
      fun address below => (rest.input address below).trans (step.input address below), ?_, ?_⟩
    · intro address fit outside
      have dests (l : Nat) : siblingDestination ordinal l = recordBase ordinal+(16+30*l) := rfl
      have restFrame := rest.frame address fit
      have copyFrame := field_outside data address fit writeFit
      have reachRest : lowerReach ordinal (first+1) count = recordBase ordinal+(16+30*(first+1+count)) := by
        simp [lowerReach, dests]
      have reachHere : lowerReach ordinal first (count+1) =
          recordBase ordinal+(16+30*(first+(count+1))) + (if first = 0 ∧ count = 0 then 2 else 0) := by
        simp [lowerReach, dests]
      have widthHere : copyWidth first = if first = 0 then 32 else 30 := rfl
      rw [reachRest] at restFrame
      rw [reachHere] at outside
      rw [widthHere] at copyFrame
      simp only [dests] at outside restFrame copyFrame
      apply (restFrame ?_).trans (copyFrame ?_) <;> split_ifs at * <;> omega
    · intro l low hi byte valid
      by_cases initial : l = first
      · subst l
        have left : siblingDestination ordinal first+byte < siblingDestination ordinal (first+1) := by
          have w : siblingWidth first = 30 := rfl
          simp only [siblingDestination, siblingOffset]
          omega
        have wide : 30 ≤ copyWidth first := by unfold copyWidth; split <;> omega
        have w : siblingWidth first = 30 := rfl
        exact (rest.frame _ (by omega) (Or.inl left)).trans
          (data.copied byte (by unfold siblingWidth at valid; unfold copyWidth; split <;> omega))
      · have later := rest.fields l (by omega) (by omega) byte valid
        have srcFit := (all_sibling_copies_fit index ordinal l ordinalBound (by omega)).2.2.1
        have inputBefore : siblingAddress index l+byte < siblingDestination ordinal first := by
          have srcBound := Opening.lower_swap_bound index l
          have heapEnd := Opening.heap_before_nonces
          have nonceEnd := Opening.nonces_end_at_indices
          have order := Opening.indices_before_records
          have small : siblingWidth l ≤ 32 := by unfold siblingWidth; decide
          unfold siblingAddress siblingDestination recordBase
          omega
        exact later.trans (field_outside data _ (by omega) writeFit (Or.inl inputBefore))

end TwoPermutationPrototype.PackedOpening
