import CommitGolfCandidate.NonceBackwardReady
import CommitGolfCandidate.NonceCopyMemory

/-! Scratch high-to-low word-copy memory invariant for future proof expansion. -/
namespace CommitGolfCandidate.NonceBackwardMemory
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open NonceBackwardReady NonceCopyMemory
attribute [local irreducible] NonceWordCopy.copyPrefix

structure Preserved (source target count remaining : Nat)
    (reference state : MachineState) : Prop where
  copied : ∀ index, remaining ≤ index → index<count →
    state.getMem (address target index)=reference.getMem (address source index)
  frame : ∀ location, (∀ index, remaining ≤ index → index<count → location ≠ address target index) →
    state.getMem location=reference.getMem location

theorem initial_preserved (source target count : Nat) (state : MachineState) :
    Preserved source target count count state state := by
  constructor
  · intro index afterPrefix inside
    omega
  · intro location _
    rfl

theorem unread (entry : Word) (source target count remaining : Nat)
    (reference state : MachineState)
    (ready : Backward entry source target count remaining state)
    (preserved : Preserved source target count remaining reference state)
    (index : Nat) (beforeSuffix : index<remaining) (inside : index<count) :
    state.getMem (address source index)=reference.getMem (address source index) := by
  apply preserved.frame
  intro previous earlier bounded
  have ordered : source+8*index < target+8*previous := by
    have order:=ready.order
    omega
  exact address_ne ordered (address_small target count previous ready.target_window bounded)

theorem iteration_write (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Backward entry source target count (remaining+1) state) :
    (NonceWordCopy.copyPrefix true state 6).mem =
      (state.setMem (address target remaining) (state.getMem (address source remaining))).mem := by
  calc
    _ = (state.setMem (state.getReg .x25) (state.getMem (state.getReg .x23))).mem :=
      NonceWordCopy.iteration_memory true state
    _ = _ := by
      rw [ready.source, ready.target,
        show source+8*(remaining+1)-8=source+8*remaining by omega,
        show target+8*(remaining+1)-8=target+8*remaining by omega]
      rfl

theorem preserved_update (entry : Word) (source target count remaining : Nat)
    (reference state next : MachineState)
    (ready : Backward entry source target count (remaining+1) state)
    (preserved : Preserved source target count (remaining+1) reference state)
    (effect : next.mem=(state.setMem (address target remaining)
      (state.getMem (address source remaining))).mem) :
    Preserved source target count remaining reference next := by
  have rem:=ready.remaining_le
  have currentBound : remaining<count := by omega
  constructor
  · intro index afterSuffix inside
    have atWord := congrArg (fun memory : Word → Word => memory (address target index)) effect
    change next.getMem (address target index) =
      (state.setMem (address target remaining)
        (state.getMem (address source remaining))).getMem (address target index) at atWord
    rw [atWord]
    by_cases earlier : remaining+1 ≤ index
    · have different : address target index  ≠  address target remaining :=
        Ne.symm (address_ne (by omega) (address_small target count index ready.target_window inside))
      rw [MachineState.getMem_setMem_ne different]
      exact preserved.copied index earlier inside
    · have equal : index=remaining := by omega
      subst index
      rw [MachineState.getMem_setMem_eq]
      exact unread entry source target count (remaining+1) reference state ready preserved
        remaining (by omega) currentBound
  · intro location outside
    have atWord := congrArg (fun memory : Word → Word => memory location) effect
    change next.getMem location =
      (state.setMem (address target remaining)
        (state.getMem (address source remaining))).getMem location at atWord
    rw [atWord, MachineState.getMem_setMem_ne (outside remaining (by omega) currentBound)]
    apply preserved.frame
    intro index afterSuffix inside
    exact outside index (by omega) inside

theorem preserved_next (entry : Word) (source target count remaining : Nat)
    (reference state : MachineState)
    (ready : Backward entry source target count (remaining+1) state)
    (preserved : Preserved source target count (remaining+1) reference state) :
    Preserved source target count remaining reference (NonceWordCopy.copyPrefix true state 6) :=
  preserved_update entry source target count remaining reference state _ ready preserved
    (iteration_write entry source target count remaining state ready)

theorem loop_memory (entry : Word) (source target count : Nat) (state : MachineState)
    (ready : Backward entry source target count count state) :
    let final := capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) count state
    (∀ index<count, final.getMem (address target index)=state.getMem (address source index)) ∧
    (∀ location, (∀ index<count, location ≠ address target index) →
      final.getMem location=state.getMem location) := by
  have final := cap_counted_run_ready
    (fun current => NonceWordCopy.copyPrefix true current 6)
    (fun remaining current => Backward entry source target count remaining current ∧
      Preserved source target count remaining state current)
    (fun remaining current currentReady =>
      ⟨backward_next entry source target count remaining current currentReady.1,
       preserved_next entry source target count remaining state current currentReady.1 currentReady.2⟩)
    count state ⟨ready, initial_preserved source target count state⟩
  exact ⟨by simpa using final.2.copied, by simpa using final.2.frame⟩

end CommitGolfCandidate.NonceBackwardMemory
