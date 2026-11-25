import CommitGolfCandidate.NonceCopyReady

/-! Scratch word-memory invariant for an in-place forward proof compactor. -/
namespace CommitGolfCandidate.NonceCopyMemory
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open NonceCopyReady
attribute [local irreducible] NonceWordCopy.copyPrefix

def address (base index : Nat) : Word := BitVec.ofNat 64 (base+8*index)

theorem address_ne {left right : Nat} (ordered : left<right) (small : right<2^64) :
    (BitVec.ofNat 64 left : Word) ≠ BitVec.ofNat 64 right := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (by omega : left<2^64)] at numeric
  omega

theorem address_small (base count index : Nat) (window : base+8*count ≤ MEMORY_BYTES)
    (inside : index<count) : base+8*index<2^64 := by
  norm_num [MEMORY_BYTES] at window
  omega

structure Preserved (source target count remaining : Nat)
    (reference state : MachineState) : Prop where
  copied : ∀ index<count-remaining,
    state.getMem (address target index)=reference.getMem (address source index)
  frame : ∀ location, (∀ index<count-remaining, location≠address target index) →
    state.getMem location=reference.getMem location

theorem initial_preserved (source target count : Nat) (state : MachineState) :
    Preserved source target count count state state := by
  constructor
  · intro index inside
    omega
  · intro location _
    rfl

theorem unread (entry : Word) (source target count remaining : Nat)
    (reference state : MachineState)
    (ready : Forward entry source target count remaining state)
    (preserved : Preserved source target count remaining reference state)
    (index : Nat) (afterPrefix : count-remaining ≤ index) (inside : index<count) :
    state.getMem (address source index)=reference.getMem (address source index) := by
  apply preserved.frame
  intro previous earlier
  have ordered : target+8*previous < source+8*index := by
    have ordering := ready.source_le
    omega
  exact Ne.symm (address_ne ordered (address_small source count index ready.source_window inside))

theorem iteration_write (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Forward entry source target count (remaining+1) state) :
    (NonceWordCopy.copyPrefix false state 6).mem =
      (state.setMem (address target (count-(remaining+1)))
        (state.getMem (address source (count-(remaining+1))))).mem := by
  calc
    _ = (state.setMem (state.getReg .x25) (state.getMem (state.getReg .x23))).mem :=
      NonceWordCopy.iteration_memory false state
    _ = _ := by rw [ready.source, ready.target]; rfl

theorem preserved_update (entry : Word) (source target count remaining : Nat)
    (reference state next : MachineState)
    (ready : Forward entry source target count (remaining+1) state)
    (preserved : Preserved source target count (remaining+1) reference state)
    (effect : next.mem=(state.setMem (address target (count-(remaining+1)))
      (state.getMem (address source (count-(remaining+1))))).mem) :
    Preserved source target count remaining reference next := by
  have rem := ready.remaining_le
  have currentBound : count-(remaining+1)<count := by omega
  have nextPrefix : count-remaining=count-(remaining+1)+1 := by omega
  constructor
  · intro index inside
    have atWord := congrArg (fun memory : Word → Word => memory (address target index)) effect
    change next.getMem (address target index) =
      (state.setMem (address target (count-(remaining+1)))
        (state.getMem (address source (count-(remaining+1))))).getMem (address target index) at atWord
    rw [atWord]
    by_cases earlier : index<count-(remaining+1)
    · have different : address target index ≠ address target (count-(remaining+1)) :=
        address_ne (by omega) (address_small target count _ ready.target_window currentBound)
      rw [MachineState.getMem_setMem_ne different]
      exact preserved.copied index earlier
    · have equal : index=count-(remaining+1) := by omega
      subst index
      rw [MachineState.getMem_setMem_eq]
      exact unread entry source target count (remaining+1) reference state ready preserved
        _ (by omega) currentBound
  · intro location outside
    have atWord := congrArg (fun memory : Word → Word => memory location) effect
    change next.getMem location =
      (state.setMem (address target (count-(remaining+1)))
        (state.getMem (address source (count-(remaining+1))))).getMem location at atWord
    rw [atWord, MachineState.getMem_setMem_ne (outside _ (by omega))]
    apply preserved.frame
    intro index inside
    exact outside index (by omega)

theorem preserved_next (entry : Word) (source target count remaining : Nat)
    (reference state : MachineState)
    (ready : Forward entry source target count (remaining+1) state)
    (preserved : Preserved source target count (remaining+1) reference state) :
    Preserved source target count remaining reference (NonceWordCopy.copyPrefix false state 6) :=
  preserved_update entry source target count remaining reference state _ ready preserved
    (iteration_write entry source target count remaining state ready)

theorem loop_memory (entry : Word) (source target count : Nat) (state : MachineState)
    (ready : Forward entry source target count count state) :
    let final := capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) count state
    (∀ index<count, final.getMem (address target index)=state.getMem (address source index)) ∧
    (∀ location, (∀ index<count, location≠address target index) →
      final.getMem location=state.getMem location) := by
  have final := cap_counted_run_ready
    (fun current => NonceWordCopy.copyPrefix false current 6)
    (fun remaining current => Forward entry source target count remaining current ∧
      Preserved source target count remaining state current)
    (fun remaining current currentReady =>
      ⟨forward_next entry source target count remaining current currentReady.1,
       preserved_next entry source target count remaining state current currentReady.1 currentReady.2⟩)
    count state ⟨ready, initial_preserved source target count state⟩
  exact ⟨by simpa using final.2.copied, by simpa using final.2.frame⟩

end CommitGolfCandidate.NonceCopyMemory
