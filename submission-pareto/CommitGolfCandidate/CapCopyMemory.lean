import CommitGolfCandidate.CapDigestCopy
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.CapMemoryFrame

/-! Boundary-copy refinement for the two directions of the cap codec. Runtime
admission is proved separately. Source separation here ensures later loads
still see the original digest; the outside-word frame needs no such premise. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem store_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem store_memory (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query =
      if query = address then value else state.getMem query := by
  simp [MachineState.getMem, MachineState.setMem]

/-- Only the four destination words can change, even for overlapping buffers. -/
theorem cap_copy_memory_outside (checking : Bool) (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4,
      address ≠ state.getReg (capCopyDestination checking) +
        BitVec.ofNat 64 (8 * word.val)) :
    (capDigestCopyPrefix checking state 8).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have h3 := outside ⟨3, by decide⟩
  cases checking <;>
    simp [capCopyDestination] at h0 h1 h2 h3 <;>
    simp [capDigestCopyPrefix, capDigestCopyInstructions, capCopySource,
      capCopyDestination, execInstrBr, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, store_register, store_memory, signExtend12,
      h0, h1, h2, h3]

/-- All copied words equal their original source words when the buffers separate. -/
theorem cap_copy_memory (checking : Bool) (state : MachineState)
    (separated : ∀ source destination : Fin 4,
      state.getReg (capCopySource checking) + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg (capCopyDestination checking) +
          BitVec.ofNat 64 (8 * destination.val)) (word : Fin 4) :
    (capDigestCopyPrefix checking state 8).getMem
        (state.getReg (capCopyDestination checking) + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg (capCopySource checking) +
        BitVec.ofNat 64 (8 * word.val)) := by
  have h10 := separated ⟨1, by decide⟩ ⟨0, by decide⟩
  have h20 := separated ⟨2, by decide⟩ ⟨0, by decide⟩
  have h21 := separated ⟨2, by decide⟩ ⟨1, by decide⟩
  have h30 := separated ⟨3, by decide⟩ ⟨0, by decide⟩
  have h31 := separated ⟨3, by decide⟩ ⟨1, by decide⟩
  have h32 := separated ⟨3, by decide⟩ ⟨2, by decide⟩
  cases checking <;>
    simp [capCopySource, capCopyDestination] at h10 h20 h21 h30 h31 h32 <;>
    fin_cases word <;>
    simp [capDigestCopyPrefix, capDigestCopyInstructions, capCopySource,
      capCopyDestination, execInstrBr, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, store_register, signExtend12,
      h10, h20, h21, h30, h31, h32]

/-- The complete 32-byte destination reproduces the original source digest. -/
theorem cap_copy_digest (checking : Bool) (state : MachineState)
    (source destination : Nat)
    (sourcePointer : state.getReg (capCopySource checking) = BitVec.ofNat 64 source)
    (destinationPointer :
      state.getReg (capCopyDestination checking) = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source + 32 ≤ 2^64) (destinationBound : destination + 32 ≤ 2^64)
    (separate : source + 32 ≤ destination ∨ destination + 32 ≤ source) :
    readBuffer (capDigestCopyPrefix checking state 8) destination 32 =
      readBuffer state source 32 := by
  apply (read_digest_eq_iff _ _ _ _ destinationAligned sourceAligned).mpr
  intro word inside
  have copied := cap_copy_memory checking state (by
    intro i j
    rw [sourcePointer, destinationPointer, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact separate_digest_words source destination i.val j.val sourceBound destinationBound
      i.isLt j.isLt separate) ⟨word, inside⟩
  simpa only [sourcePointer, destinationPointer, ← BitVec.ofNat_add] using copied

/-- A separate digest remains unchanged, independent of all loaded contents. -/
theorem cap_copy_preserves_digest (checking : Bool) (state : MachineState)
    (destination address : Nat)
    (destinationPointer :
      state.getReg (capCopyDestination checking) = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 32 ≤ 2^64) (readBound : address + 32 ≤ 2^64)
    (separate : address + 32 ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer (capDigestCopyPrefix checking state 8) address 32 =
      readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply cap_copy_memory_outside
  intro j
  rw [destinationPointer, ← BitVec.ofNat_add]
  exact separate_digest_words address destination i j.val readBound destinationBound
    hi j.isLt separate

end CommitGolfCandidate
