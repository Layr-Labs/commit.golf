import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.CopyRefinement

/-! Data refinement of a register-parametric zero-offset digest copy.
Runtime access admission is separate. Source/destination registers survive the
load temporary; source separation is required only for the copied digest. -/
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

theorem cap_word_copy_memory_outside (source destination : Reg) (state : MachineState)
    (sourceStable : source ≠ .x6) (destinationStable : destination ≠ .x6)
    (address : Word)
    (outside : ∀ word : Fin 4,
      address ≠ state.getReg destination + BitVec.ofNat 64 (8*word.val)) :
    (capWordCopyPrefix source destination 0 0 state 8).getMem address =
      state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have h3 := outside ⟨3, by decide⟩
  simp at h0 h1 h2 h3
  simp [capWordCopyPrefix, capWordCopyInstructions, execInstrBr,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    store_register, store_memory, signExtend12,
    Ne.symm sourceStable, Ne.symm destinationStable, h0,h1,h2,h3]

theorem cap_word_copy_memory (source destination : Reg) (state : MachineState)
    (sourceStable : source ≠ .x6) (destinationStable : destination ≠ .x6)
    (separated : ∀ i j : Fin 4,
      state.getReg source + BitVec.ofNat 64 (8*i.val) ≠
        state.getReg destination + BitVec.ofNat 64 (8*j.val))
    (word : Fin 4) :
    (capWordCopyPrefix source destination 0 0 state 8).getMem
      (state.getReg destination + BitVec.ofNat 64 (8*word.val)) =
      state.getMem (state.getReg source + BitVec.ofNat 64 (8*word.val)) := by
  have h10 := separated ⟨1,by decide⟩ ⟨0,by decide⟩
  have h20 := separated ⟨2,by decide⟩ ⟨0,by decide⟩
  have h21 := separated ⟨2,by decide⟩ ⟨1,by decide⟩
  have h30 := separated ⟨3,by decide⟩ ⟨0,by decide⟩
  have h31 := separated ⟨3,by decide⟩ ⟨1,by decide⟩
  have h32 := separated ⟨3,by decide⟩ ⟨2,by decide⟩
  simp at h10 h20 h21 h30 h31 h32
  fin_cases word <;>
    simp [capWordCopyPrefix, capWordCopyInstructions, execInstrBr,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      store_register, store_memory, signExtend12, Ne.symm sourceStable,
      Ne.symm destinationStable, h10,h20,h21,h30,h31,h32]

theorem cap_word_copy_digest (sourceReg destinationReg : Reg) (state : MachineState)
    (sourceStable : sourceReg ≠ .x6) (destinationStable : destinationReg ≠ .x6)
    (source destination : Nat)
    (sourcePointer : state.getReg sourceReg = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg destinationReg = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (capWordCopyPrefix sourceReg destinationReg 0 0 state 8) destination 32 =
      readBuffer state source 32 := by
  apply (read_digest_eq_iff _ _ _ _ destinationAligned sourceAligned).mpr
  intro word inside
  have copied := cap_word_copy_memory sourceReg destinationReg state
    sourceStable destinationStable (by
      intro i j
      rw [sourcePointer, destinationPointer, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact separate_digest_words source destination i.val j.val
        sourceBound destinationBound i.isLt j.isLt separate) ⟨word,inside⟩
  simpa only [sourcePointer, destinationPointer, ← BitVec.ofNat_add] using copied

end CommitGolfCandidate
