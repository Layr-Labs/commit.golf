import CommitGolfCandidate.ChainedFieldFrame

/-! Derive native copy safety and access premises from non-wrapping pointer ranges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem copy_ahead_of_le (source destination count : Nat) (ordered : destination≤source)
    (fit : source+count<2^64) :
    CopyAhead (BitVec.ofNat 64 source) (BitVec.ofNat 64 destination) count := by
  intro index inside written before same
  have sourceFit : source+index<2^64 := by omega
  have destinationFit : destination+written<2^64 := by omega
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add] at same
  have numeric := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt sourceFit,Nat.mod_eq_of_lt destinationFit] at numeric
  omega

theorem byte_access_offset (base : Word) (index : Nat)
    (room : base.toNat+index+1≤MEMORY_BYTES) : accessValid (base+BitVec.ofNat 64 index) 1=true := by
  have fit : base.toNat+index<2^64 := by unfold MEMORY_BYTES at room; omega
  have indexFit : index<2^64 := by omega
  have address : (base+BitVec.ofNat 64 index).toNat=base.toNat+index := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexFit,Nat.mod_eq_of_lt fit]
  simp [accessValid,rangeValid,address,room]
  exact Nat.mod_one _

theorem low_copy_ready_of_access (n : Nat) (s : MachineState)
    (source : ∀ index, index<n → accessValid (s.getReg .x5+BitVec.ofNat 64 index) 1=true)
    (destination : ∀ index, index<n → accessValid (s.getReg .x6+BitVec.ofNat 64 index) 1=true) :
    LowCopyReady n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,?_,ih (byteCopyPrefix s 4) ?_ ?_⟩
    · simpa using source 0 (by omega)
    · simpa using destination 0 (by omega)
    · intro index inside
      rw [byte_copy_source,byte_offset_succ]
      exact source (index+1) (by omega)
    · intro index inside
      rw [byte_copy_destination,byte_offset_succ]
      exact destination (index+1) (by omega)

theorem field_build_access (n : Nat) (s : MachineState)
    (source : (s.getReg .x5).toNat+n+1≤MEMORY_BYTES)
    (destination : (s.getReg .x6).toNat+n≤MEMORY_BYTES)
    (scratch : (s.getReg .x7).toNat+2≤MEMORY_BYTES) :
    LowCopyReady n s ∧
      accessValid ((lowCopyState n s).getReg .x5) 1=true ∧
      accessValid ((lowCopyState n s).getReg .x7) 1=true ∧
      accessValid ((lowCopyState n s).getReg .x7+1) 1=true := by
  refine ⟨low_copy_ready_of_access n s ?_ ?_,?_,?_,?_⟩
  · intro index inside
    exact byte_access_offset _ index (by omega)
  · intro index inside
    exact byte_access_offset _ index (by omega)
  · rw [low_copy_source]
    exact byte_access_offset _ n source
  · rw [low_copy_frame _ _ .x7 (by decide) (by decide) (by decide)]
    simpa using byte_access_offset (s.getReg .x7) 0 (by omega)
  · rw [low_copy_frame _ _ .x7 (by decide) (by decide) (by decide)]
    exact byte_access_offset (s.getReg .x7) 1 scratch

end CommitGolfCandidate.Chained.Native
