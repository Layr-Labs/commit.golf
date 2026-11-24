import CommitGolfCandidate.ChainedCopyGeometry

/-! Raw-field construction preserves unread raw bytes under forward compaction geometry. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem word_of_nat_ne (left right : Nat) (leftFit : left<2^64) (rightFit : right<2^64)
    (different : left≠right) : BitVec.ofNat 64 left≠BitVec.ofNat 64 right := by
  intro same
  apply different
  have numeric := congrArg BitVec.toNat same
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt leftFit,Nat.mod_eq_of_lt rightFit] using numeric

theorem raw_field_tail_view (low padding rest : Proof) (high : List Bool)
    (s : MachineState) (base : Word)
    (memory : BytesAt s base (low++tailBitsWord 8 high::(padding++rest))) :
    BytesAt s (base+BitVec.ofNat 64 (low.length+1+padding.length)) rest := by
  intro index inside
  have data := memory (low.length+1+padding.length+index) (by simp only [List.length_append,List.length_cons]; omega)
  rw [List.getD_append_right low _ 0 _ (by omega)] at data
  have offset : low.length+1+padding.length+index-low.length=(padding.length+index)+1 := by omega
  rw [offset,List.getD_cons_succ,List.getD_append_right padding rest 0 _ (by omega),Nat.add_sub_cancel_left] at data
  simpa only [byte_offset_add] using data

theorem native_raw_field (low padding rest : Proof) (high : List Bool)
    (s : MachineState) (source destination scratch : Nat)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source)
    (destinationReg : s.getReg .x6=BitVec.ofNat 64 destination)
    (scratchReg : s.getReg .x7=BitVec.ofNat 64 scratch)
    (skip : s.getReg .x9=BitVec.ofNat 64 (1+padding.length))
    (width : s.getReg .x10=BitVec.ofNat 64 high.length)
    (memory : BytesAt s (BitVec.ofNat 64 source) (low++tailBitsWord 8 high::(padding++rest)))
    (ordered : destination≤source)
    (separate : source+low.length+1+padding.length+rest.length≤scratch)
    (room : scratch+2<2^64) :
    BytesAt (fieldBuildState low.length s) (BitVec.ofNat 64 destination) low ∧
    BytesAt (fieldBuildState low.length s) (BitVec.ofNat 64 scratch) (descriptorBytes [high]) ∧
    BytesAt (fieldBuildState low.length s)
      (BitVec.ofNat 64 (source+low.length+1+padding.length)) rest ∧
    (fieldBuildState low.length s).getReg .x5=BitVec.ofNat 64 (source+low.length+1+padding.length) ∧
    (fieldBuildState low.length s).getReg .x6=BitVec.ofNat 64 (destination+low.length) ∧
    (fieldBuildState low.length s).getReg .x7=BitVec.ofNat 64 (scratch+2) := by
  have body : BytesAt s (s.getReg .x5) low := by
    rw [sourceReg]
    exact ((bytes_at_append s _ low _).mp memory).1
  have ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length := by
    rw [sourceReg,destinationReg]
    exact copy_ahead_of_le source destination low.length ordered (by omega)
  have highValue : s.getByte (s.getReg .x5+BitVec.ofNat 64 low.length)=tailBitsWord 8 high := by
    rw [sourceReg]
    have data := memory low.length (by simp only [List.length_append,List.length_cons]; omega)
    rw [List.getD_append_right low (tailBitsWord 8 high::(padding++rest)) 0 low.length (by omega),Nat.sub_self] at data
    exact data
  have lowBody := native_field_low_body low s body ahead
  have lowApart : ∀ index, index<low.length →
      s.getReg .x6+BitVec.ofNat 64 index≠s.getReg .x7 ∧
      s.getReg .x6+BitVec.ofNat 64 index≠s.getReg .x7+1 := by
    intro index inside
    rw [destinationReg,scratchReg,←BitVec.ofNat_add]
    constructor
    · exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    · change BitVec.ofNat 64 (destination+index)≠BitVec.ofNat 64 scratch+BitVec.ofNat 64 1
      rw [←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  have lowResult := lowBody lowApart (by omega)
  rw [destinationReg] at lowResult
  have descriptor := native_field_descriptor low high s body ahead highValue width
  rw [scratchReg] at descriptor
  have unread := raw_field_tail_view low padding rest high s _ memory
  have nextSource : BitVec.ofNat 64 source+BitVec.ofNat 64 (low.length+1+padding.length)=
      BitVec.ofNat 64 (source+low.length+1+padding.length) := by rw [←BitVec.ofNat_add]; congr 1; omega
  rw [nextSource] at unread
  have restResult : BytesAt (fieldBuildState low.length s)
      (BitVec.ofNat 64 (source+low.length+1+padding.length)) rest := by
    apply native_field_preserves_bytes low rest s _ body ahead unread
    · intro index inside
      rw [scratchReg,←BitVec.ofNat_add]
      constructor
      · exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
      · change BitVec.ofNat 64 (source+low.length+1+padding.length+index)≠
          BitVec.ofNat 64 scratch+BitVec.ofNat 64 1
        rw [←BitVec.ofNat_add]
        exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    · intro index inside written before
      rw [destinationReg,←BitVec.ofNat_add,←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  refine ⟨lowResult,descriptor,restResult,?_,?_,?_⟩
  · rw [field_build_source,sourceReg,skip,←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  · rw [field_build_destination,destinationReg,←BitVec.ofNat_add]
  · rw [field_build_descriptor_pointer,scratchReg]
    change BitVec.ofNat 64 scratch+BitVec.ofNat 64 2=_
    rw [←BitVec.ofNat_add]

theorem compact_field_preserves_completed (low bytes : Proof) (s : MachineState)
    (source destination scratch base : Nat)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source)
    (destinationReg : s.getReg .x6=BitVec.ofNat 64 destination)
    (scratchReg : s.getReg .x7=BitVec.ofNat 64 scratch)
    (body : BytesAt s (s.getReg .x5) low) (memory : BytesAt s (BitVec.ofNat 64 base) bytes)
    (ordered : destination≤source) (sourceEnd : source+low.length<2^64)
    (outputEnd : destination+low.length≤scratch) (scratchEnd : scratch+2<2^64)
    (completed : base+bytes.length≤scratch)
    (apart : base+bytes.length≤destination ∨ destination+low.length≤base) :
    BytesAt (fieldBuildState low.length s) (BitVec.ofNat 64 base) bytes := by
  have ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length := by
    rw [sourceReg,destinationReg]
    exact copy_ahead_of_le source destination low.length ordered sourceEnd
  apply native_field_preserves_bytes low bytes s _ body ahead memory
  · intro index inside
    rw [scratchReg,←BitVec.ofNat_add]
    constructor
    · exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    · change BitVec.ofNat 64 (base+index)≠BitVec.ofNat 64 scratch+BitVec.ofNat 64 1
      rw [←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  · intro index inside written before
    rw [destinationReg,←BitVec.ofNat_add,←BitVec.ofNat_add]
    apply word_of_nat_ne _ _ (by omega) (by omega)
    rcases apart with left | right <;> omega

end CommitGolfCandidate.Chained.Native
