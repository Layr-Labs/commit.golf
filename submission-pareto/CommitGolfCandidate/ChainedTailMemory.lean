import CommitGolfCandidate.ChainedTailPacking

/-! Complete native tail output, including final padding, agrees byte-for-byte. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem write_byte_list_append (memory : Word → BitVec 8) (base : Word) (front back : Proof) :
    writeByteList memory base (front++back)=
      writeByteList (writeByteList memory base front) (base+BitVec.ofNat 64 front.length) back := by
  induction front generalizing memory base with
  | nil => simp [writeByteList]
  | cons byte front ih =>
    change writeByteList (storeByteFn memory base byte) (base+1) (front++back)=_
    rw [ih]
    have location : (base+1)+BitVec.ofNat 64 front.length=base+BitVec.ofNat 64 (byte::front).length := by
      change (base+BitVec.ofNat 64 1)+BitVec.ofNat 64 front.length=_
      rw [byte_offset_add,Nat.add_comm 1]
      rfl
    rw [location]
    rfl

theorem native_tail_memory (rows : List (List Bool)) (front : List Bool) (s : MachineState)
    (buffer : TailBuffer s front) (small : ∀ row ∈ rows, row.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes rows))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) rows) (query : Word) :
    (tailFinishState (tailFieldsState rows.length s)).getByte query=
      writeByteList s.getByte (s.getReg .x20) (packedBits (front++rows.flatten)) query := by
  obtain ⟨finalBuffer,finalMemory,finalPointer⟩ := native_tail_plan rows front s buffer small memory apart
  rw [←tail_plan_packed rows front buffer.pending small,write_byte_list_append,
    tail_finish_bits_byte _ _ finalBuffer.value finalBuffer.count finalBuffer.pending]
  by_cases empty : (tailPlanCarry front rows).length=0
  · rw [ite_eq_left empty,finishTailBytes,ite_eq_left empty]
    exact finalMemory query
  · rw [ite_eq_right empty,finishTailBytes,ite_eq_right empty]
    change (if query=(tailFieldsState rows.length s).getReg .x20 then _ else _)=
      storeByteFn _ _ _ query
    rw [finalPointer,finalMemory]
    rfl

theorem native_descriptor_memory {spec : SplitCodec.Spec} (payload : SplitCodec.Payload spec) (s : MachineState)
    (buffer : TailBuffer s []) (small : ∀ field ∈ spec, field.2≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows payload)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows payload)) (query : Word) :
    (tailFinishState (tailFieldsState spec.length s)).getByte query=
      writeByteList s.getByte (s.getReg .x20) (packedBits (SplitCodec.highs payload)) query := by
  have result := native_tail_memory (highRows payload) [] s buffer (high_rows_small payload small) memory apart query
  simpa only [high_rows_length,List.nil_append,high_rows_flatten] using result

theorem native_record_tail_memory (record : InteriorCodec.Record) (s : MachineState) (buffer : TailBuffer s [])
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows record)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows record)) (query : Word) :
    (tailFinishState (tailFieldsState 17 s)).getByte query=
      writeByteList s.getByte (s.getReg .x20) (packedBits (SplitCodec.highs record)) query := by
  exact native_descriptor_memory record s buffer (by decide +kernel) memory apart query

end CommitGolfCandidate.Chained.Native
