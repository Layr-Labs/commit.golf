import CommitGolfCandidate.ChainedByteWriteView

/-! Native tail traversal preserves the low body and finishes the exact payload. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

theorem native_payload_bytes_at {spec : Spec} (payload : Payload spec) (s : MachineState) (base : Word)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6)
    (buffer : TailBuffer s []) (cursor : s.getReg .x20=base+BitVec.ofNat 64 (lowBytes payload).length)
    (body : BytesAt s base (lowBytes payload))
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows payload)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows payload))
    (fit : (encode payload).length<2^64) :
    BytesAt (tailFinishState (tailFieldsState spec.length s)) base (encode payload) := by
  have encoding : encode payload=lowBytes payload++packedBits (highs payload) := by
    simpa only [high_rows_flatten] using encode_descriptors payload aligned
  have total : (lowBytes payload).length+(packedBits (highs payload)).length<2^64 := by
    rwa [encoding,List.length_append] at fit
  rw [encoding,bytes_at_append]
  constructor
  · intro index inside
    rw [native_descriptor_memory payload s buffer small memory apart]
    rw [write_byte_list_preserves]
    · exact body index inside
    · intro offset bounded same
      rw [cursor,byte_offset_add] at same
      have equal := byte_offset_inj base index ((lowBytes payload).length+offset) (by omega) (by omega) same
      omega
  · have tailView := native_tail_bytes_at (highRows payload) [] s buffer
      (high_rows_small payload small) memory apart (by simpa only [List.nil_append,high_rows_flatten] using
        (show (packedBits (highs payload)).length<2^64 by omega))
    simpa only [high_rows_length,List.nil_append,high_rows_flatten,cursor] using tailView

theorem native_record_bytes_at (record : InteriorCodec.Record) (s : MachineState) (base : Word)
    (buffer : TailBuffer s []) (cursor : s.getReg .x20=base+479#64)
    (body : BytesAt s base (lowBytes record))
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows record)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows record)) :
    BytesAt (tailFinishState (tailFieldsState 17 s)) base (encode record) := by
  have location : s.getReg .x20=base+BitVec.ofNat 64 (lowBytes record).length := by
    simpa only [(record_descriptor_sizes record).1] using cursor
  have fit : (encode record).length<2^64 := by
    rw [InteriorCodec.encode_record_length]
    decide
  exact native_payload_bytes_at record s base (by decide +kernel) (by decide +kernel) buffer location body memory apart fit

theorem native_footer_bytes_at (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (base : Word) (buffer : TailBuffer s [])
    (cursor : s.getReg .x20=base+BitVec.ofNat 64 (29*nodes.length))
    (body : BytesAt s base (lowBytes footer))
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (highRows footer)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows footer)) (fit : (encode footer).length<2^64) :
    BytesAt (tailFinishState (tailFieldsState nodes.length s)) base (encode footer) := by
  have aligned : ∀ field ∈ InteriorCodec.footerSpec nodes, field.1%8=0 := by
    intro field member
    obtain ⟨node,_,same⟩ := List.mem_map.mp member
    subst field
    change 232%8=0
    decide
  have small : ∀ field ∈ InteriorCodec.footerSpec nodes, field.2≤6 := by
    intro field member
    obtain ⟨node,_,same⟩ := List.mem_map.mp member
    subst field
    change InteriorCodec.footerWidth node-232≤6
    unfold InteriorCodec.footerWidth
    split <;> omega
  have location : s.getReg .x20=base+BitVec.ofNat 64 (lowBytes footer).length := by
    simpa only [footer_low_bytes_length] using cursor
  have result := native_payload_bytes_at footer s base aligned small buffer location body memory apart fit
  simpa only [InteriorCodec.footerSpec,List.length_map] using result

end CommitGolfCandidate.Chained.Native
