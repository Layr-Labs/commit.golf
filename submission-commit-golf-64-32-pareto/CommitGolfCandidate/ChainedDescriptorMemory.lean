import CommitGolfCandidate.ChainedPacketDescriptors
import CommitGolfCandidate.ChainedTailBuffer

/-! Byte-addressed record/footer descriptor and output memory interfaces. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

def BytesAt (s : MachineState) (base : Word) (bytes : Proof) : Prop :=
  ∀ index, index<bytes.length → s.getByte (base+BitVec.ofNat 64 index)=bytes.getD index 0

theorem byte_offset_add (base : Word) (first second : Nat) :
    (base+BitVec.ofNat 64 first)+BitVec.ofNat 64 second=base+BitVec.ofNat 64 (first+second) := by
  rw [BitVec.add_assoc,BitVec.ofNat_add]

theorem bytes_at_append (s : MachineState) (base : Word) (front back : Proof) :
    BytesAt s base (front++back) ↔ BytesAt s base front ∧ BytesAt s (base+BitVec.ofNat 64 front.length) back := by
  constructor
  · intro memory
    constructor
    · intro index inside
      have data := memory index (by simp only [List.length_append]; omega)
      rwa [List.getD_append front back 0 index inside] at data
    · intro index inside
      have data := memory (front.length+index) (by simp only [List.length_append]; omega)
      rw [List.getD_append_right front back 0 (front.length+index) (by omega),Nat.add_sub_cancel_left] at data
      simpa only [byte_offset_add] using data
  · rintro ⟨frontMemory,backMemory⟩ index inside
    by_cases before : index<front.length
    · rw [List.getD_append front back 0 index before]
      exact frontMemory index before
    · rw [List.getD_append_right front back 0 index (by omega)]
      have data := backMemory (index-front.length) (by simp only [List.length_append] at inside; omega)
      rw [byte_offset_add,show front.length+(index-front.length)=index by omega] at data
      exact data

theorem descriptor_memory_slot (s : MachineState) (base : Word) (rows : List (List Bool))
    (memory : BytesAt s base (descriptorBytes rows)) (index : Nat) (inside : index<rows.length)
    (cursor : s.getReg .x21=base+BitVec.ofNat 64 (2*index)) :
    s.getByte (s.getReg .x21)=tailBitsWord 8 (rows.getD index []) ∧
    s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 (rows.getD index []).length := by
  constructor
  · rw [cursor]
    exact (memory (2*index) (by rw [descriptor_bytes_length]; omega)).trans (descriptor_value rows index inside)
  · rw [cursor]
    change s.getByte ((base+BitVec.ofNat 64 (2*index))+BitVec.ofNat 64 1)=_
    rw [byte_offset_add]
    exact (memory (2*index+1) (by rw [descriptor_bytes_length]; omega)).trans (descriptor_width rows index inside)

theorem descriptor_native_load (s : MachineState) (base : Word) (rows : List (List Bool))
    (memory : BytesAt s base (descriptorBytes rows)) (index : Nat) (inside : index<rows.length)
    (cursor : s.getReg .x21=base+BitVec.ofNat 64 (2*index))
    (small : (rows.getD index []).length≤6) :
    (tailLoadPrefix s 3).getReg .x24=tailBitsWord 64 (rows.getD index []) ∧
    (tailLoadPrefix s 3).getReg .x26=BitVec.ofNat 64 (rows.getD index []).length := by
  have data := descriptor_memory_slot s base rows memory index inside cursor
  exact tail_load_field_bits s _ small data.1 data.2

def SegmentsAt (s : MachineState) : Word → List Proof → Prop
  | _,[] => True
  | base,chunk::rest => BytesAt s base chunk ∧ SegmentsAt s (base+BitVec.ofNat 64 chunk.length) rest

theorem segments_at_flatten (s : MachineState) (base : Word) (chunks : List Proof) :
    SegmentsAt s base chunks ↔ BytesAt s base chunks.flatten := by
  induction chunks generalizing base with
  | nil => simp [SegmentsAt,BytesAt]
  | cons chunk chunks ih =>
    rw [SegmentsAt,List.flatten_cons,bytes_at_append,ih]

def payloadSegments {spec : Spec} (payload : Payload spec) : List Proof :=
  [lowBytes payload,packedBits (highRows payload).flatten]

theorem payload_segments_encode {spec : Spec} (payload : Payload spec)
    (aligned : ∀ field ∈ spec, field.1%8=0) : (payloadSegments payload).flatten=encode payload := by
  simpa [payloadSegments] using (encode_descriptors payload aligned).symm

def openingSegments (positions : Positions) (records : List InteriorCodec.Record) (footer : InteriorCodec.Footer positions) :
    List Proof := records.flatMap payloadSegments++payloadSegments footer

theorem opening_segments_encode (positions : Positions) (records : List InteriorCodec.Record)
    (footer : InteriorCodec.Footer positions) :
    (openingSegments positions records footer).flatten=InteriorCodec.encodeOpening positions records footer := by
  have recordData : ∀ record : InteriorCodec.Record, (payloadSegments record).flatten=encode record := by
    intro record
    simpa [payloadSegments] using (record_descriptor_encoding record).symm
  have footerData : (payloadSegments footer).flatten=encode footer := by
    simpa [payloadSegments] using (footer_descriptor_encoding _ footer).symm
  unfold openingSegments InteriorCodec.encodeOpening
  rw [List.flatten_append,footerData]
  congr 1
  induction records with
  | nil => rfl
  | cons record records ih =>
    simp only [List.flatMap_cons,List.flatten_append,recordData,ih]

theorem opening_memory_encode (s : MachineState) (base : Word) (positions : Positions)
    (records : List InteriorCodec.Record) (footer : InteriorCodec.Footer positions) :
    SegmentsAt s base (openingSegments positions records footer) ↔
      BytesAt s base (InteriorCodec.encodeOpening positions records footer) := by
  rw [segments_at_flatten,opening_segments_encode]

end CommitGolfCandidate.Chained.Native
