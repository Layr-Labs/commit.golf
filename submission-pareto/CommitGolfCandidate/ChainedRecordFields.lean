import CommitGolfCandidate.ChainedPayloadFields

/-! Record/footer native construction plans have the delivered raw source strides. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

def recordSourcePads : List Proof := [[],[0,0]]
theorem record_fields_small : ∀ field ∈ InteriorCodec.recordSpec, field.2≤6 := by decide +kernel
theorem record_pads_small : ∀ pad ∈ recordSourcePads, pad.length≤2 := by decide

def recordRawFields (record : InteriorCodec.Record) : List RawField :=
  payloadRawFields record recordSourcePads record_fields_small record_pads_small

theorem record_raw_fields_length (record : InteriorCodec.Record) :
    (rawFieldsBytes (recordRawFields record)).length=498 := by
  unfold recordRawFields
  rw [payload_raw_fields_length,(record_descriptor_sizes record).1]
  rfl

theorem record_raw_fields_steps (record : InteriorCodec.Record) :
    rawFieldsSteps (recordRawFields record)=2035 := by
  unfold recordRawFields
  rw [payload_raw_fields_steps,(record_descriptor_sizes record).1]
  rfl

theorem record_raw_fields_count (record : InteriorCodec.Record) : (recordRawFields record).length=17 := by
  unfold recordRawFields
  rw [payload_raw_fields_count]
  rfl

theorem footer_fields_small (nodes : List Nat) : ∀ field ∈ InteriorCodec.footerSpec nodes, field.2≤6 := by
  intro field member
  obtain ⟨node,_,same⟩ := List.mem_map.mp member
  subst field
  change InteriorCodec.footerWidth node-232≤6
  unfold InteriorCodec.footerWidth
  split <;> omega

def footerRawFields (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) : List RawField :=
  payloadRawFields footer [] (footer_fields_small nodes) (by simp)

theorem footer_raw_fields_count (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    (footerRawFields nodes footer).length=nodes.length := by
  unfold footerRawFields
  rw [payload_raw_fields_count]
  simp only [InteriorCodec.footerSpec,List.length_map]

theorem footer_raw_fields_length (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    (rawFieldsBytes (footerRawFields nodes footer)).length=30*nodes.length := by
  unfold footerRawFields
  rw [payload_raw_fields_length,footer_low_bytes_length]
  simp only [List.take_nil,List.flatten_nil,List.length_nil,InteriorCodec.footerSpec,List.length_map]
  omega

theorem footer_raw_fields_steps (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    rawFieldsSteps (footerRawFields nodes footer)=123*nodes.length := by
  unfold footerRawFields
  rw [payload_raw_fields_steps,footer_low_bytes_length]
  simp only [InteriorCodec.footerSpec,List.length_map]
  omega

end CommitGolfCandidate.Chained.Native
