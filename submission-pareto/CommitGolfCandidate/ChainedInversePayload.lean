import CommitGolfCandidate.ChainedInverseFieldsExecution
import CommitGolfCandidate.ChainedPayloadFields
import CommitGolfCandidate.ChainedInverseDecode

/-! Whole typed payload reconstruction from its low body and parsed descriptors. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
attribute [local irreducible] execute

theorem native_inverse_payload {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2)
    (image : Image) (base : Word) (suffix : Proof) (s : MachineState) (source outputBase metadata : Nat)
    (code : InverseRawFieldsAt image base (payloadRawFields payload pads small padSmall))
    (pc : s.pc=base)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata)
    (input : BytesAt s (BitVec.ofNat 64 source) (lowBytes payload++suffix))
    (table : BytesAt s (BitVec.ofNat 64 metadata) (descriptorBytes (highRows payload)))
    (padding : RawPaddingAt s (BitVec.ofNat 64 outputBase) (payloadRawFields payload pads small padSmall))
    (inputBefore : source+(lowBytes payload).length+suffix.length<outputBase)
    (outputBefore : outputBase+(rawFieldsBytes (payloadRawFields payload pads small padSmall)).length≤metadata)
    (capacity : metadata+2*spec.length≤MEMORY_BYTES) :
    let fields := payloadRawFields payload pads small padSmall
    let after := inverseRawFieldsState fields s
    let cycles := 4*(lowBytes payload).length+6*spec.length
    BytesAt after (BitVec.ofNat 64 outputBase) (rawFieldsBytes fields) ∧
    BytesAt after (BitVec.ofNat 64 (source+(lowBytes payload).length)) suffix ∧
    after.getReg .x5=BitVec.ofNat 64 (source+(lowBytes payload).length) ∧
    after.getReg .x6=BitVec.ofNat 64 (outputBase+(rawFieldsBytes fields).length) ∧
    after.getReg .x7=BitVec.ofNat 64 (metadata+2*spec.length) ∧
    ∀ fuel coins, execute image (cycles+fuel) s coins=
      (do let result ← execute image fuel after coins
          return result.charge cycles 0) := by
  let fields := payloadRawFields payload pads small padSmall
  have low : rawFieldsLow fields=lowBytes payload := payload_raw_fields_low payload pads small padSmall
  have high : rawFieldsMeta fields=descriptorBytes (highRows payload) := by
    rw [raw_fields_meta_rows,payload_raw_fields_high]
  have count : fields.length=spec.length := payload_raw_fields_count payload pads small padSmall
  have ready : InverseFieldsReady fields suffix [] s source outputBase metadata := by
    refine ⟨sourcePointer,?_,metaPointer,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using outputPointer
    · rwa [low]
    · intro index inside
      simp at inside
    · rwa [high]
    · simpa using padding
    · rwa [low]
    · simpa using outputBefore
    · rw [count]
      unfold MEMORY_BYTES at capacity
      omega
  have result := inverse_raw_fields_memory fields suffix [] s source outputBase metadata ready
  have steps : inverseRawFieldsSteps fields=4*(lowBytes payload).length+6*spec.length := by
    rw [inverse_raw_fields_steps,low,count]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.nil_append] using result.output
  · have rest := result.input
    rw [low] at rest
    simpa only [rawFieldsLow,List.flatMap_nil,List.nil_append] using rest
  · simpa only [low] using result.sourcePointer
  · simpa only [List.nil_append] using result.outputPointer
  · simpa only [count] using result.metaPointer
  · intro fuel coins
    rw [←steps]
    exact inverse_raw_fields_execution image fields suffix [] s source outputBase metadata base code ready pc
      (by rwa [count]) fuel coins

end CommitGolfCandidate.Chained.Native
