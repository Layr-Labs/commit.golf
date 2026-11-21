import CommitGolfCandidate.ChainedFooterFrame

/-! Extend the actual footer's accumulated low-body and descriptor prefixes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem raw_fields_ready_transport (fields : List RawField) (suffix outputPrefix metaPrefix : Proof)
    (before after : MachineState) (source outputBase metaBase : Nat)
    (ready : RawFieldsReady fields suffix outputPrefix metaPrefix before source outputBase metaBase)
    (sourceFrame : after.getReg .x5=before.getReg .x5)
    (outputFrame : after.getReg .x6=before.getReg .x6)
    (metaFrame : after.getReg .x7=before.getReg .x7)
    (bytes : ∀ address, after.getByte address=before.getByte address) :
    RawFieldsReady fields suffix outputPrefix metaPrefix after source outputBase metaBase := by
  refine ⟨sourceFrame.trans ready.sourcePointer,outputFrame.trans ready.outputPointer,
    metaFrame.trans ready.metaPointer,?_,?_,?_,ready.ordered,ready.separate,ready.room⟩
  · intro index inside
    rw [bytes]
    exact ready.input index inside
  · intro index inside
    rw [bytes]
    exact ready.output index inside
  · intro index inside
    rw [bytes]
    exact ready.metadata index inside

theorem footer_fields_step (field : RawField) (fields : List RawField)
    (suffix outputPrefix metaPrefix : Proof) (s : MachineState) (source outputBase metaBase node : Nat)
    (ready : RawFieldsReady (field::fields) suffix outputPrefix metaPrefix s source outputBase metaBase)
    (lowSize : field.low.length=29) (padding : field.padding=[])
    (highSize : field.high.length=InteriorCodec.footerWidth node-232) (nodeFit : node<2^64)
    (nodeReg : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) :
    RawFieldsReady fields suffix (outputPrefix++field.low) (metaPrefix++descriptorBytes [field.high])
      (footerEmitState s) (source+30) outputBase metaBase := by
  have rawSize : field.bytes.length=30 := by simp only [RawField.bytes,padding,lowSize,List.length_append,List.length_cons,List.length_nil]
  have separate : source+30+(rawFieldsBytes fields++suffix).length≤metaBase := by
    have bound := ready.separate
    change source+(field.bytes++rawFieldsBytes fields).length+suffix.length≤metaBase at bound
    simp only [List.length_append,rawSize] at bound ⊢
    omega
  have room : metaBase+metaPrefix.length+2<2^64 := by
    have bound := ready.room
    simp only [List.length_cons] at bound
    omega
  have result := footer_emit_memory field (rawFieldsBytes fields++suffix) s source
    (outputBase+outputPrefix.length) (metaBase+metaPrefix.length) node lowSize padding highSize nodeFit
    nodeReg limit ready.sourcePointer ready.outputPointer ready.metaPointer
    (by simpa only [rawFieldsBytes,List.flatMap_cons,List.append_assoc] using ready.input)
    ready.ordered (by omega) room
  have outputBound : outputBase+outputPrefix.length+29≤metaBase := by have := ready.ordered; omega
  have oldOutput := footer_emit_preserves_bytes outputPrefix s (outputBase+outputPrefix.length)
    (metaBase+metaPrefix.length) outputBase ready.outputPointer ready.metaPointer ready.output
    (by omega) room (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have oldMeta := footer_emit_preserves_bytes metaPrefix s (outputBase+outputPrefix.length)
    (metaBase+metaPrefix.length) metaBase ready.outputPointer ready.metaPointer ready.metadata
    (by omega) room (by omega) (Or.inr outputBound) (Or.inl (by omega))
  refine ⟨result.2.2.2.1,?_,?_,result.2.2.1,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append,lowSize,Nat.add_assoc] using result.2.2.2.2.1
  · simpa only [descriptor_bytes_length,List.length_singleton,List.length_append,Nat.mul_one,Nat.add_assoc] using result.2.2.2.2.2
  · apply (bytes_at_append _ _ outputPrefix field.low).mpr
    refine ⟨oldOutput,?_⟩
    rw [←BitVec.ofNat_add]
    exact result.1
  · apply (bytes_at_append _ _ metaPrefix (descriptorBytes [field.high])).mpr
    refine ⟨oldMeta,?_⟩
    rw [←BitVec.ofNat_add]
    exact result.2.1
  · simp only [List.length_append,lowSize]
    have := ready.ordered
    omega
  · simpa only [List.length_append,Nat.add_assoc] using separate
  · have bound := ready.room
    simp only [List.length_append,descriptor_bytes_length,List.length_cons,List.length_nil] at bound ⊢
    omega

end CommitGolfCandidate.Chained.Native
