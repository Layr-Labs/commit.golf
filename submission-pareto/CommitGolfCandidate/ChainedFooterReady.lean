import CommitGolfCandidate.ChainedFooterMarks

/-! Data, marks and physical capacity invariant for the native footer traversal. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

structure FooterReady (groups : List Nat) (fields : List RawField) (suffix outputPrefix metaPrefix : Proof)
    (s : MachineState) (node source outputBase metaBase : Nat) : Prop where
  marks : FooterMarks groups s
  data : RawFieldsReady fields suffix outputPrefix metaPrefix s source outputBase metaBase
  cursor : s.getReg .x30=BitVec.ofNat 64 node
  count : s.getReg .x19=BitVec.ofNat 64 (metaPrefix.length/2)
  even : metaPrefix.length%2=0
  outputAbove : 8192≤outputBase
  metaAbove : 8192≤metaBase
  capacity : metaBase+metaPrefix.length+2*fields.length≤MEMORY_BYTES
  proofBase : s.getReg .x17=BitVec.ofNat 64 outputBase

theorem FooterReady.move {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s after : MachineState} {node next source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (marks : FooterMarks groups after) (cursor : after.getReg .x30=BitVec.ofNat 64 next)
    (register : ∀ reg, reg ∈ ([.x5,.x6,.x7,.x17,.x19] : List Reg) → after.getReg reg=s.getReg reg)
    (bytes : ∀ address, after.getByte address=s.getByte address) :
    FooterReady groups fields suffix outputPrefix metaPrefix after next source outputBase metaBase := by
  refine ⟨marks,?_,cursor,?_,ready.even,ready.outputAbove,ready.metaAbove,ready.capacity,?_⟩
  · exact raw_fields_ready_transport fields suffix outputPrefix metaPrefix s after source outputBase metaBase ready.data
      (register .x5 (by simp)) (register .x6 (by simp)) (register .x7 (by simp)) bytes
  · rw [register .x19 (by simp)]
    exact ready.count
  · rw [register .x17 (by simp)]
    exact ready.proofBase

theorem FooterReady.lookup {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {node source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s node source outputBase metaBase) :
    FooterReady groups fields suffix outputPrefix metaPrefix (footerLookupPrefix s 4) node source outputBase metaBase := by
  apply ready.move ready.marks.lookup
  · rw [footer_lookup_register _ .x30 (by decide)]
    exact ready.cursor
  · intro reg member
    apply footer_lookup_register
    intro same
    subst reg
    simp at member
  · exact footer_lookup_byte s

theorem footer_wide_test (s : MachineState) (node : Nat) (bounded : node<512)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) :
    footerWide s=decide (node<256) := by
  rw [footerWide,cursor,limit,BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : node<2^64)]
  rfl

theorem FooterReady.descend {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {node source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (internal : footerWide s) :
    FooterReady groups fields suffix outputPrefix metaPrefix (footerKnownPrefix s 3) (2*node) source outputBase metaBase := by
  apply ready.move (ready.marks.descend internal)
  · rw [footer_descend_node s internal,ready.cursor,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 node*BitVec.ofNat 64 2=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm node]
  · intro reg member
    apply footer_descend_register _ internal
    intro same
    subst reg
    simp at member
  · exact footer_descend_byte s internal

theorem FooterReady.prune {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {node source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s node source outputBase metaBase) :
    FooterReady groups fields suffix outputPrefix metaPrefix (footerKnownPrefix s 1) node source outputBase metaBase := by
  apply ready.move ready.marks.prune
  · rw [footer_prune_register]
    exact ready.cursor
  · intro reg _
    exact footer_prune_register s reg
  · exact footer_prune_byte s

theorem FooterReady.emit {groups : List Nat} {field : RawField} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {node source outputBase metaBase : Nat}
    (ready : FooterReady groups (field::fields) suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (lowSize : field.low.length=29) (padding : field.padding=[])
    (highSize : field.high.length=InteriorCodec.footerWidth node-232) (nodeFit : node<2^64) :
    FooterReady groups fields suffix (outputPrefix++field.low) (metaPrefix++descriptorBytes [field.high])
      (footerEmitState s) node (source+30) outputBase metaBase := by
  have data := footer_fields_step field fields suffix outputPrefix metaPrefix s source outputBase metaBase node ready.data
    lowSize padding highSize nodeFit ready.cursor ready.marks.limit
  have room : metaBase+metaPrefix.length+2<2^64 := by
    have cap := ready.capacity
    simp only [List.length_cons] at cap
    unfold MEMORY_BYTES at cap
    omega
  have rawSize : field.bytes.length=30 := by simp only [RawField.bytes,padding,lowSize,List.length_append,List.length_cons,List.length_nil]
  have outputRoom : outputBase+outputPrefix.length+29<2^64 := by
    have apart := ready.data.separate
    change source+(field.bytes++rawFieldsBytes fields).length+suffix.length≤metaBase at apart
    rw [List.length_append,rawSize] at apart
    have ordered := ready.data.ordered
    omega
  refine ⟨ready.marks.emit _ _ ready.data.outputPointer ready.data.metaPointer outputRoom room
    (by have := ready.outputAbove; omega) (by have := ready.metaAbove; omega),data,?_,?_,?_,
    ready.outputAbove,ready.metaAbove,?_,?_⟩
  · rw [footer_emit_register _ .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.cursor
  · rw [footer_emit_counter,ready.count]
    simp only [List.length_append,descriptor_bytes_length,List.length_singleton,Nat.mul_one]
    have quotient : (metaPrefix.length+2)/2=metaPrefix.length/2+1 := by omega
    rw [quotient,BitVec.ofNat_add]
    rfl
  · simp only [List.length_append,descriptor_bytes_length,List.length_singleton,Nat.mul_one]
    have := ready.even
    omega
  · have cap := ready.capacity
    simp only [List.length_append,descriptor_bytes_length,List.length_cons,List.length_nil] at cap ⊢
    omega
  · rw [footer_emit_register _ .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.proofBase

structure FooterRangeReady (groups : List Nat) (remaining : Nat) (s : MachineState)
    (node source output metadata count : Nat) (proofBase : Word) : Prop where
  marks : FooterMarks groups s
  cursor : s.getReg .x30=BitVec.ofNat 64 node
  sourcePointer : s.getReg .x5=BitVec.ofNat 64 source
  outputPointer : s.getReg .x6=BitVec.ofNat 64 output
  metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata
  counter : s.getReg .x19=BitVec.ofNat 64 count
  proofBaseReg : s.getReg .x17=proofBase
  ordered : output≤source
  separate : source+30*remaining≤metadata
  capacity : metadata+2*remaining≤MEMORY_BYTES
  outputAbove : 8192≤output
  metaAbove : 8192≤metadata

theorem FooterRangeReady.move {groups : List Nat} {remaining node next source output metadata count : Nat}
    {s after : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s node source output metadata count proofBase)
    (marks : FooterMarks groups after) (cursor : after.getReg .x30=BitVec.ofNat 64 next)
    (register : ∀ reg, reg ∈ ([.x5,.x6,.x7,.x17,.x19] : List Reg) → after.getReg reg=s.getReg reg) :
    FooterRangeReady groups remaining after next source output metadata count proofBase := by
  refine ⟨marks,cursor,?_,?_,?_,?_,?_,ready.ordered,ready.separate,ready.capacity,ready.outputAbove,ready.metaAbove⟩
  · rw [register .x5 (by simp)]; exact ready.sourcePointer
  · rw [register .x6 (by simp)]; exact ready.outputPointer
  · rw [register .x7 (by simp)]; exact ready.metaPointer
  · rw [register .x19 (by simp)]; exact ready.counter
  · rw [register .x17 (by simp)]; exact ready.proofBaseReg

theorem FooterRangeReady.lookup {groups : List Nat} {remaining node source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s node source output metadata count proofBase) :
    FooterRangeReady groups remaining (footerLookupPrefix s 4) node source output metadata count proofBase := by
  apply ready.move ready.marks.lookup
  · rw [footer_lookup_register _ .x30 (by decide)]; exact ready.cursor
  · intro reg member
    apply footer_lookup_register
    intro same; subst reg; simp at member

theorem FooterRangeReady.descend {groups : List Nat} {remaining node source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s node source output metadata count proofBase)
    (internal : footerWide s) :
    FooterRangeReady groups remaining (footerKnownPrefix s 3) (2*node) source output metadata count proofBase := by
  apply ready.move (ready.marks.descend internal)
  · rw [footer_descend_node s internal,ready.cursor,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 node*BitVec.ofNat 64 2=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm node]
  · intro reg member
    apply footer_descend_register _ internal
    intro same; subst reg; simp at member

theorem FooterRangeReady.prune {groups : List Nat} {remaining node source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s node source output metadata count proofBase) :
    FooterRangeReady groups remaining (footerKnownPrefix s 1) node source output metadata count proofBase := by
  apply ready.move ready.marks.prune
  · rw [footer_prune_register]; exact ready.cursor
  · intro reg _; exact footer_prune_register s reg

theorem FooterRangeReady.emit {groups : List Nat} {remaining node source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups (remaining+1) s node source output metadata count proofBase) :
    FooterRangeReady groups remaining (footerEmitState s) node (source+30) (output+29)
      (metadata+2) (count+1) proofBase := by
  have capacity := ready.capacity
  have separate := ready.separate
  have ordered := ready.ordered
  have room : metadata+2<2^64 := by unfold MEMORY_BYTES at capacity; omega
  have outputRoom : output+29<2^64 := by omega
  refine ⟨ready.marks.emit output metadata ready.outputPointer ready.metaPointer outputRoom room
    ready.outputAbove ready.metaAbove,?_,?_,?_,?_,?_,?_,by omega,by omega,by omega,by have := ready.outputAbove; omega,
      by have := ready.metaAbove; omega⟩
  · rw [footer_emit_register _ .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.cursor
  · rw [footerEmitState,footer_count_register _ .x5 (by decide),field_build_source,
      footer_header_register _ .x5 (by decide) (by decide),footer_header_skip,ready.sourcePointer]
    have one : (1 : Word)=BitVec.ofNat 64 1 := by decide
    rw [one,←BitVec.ofNat_add,←BitVec.ofNat_add]
  · rw [footerEmitState,footer_count_register _ .x6 (by decide),field_build_destination,
      footer_header_register _ .x6 (by decide) (by decide),ready.outputPointer,←BitVec.ofNat_add]
  · rw [footerEmitState,footer_count_register _ .x7 (by decide),field_build_descriptor_pointer,
      footer_header_register _ .x7 (by decide) (by decide),ready.metaPointer]
    have two : (2 : Word)=BitVec.ofNat 64 2 := by decide
    rw [two,←BitVec.ofNat_add]
  · rw [footer_emit_counter,ready.counter,BitVec.ofNat_add]
    rfl
  · rw [footer_emit_register _ .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.proofBaseReg

end CommitGolfCandidate.Chained.Native
