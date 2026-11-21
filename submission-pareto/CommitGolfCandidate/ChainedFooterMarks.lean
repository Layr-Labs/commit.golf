import CommitGolfCandidate.ChainedFooterFieldStep

/-! The native footer reads the canonical cap marks, unchanged by its own writes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Opening TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

structure FooterMarks (groups : List Nat) (s : MachineState) : Prop where
  base : s.getReg .x8=4096
  limit : s.getReg .x29=256
  words : ∀ node, node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node

theorem FooterMarks.transport {groups : List Nat} {before after : MachineState}
    (marks : FooterMarks groups before)
    (base : after.getReg .x8=before.getReg .x8) (limit : after.getReg .x29=before.getReg .x29)
    (memory : ∀ address, after.getMem address=before.getMem address) : FooterMarks groups after := by
  refine ⟨base.trans marks.base,limit.trans marks.limit,?_⟩
  intro node bound
  rw [memory]
  exact marks.words node bound

theorem FooterMarks.lookup {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s) :
    FooterMarks groups (footerLookupPrefix s 4) :=
  marks.transport (footer_lookup_register _ _ (by decide)) (footer_lookup_register _ _ (by decide))
    (footer_lookup_memory s)
theorem FooterMarks.descend {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s) (internal : footerWide s) :
    FooterMarks groups (footerKnownPrefix s 3) :=
  marks.transport (footer_descend_register _ internal _ (by decide)) (footer_descend_register _ internal _ (by decide))
    (footer_descend_memory s internal)
theorem FooterMarks.prune {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s) :
    FooterMarks groups (footerKnownPrefix s 1) :=
  marks.transport (footer_prune_register _ _) (footer_prune_register _ _) (footer_prune_memory s)
theorem FooterMarks.decision {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s) :
    FooterMarks groups (footerDecisionPrefix s 4) :=
  marks.transport (footer_decision_register _ _ (by decide)) (footer_decision_register _ _ (by decide))
    (footer_decision_memory s)
theorem FooterMarks.parent {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s) :
    FooterMarks groups (footerParentPrefix s 2) :=
  marks.transport (footer_parent_register _ _ (by decide)) (footer_parent_register _ _ (by decide))
    (footer_parent_memory s)
theorem FooterMarks.sibling {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s) :
    FooterMarks groups (footerSiblingPrefix s 2) :=
  marks.transport (footer_sibling_register _ _ (by decide)) (footer_sibling_register _ _ (by decide))
    (footer_sibling_memory s)

theorem FooterMarks.emit {groups : List Nat} {s : MachineState} (marks : FooterMarks groups s)
    (output metadata : Nat)
    (outputReg : s.getReg .x6=BitVec.ofNat 64 output) (metaReg : s.getReg .x7=BitVec.ofNat 64 metadata)
    (outputFit : output+29<2^64) (metaFit : metadata+2<2^64)
    (outputAbove : 8192≤output) (metaAbove : 8192≤metadata) : FooterMarks groups (footerEmitState s) := by
  refine ⟨?_,?_,?_⟩
  · rw [footer_emit_register _ .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact marks.base
  · rw [footer_emit_register _ .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact marks.limit
  · intro node bound
    rw [footer_emit_mark_frame s output metadata node outputReg metaReg outputFit metaFit outputAbove metaAbove bound]
    exact marks.words node bound

theorem footer_mark_test (groups : List Nat) (s : MachineState) (node height : Nat)
    (marks : FooterMarks groups s) (span : CapSpan node height) (cursor : s.getReg .x30=BitVec.ofNat 64 node) :
    s.getMem (footerMarkAddress s)=0#64 ↔ capIsMarked groups node height=false := by
  rw [footer_mark_address_eq s node marks.base cursor,marks.words node (cap_span_node node height span).2,
    markWord,cap_span_height node height span]
  cases capIsMarked groups node height <;> decide

theorem footer_lookup_access (groups : List Nat) (s : MachineState) (node height : Nat)
    (marks : FooterMarks groups s) (span : CapSpan node height) (cursor : s.getReg .x30=BitVec.ofNat 64 node) :
    accessValid (footerMarkAddress s) 8=true := by
  rw [footer_mark_address_eq s node marks.base cursor]
  have bound := (cap_span_node node height span).2
  have natural : (BitVec.ofNat 64 (4096+8*node)).toNat=4096+8*node := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [accessValid,rangeValid,natural,MEMORY_BYTES]
  omega

theorem footer_lookup_dispatch (groups : List Nat) (s : MachineState) (node height : Nat)
    (pc : s.pc=12408) (marks : FooterMarks groups s) (span : CapSpan node height)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) :
    (footerLookupPrefix s 4).pc=if capIsMarked groups node height then 12424 else 12436 := by
  rw [footer_lookup_pc s pc]
  have test := footer_mark_test groups s node height marks span cursor
  cases marked : capIsMarked groups node height
  · have empty : s.getMem (footerMarkAddress s)=0 := by simpa using test.mpr marked
    simp only [Bool.false_eq_true,↓reduceIte,empty]
  · have occupied : s.getMem (footerMarkAddress s)≠0 := by
      intro empty
      have absent := test.mp (by simpa using empty)
      rw [marked] at absent
      contradiction
    simp only [↓reduceIte,occupied]

end CommitGolfCandidate.Chained.Native
