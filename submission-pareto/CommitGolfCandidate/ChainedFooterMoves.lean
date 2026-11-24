import CommitGolfCandidate.ChainedFooterLayout

/-! Compose actual footer blocks while transporting the full data invariant. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def RunsFooterBlock (before after : MachineState) (cycles : Nat) : Prop :=
  ∀ fuel coins, execute openingControllerImage (cycles+fuel) before coins=
    (do let result ← execute openingControllerImage fuel after coins
        return result.charge cycles 0)

theorem RunsFooterBlock.next {before middle after : MachineState} {a b : Nat}
    (first : RunsFooterBlock before middle a) (second : RunsFooterBlock middle after b) :
    RunsFooterBlock before after (a+b) := by
  intro fuel coins
  rw [Nat.add_assoc,first (b+fuel) coins,second fuel coins]
  simp [Execution.charge,←Nat.add_assoc]

theorem footer_emit_cycles_node (s : MachineState) (node : Nat) (bounded : node<512)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) :
    footerEmitCycles s=if node<256 then 126 else 125 := by
  unfold footerEmitCycles footerHeaderCycles
  rw [footer_wide_test s node bounded cursor limit]
  by_cases internal : node<256 <;> simp [internal]

theorem footer_ready_emit_run {groups : List Nat} {field : RawField} {fields : List RawField}
    {suffix outputPrefix metaPrefix : Proof} {s : MachineState} {node source outputBase metaBase : Nat}
    (ready : FooterReady groups (field::fields) suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (pc : s.pc=12436) (bounded : node<512) (lowSize : field.low.length=29) (padding : field.padding=[]) :
    RunsFooterBlock s (footerEmitState s) (if node<256 then 126 else 125) := by
  have rawSize : field.bytes.length=30 := by simp only [RawField.bytes,lowSize,padding,List.length_append,List.length_cons,List.length_nil]
  have separate : source+30≤metaBase+metaPrefix.length := by
    have bound := ready.data.separate
    change source+(field.bytes++rawFieldsBytes fields).length+suffix.length≤metaBase at bound
    rw [List.length_append,rawSize] at bound
    omega
  have capacity : metaBase+metaPrefix.length+2≤MEMORY_BYTES := by
    have bound := ready.capacity
    simp only [List.length_cons] at bound
    omega
  intro fuel coins
  have execution := footer_emit_execution s pc source (outputBase+outputPrefix.length) (metaBase+metaPrefix.length)
    ready.data.sourcePointer ready.data.outputPointer ready.data.metaPointer ready.data.ordered separate capacity fuel coins
  simpa only [footer_emit_cycles_node s node bounded ready.cursor ready.marks.limit] using execution

theorem FooterReady.decision {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {node source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s node source outputBase metaBase) :
    FooterReady groups fields suffix outputPrefix metaPrefix (footerDecisionPrefix s 4) node source outputBase metaBase := by
  apply ready.move ready.marks.decision
  · rw [footer_decision_register _ .x30 (by decide)]
    exact ready.cursor
  · intro reg member
    apply footer_decision_register
    intro same
    subst reg
    simp at member
  · exact footer_decision_byte s

theorem footer_node_low_bit (node : Nat) (bounded : node<512) :
    BitVec.ofNat 64 node&&&1#64=BitVec.ofNat 64 (node%2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : node<2^64)]
  rw [Nat.mod_eq_of_lt (by omega : node%2<2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem footer_move_sibling {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {parent source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s (2*parent) source outputBase metaBase)
    (positive : 0<parent) (bounded : 2*parent<512) (pc : s.pc=12940) :
    let after := footerSiblingPrefix (footerDecisionPrefix s 4) 2
    RunsFooterBlock s after 6 ∧ after.pc=12408 ∧
    FooterReady groups fields suffix outputPrefix metaPrefix after (2*parent+1) source outputBase metaBase := by
  have notRoot : s.getReg .x30≠1#64 := by
    rw [ready.cursor]
    exact word_of_nat_ne _ _ (by omega) (by decide) (by omega)
  have even : s.getReg .x30&&&1#64=0#64 := by
    rw [ready.cursor,footer_node_low_bit _ bounded,show (2*parent)%2=0 by omega]
  have nextPC : (footerDecisionPrefix s 4).pc=12964 := by
    rw [footer_decision_pc s pc notRoot,ite_eq_left even]
  dsimp only
  refine ⟨(show RunsFooterBlock s (footerDecisionPrefix s 4) 4 from
    fun fuel coins => footer_decision_execution s pc notRoot fuel coins).next
    (fun fuel coins => footer_sibling_execution _ nextPC fuel coins),footer_sibling_pc _ nextPC,?_⟩
  apply ready.decision.move ready.marks.decision.sibling
  · rw [footer_sibling_node,footer_decision_register _ .x30 (by decide),ready.cursor]
    change BitVec.ofNat 64 (2*parent)+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  · intro reg member
    apply footer_sibling_register
    intro same
    subst reg
    simp at member
  · exact footer_sibling_byte _

theorem footer_move_parent {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {parent source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s (2*parent+1) source outputBase metaBase)
    (positive : 0<parent) (bounded : 2*parent+1<512) (pc : s.pc=12940) :
    let after := footerParentPrefix (footerDecisionPrefix s 4) 2
    RunsFooterBlock s after 6 ∧ after.pc=12940 ∧
    FooterReady groups fields suffix outputPrefix metaPrefix after parent source outputBase metaBase := by
  have notRoot : s.getReg .x30≠1#64 := by
    rw [ready.cursor]
    exact word_of_nat_ne _ _ (by omega) (by decide) (by omega)
  have odd : s.getReg .x30&&&1#64≠0#64 := by
    rw [ready.cursor,footer_node_low_bit _ bounded,show (2*parent+1)%2=1 by omega]
    decide
  have nextPC : (footerDecisionPrefix s 4).pc=12956 := by
    rw [footer_decision_pc s pc notRoot,ite_eq_right odd]
  dsimp only
  refine ⟨(show RunsFooterBlock s (footerDecisionPrefix s 4) 4 from
    fun fuel coins => footer_decision_execution s pc notRoot fuel coins).next
    (fun fuel coins => footer_parent_execution _ nextPC fuel coins),footer_parent_pc _ nextPC,?_⟩
  apply ready.decision.move ready.marks.decision.parent
  · rw [footer_parent_node,footer_decision_register _ .x30 (by decide),ready.cursor]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 2*parent+1<2^64),
      Nat.mod_eq_of_lt (by omega : parent<2^64)]
    omega
  · intro reg member
    apply footer_parent_register
    intro same
    subst reg
    simp at member
  · exact footer_parent_byte _

theorem FooterRangeReady.decision {groups : List Nat} {remaining node source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s node source output metadata count proofBase) :
    FooterRangeReady groups remaining (footerDecisionPrefix s 4) node source output metadata count proofBase := by
  apply ready.move ready.marks.decision
  · rw [footer_decision_register _ .x30 (by decide)]; exact ready.cursor
  · intro reg member
    apply footer_decision_register
    intro same; subst reg; simp at member

theorem footer_range_move_sibling {groups : List Nat} {remaining parent source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s (2*parent) source output metadata count proofBase)
    (positive : 0<parent) (bounded : 2*parent<512) (pc : s.pc=12940) :
    let after := footerSiblingPrefix (footerDecisionPrefix s 4) 2
    RunsFooterBlock s after 6 ∧ after.pc=12408 ∧
    FooterRangeReady groups remaining after (2*parent+1) source output metadata count proofBase := by
  have notRoot : s.getReg .x30≠1#64 := by
    rw [ready.cursor]
    exact word_of_nat_ne _ _ (by omega) (by decide) (by omega)
  have even : s.getReg .x30&&&1#64=0#64 := by
    rw [ready.cursor,footer_node_low_bit _ bounded,show (2*parent)%2=0 by omega]
  have nextPC : (footerDecisionPrefix s 4).pc=12964 := by
    rw [footer_decision_pc s pc notRoot,ite_eq_left even]
  dsimp only
  refine ⟨(show RunsFooterBlock s (footerDecisionPrefix s 4) 4 from
    fun fuel coins => footer_decision_execution s pc notRoot fuel coins).next
    (fun fuel coins => footer_sibling_execution _ nextPC fuel coins),footer_sibling_pc _ nextPC,?_⟩
  apply ready.decision.move ready.marks.decision.sibling
  · rw [footer_sibling_node,footer_decision_register _ .x30 (by decide),ready.cursor]
    change BitVec.ofNat 64 (2*parent)+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  · intro reg member
    apply footer_sibling_register
    intro same; subst reg; simp at member

theorem footer_range_move_parent {groups : List Nat} {remaining parent source output metadata count : Nat}
    {s : MachineState} {proofBase : Word}
    (ready : FooterRangeReady groups remaining s (2*parent+1) source output metadata count proofBase)
    (positive : 0<parent) (bounded : 2*parent+1<512) (pc : s.pc=12940) :
    let after := footerParentPrefix (footerDecisionPrefix s 4) 2
    RunsFooterBlock s after 6 ∧ after.pc=12940 ∧
    FooterRangeReady groups remaining after parent source output metadata count proofBase := by
  have notRoot : s.getReg .x30≠1#64 := by
    rw [ready.cursor]
    exact word_of_nat_ne _ _ (by omega) (by decide) (by omega)
  have odd : s.getReg .x30&&&1#64≠0#64 := by
    rw [ready.cursor,footer_node_low_bit _ bounded,show (2*parent+1)%2=1 by omega]
    decide
  have nextPC : (footerDecisionPrefix s 4).pc=12956 := by
    rw [footer_decision_pc s pc notRoot,ite_eq_right odd]
  dsimp only
  refine ⟨(show RunsFooterBlock s (footerDecisionPrefix s 4) 4 from
    fun fuel coins => footer_decision_execution s pc notRoot fuel coins).next
    (fun fuel coins => footer_parent_execution _ nextPC fuel coins),footer_parent_pc _ nextPC,?_⟩
  apply ready.decision.move ready.marks.decision.parent
  · rw [footer_parent_node,footer_decision_register _ .x30 (by decide),ready.cursor]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 2*parent+1<2^64),Nat.mod_eq_of_lt (by omega : parent<2^64)]
    omega
  · intro reg member
    apply footer_parent_register
    intro same; subst reg; simp at member

end CommitGolfCandidate.Chained.Native
