import CommitGolfCandidate.ChainedFooterTailFrame

/-! Complete footer DFS, root exit, variable tail, result ABI and successful halt. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem footer_complete (groups : List Nat) (footer : Payload (InteriorCodec.footerSpec (capFrontierNodes groups 1 8)))
    (suffix oldPrefix : Proof) (s : MachineState) (source outputBase metadata : Nat)
    (ready : FooterReady groups (footerRawFields (capFrontierNodes groups 1 8) footer) suffix oldPrefix []
      s 1 source outputBase metadata)
    (pc : s.pc=12408)
    (gap : outputBase+oldPrefix.length+(lowBytes footer).length+(capFrontierNodes groups 1 8).length<metadata)
    (outputFit : outputBase+oldPrefix.length+(encode footer).length<2^64) :
    ∃ after cycles, (∀ fuel coins, execute openingControllerImage (cycles+fuel) s coins=pure ⟨.success,after,cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 outputBase) (oldPrefix++encode footer) ∧
      after.getReg .x6=BitVec.ofNat 64 (outputBase+oldPrefix.length+(encode footer).length) ∧
      (after.getReg .x11).toNat=oldPrefix.length+(encode footer).length ∧
      cycles≤66448+13*(capFrontierNodes groups 1 8).length := by
  have fit : (encode footer).length<2^64 := by omega
  let nodes := capFrontierNodes groups 1 8
  have initial : FooterReady groups (footerRawFields nodes footer++[]) suffix oldPrefix [] s 1 source outputBase metadata := by
    simpa only [List.append_nil] using ready
  obtain ⟨built,run,builtPC,builtReady⟩ := footer_subtree groups (footerRawFields nodes footer) [] suffix oldPrefix []
    s 1 8 source outputBase metadata (footer_raw_fields_layout nodes footer) initial cap_span_root pc
  have builtData : FooterReady groups [] suffix (oldPrefix++lowBytes footer) (descriptorBytes (highRows footer))
      built 1 (source+30*nodes.length) outputBase metadata := by
    simpa only [footer_raw_fields_low,footer_raw_fields_meta,footer_raw_fields_length,List.nil_append] using builtReady
  have root : built.getReg .x30=1#64 := builtData.cursor
  have checkedPC := footer_root_pc built builtPC root
  have marks : FooterMarks groups (footerDecisionPrefix built 2) :=
    builtData.marks.transport (footer_root_register built root .x8 (by decide))
      (footer_root_register built root .x29 (by decide)) (footer_root_memory built root)
  have checked : FooterReady groups [] suffix (oldPrefix++lowBytes footer) (descriptorBytes (highRows footer))
      (footerDecisionPrefix built 2) 1 (source+30*nodes.length) outputBase metadata := by
    apply builtData.move marks
    · rw [footer_root_register built root .x30 (by decide)]
      exact root
    · intro reg member
      apply footer_root_register _ root
      intro same
      subst reg
      simp at member
    · exact footer_root_byte built root
  let tail := footerTailSetupPrefix (footerDecisionPrefix built 2) 7
  have tailReady : FooterTailReady nodes footer tail (outputBase+oldPrefix.length) metadata :=
    footer_tail_ready groups nodes footer suffix oldPrefix _ 1 _ outputBase metadata checked gap
  have tailPC : tail.pc=13000 := by
    dsimp only [tail]
    rw [footer_tail_setup_pc _ 7 (by decide),checkedPC]
    rfl
  have packedPC : (tailTraverseState nodes.length tail).pc=13068 :=
    (footer_tail_pack nodes footer tail _ _ tailReady tailPC fit 0 false).2.2.1
  have pointer := footer_tail_cursor nodes footer tail _ metadata tailReady
  have packedBase : (tailTraverseState nodes.length tail).getReg .x17=BitVec.ofNat 64 outputBase := by
    rw [tail_traverse_register _ _ .x17 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    dsimp only [tail]
    rw [footer_tail_setup_frame _ .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact checked.proofBase
  have past : BytesAt tail (BitVec.ofNat 64 outputBase) oldPrefix := by
    have data := ((bytes_at_append _ _ oldPrefix (lowBytes footer)).mp checked.data.output).1
    intro index inside
    change (footerTailSetupPrefix (footerDecisionPrefix built 2) 7).getByte _=_
    rw [footer_tail_setup_byte]
    exact data index inside
  have packedPrefix := footer_tail_prefix nodes footer tail outputBase metadata oldPrefix tailReady past outputFit
  let cycles := footerSubtreeCycles groups 1 8+2+7+tailTraverseCycles nodes.length tail+5
  refine ⟨openingFinishPrefix (tailTraverseState nodes.length tail) 4,cycles,?_,?_,?_,?_,?_⟩
  · intro fuel coins
    have packed := footer_tail_pack nodes footer tail _ _ tailReady tailPC fit (5+fuel) coins
    rw [show cycles+fuel=footerSubtreeCycles groups 1 8+(2+(7+(tailTraverseCycles nodes.length tail+(5+fuel)))) by
      dsimp only [cycles]; omega,run,footer_root_execution built builtPC root,
      footer_tail_setup_execution openingControllerImage 12972 controller_footer_tail_at.1 _ checkedPC]
    simp only [bind_assoc]
    change (do let result ← execute openingControllerImage (tailTraverseCycles nodes.length tail+(5+fuel)) tail coins
               return ((result.charge 7 0).charge 2 0).charge (footerSubtreeCycles groups 1 8) 0)=_
    rw [packed.1,opening_finish_execution _ packedPC fuel coins]
    simp only [pure_bind,Execution.charge]
    congr 2 <;> dsimp only [cycles] <;> omega
  · have packedMemory : BytesAt (tailTraverseState nodes.length tail) (BitVec.ofNat 64 outputBase) (oldPrefix++encode footer) := by
      apply (bytes_at_append _ _ oldPrefix (encode footer)).mpr
      refine ⟨packedPrefix,?_⟩
      rw [←BitVec.ofNat_add]
      exact (footer_tail_pack nodes footer tail _ _ tailReady tailPC fit 0 false).2.1
    intro index inside
    rw [opening_finish_byte]
    exact packedMemory index inside
  · rw [opening_finish_output]
    exact pointer
  · rw [opening_finish_length,pointer,packedBase,
      BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
    have difference : outputBase+oldPrefix.length+(encode footer).length-outputBase=oldPrefix.length+(encode footer).length := by omega
    rw [difference,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  · have subtree := footer_subtree_bound groups 1 8
    have tailBound := tail_traverse_bound nodes.length tail
    dsimp only [cycles]
    change footerSubtreeCycles groups 1 8+2+7+tailTraverseCycles nodes.length tail+5≤66448+13*nodes.length
    norm_num at subtree
    omega

theorem footer_complete_range_execution (groups : List Nat) (s : MachineState)
    (source output metadata : Nat) (proofBase : Word)
    (ready : FooterRangeReady groups (capFrontierNodes groups 1 8).length
      s 1 source output metadata 0 proofBase)
    (pc : s.pc=12408)
    (outputRoom : output+30*(capFrontierNodes groups 1 8).length+1≤MEMORY_BYTES) :
    ∃ after cycles, (∀ fuel coins, execute openingControllerImage (cycles+fuel) s coins=
      pure ⟨.success,after,cycles,0⟩) ∧
      cycles≤66448+13*(capFrontierNodes groups 1 8).length := by
  let nodes := capFrontierNodes groups 1 8
  obtain ⟨built,run,builtPC,builtReady⟩ := footer_subtree_range_execution groups 8 s 1 source output metadata 0 0
    proofBase (by simpa only [Nat.add_zero] using ready) cap_span_root pc
  have root : built.getReg .x30=1#64 := builtReady.cursor
  have checkedPC := footer_root_pc built builtPC root
  have fixed (reg : Reg) (notTemp : reg≠.x31) :
      (footerDecisionPrefix built 2).getReg reg=built.getReg reg := footer_root_register built root reg notTemp
  let tail := footerTailSetupPrefix (footerDecisionPrefix built 2) 7
  have tailPC : tail.pc=13000 := by
    dsimp only [tail]
    rw [footer_tail_setup_pc _ 7 (by decide),checkedPC]
    rfl
  have rows : (footerDecisionPrefix built 2).getReg .x19=BitVec.ofNat 64 nodes.length := by
    rw [fixed .x19 (by decide)]
    simpa only [Nat.zero_add] using builtReady.counter
  have table : (footerDecisionPrefix built 2).getReg .x7=BitVec.ofNat 64 (metadata+2*nodes.length) := by
    rw [fixed .x7 (by decide)]
    exact builtReady.metaPointer
  have sourcePointer : tail.getReg .x21=BitVec.ofNat 64 metadata :=
    footer_tail_setup_table _ metadata nodes.length table rows
  have outputPointer : tail.getReg .x20=BitVec.ofNat 64 (output+29*nodes.length) := by
    rw [footer_tail_setup_cursor,fixed .x6 (by decide)]
    exact builtReady.outputPointer
  have count : tail.getReg .x22=BitVec.ofNat 64 nodes.length := by
    rw [footer_tail_setup_count,rows]
  obtain ⟨packed,packedPC,_⟩ := tail_traverse_range_execution openingControllerImage 13000 controller_footer_tail_at.2
    nodes.length tail metadata (output+29*nodes.length) tailPC sourcePointer outputPointer count ready.capacity (by
      dsimp only [nodes] at *
      omega)
  let cycles := footerSubtreeCycles groups 1 8+2+7+tailTraverseCycles nodes.length tail+5
  refine ⟨openingFinishPrefix (tailTraverseState nodes.length tail) 4,cycles,?_,?_⟩
  · intro fuel coins
    rw [show cycles+fuel=footerSubtreeCycles groups 1 8+(2+(7+(tailTraverseCycles nodes.length tail+(5+fuel)))) by
      dsimp only [cycles]; omega,run,footer_root_execution built builtPC root,
      footer_tail_setup_execution openingControllerImage 12972 controller_footer_tail_at.1 _ checkedPC]
    simp only [bind_assoc]
    change (do let result ← execute openingControllerImage (tailTraverseCycles nodes.length tail+(5+fuel)) tail coins
               return ((result.charge 7 0).charge 2 0).charge (footerSubtreeCycles groups 1 8) 0)=_
    rw [packed,opening_finish_execution _ packedPC fuel coins]
    simp only [pure_bind,Execution.charge]
    congr 2 <;> dsimp only [cycles] <;> omega
  · have treeBound := footer_subtree_bound groups 1 8
    have tailBound := tail_traverse_bound nodes.length tail
    change cycles≤66448+13*nodes.length
    dsimp only [cycles]
    omega

end CommitGolfCandidate.Chained.Native
