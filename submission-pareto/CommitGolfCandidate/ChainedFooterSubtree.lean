import CommitGolfCandidate.ChainedFooterMoves

/-! Actual stackless footer traversal emits the recursively specified frontier. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

def footerSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 129
  | height+1 => if capIsMarked groups node (height+1) then
      19+footerSubtreeCycles groups (2*node) height+footerSubtreeCycles groups (2*node+1) height
    else 130

private theorem lookup_block {groups : List Nat} {fields : List RawField} {suffix outputPrefix metaPrefix : Proof}
    {s : MachineState} {node height source outputBase metaBase : Nat}
    (ready : FooterReady groups fields suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (span : CapSpan node height) (pc : s.pc=12408) :
    RunsFooterBlock s (footerLookupPrefix s 4) 4 :=
  fun fuel coins => footer_lookup_execution s pc
    (footer_lookup_access groups s node height ready.marks span ready.cursor) fuel coins

private theorem walk_unmarked {groups : List Nat} {field : RawField} {fields : List RawField}
    {suffix outputPrefix metaPrefix : Proof} {s : MachineState} {node height source outputBase metaBase : Nat}
    (ready : FooterReady groups (field::fields) suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (span : CapSpan node height) (pc : s.pc=12408) (mark : capIsMarked groups node height=false)
    (lowSize : field.low.length=29) (padding : field.padding=[])
    (highSize : field.high.length=InteriorCodec.footerWidth node-232) :
    ∃ after, RunsFooterBlock s after (4+(if node<256 then 126 else 125)) ∧ after.pc=12940 ∧
      FooterReady groups fields suffix (outputPrefix++field.low) (metaPrefix++descriptorBytes [field.high])
        after node (source+30) outputBase metaBase := by
  have nextPC : (footerLookupPrefix s 4).pc=12436 := by
    simpa only [mark,Bool.false_eq_true,↓reduceIte] using
      footer_lookup_dispatch groups s node height pc ready.marks span ready.cursor
  have bound := (cap_span_node node height span).2
  exact ⟨_,(lookup_block ready span pc).next (footer_ready_emit_run ready.lookup nextPC bound lowSize padding),
    footer_emit_pc _ nextPC,ready.lookup.emit lowSize padding highSize (by omega)⟩

theorem footer_subtree (groups : List Nat) (fields tailFields : List RawField) (suffix outputPrefix metaPrefix : Proof)
    (s : MachineState) (node height source outputBase metaBase : Nat)
    (layout : FooterLayout (capFrontierNodes groups node height) fields)
    (ready : FooterReady groups (fields++tailFields) suffix outputPrefix metaPrefix s node source outputBase metaBase)
    (span : CapSpan node height) (pc : s.pc=12408) :
    ∃ after, RunsFooterBlock s after (footerSubtreeCycles groups node height) ∧ after.pc=12940 ∧
      FooterReady groups tailFields suffix (outputPrefix++rawFieldsLow fields) (metaPrefix++rawFieldsMeta fields)
        after node (source+(rawFieldsBytes fields).length) outputBase metaBase := by
  induction height generalizing fields tailFields s node source outputPrefix metaPrefix with
  | zero =>
    cases mark : capIsMarked groups node 0
    · have single : FooterLayout [node] fields := by simpa only [capFrontierNodes,mark,Bool.false_eq_true,↓reduceIte] using layout
      cases single with
      | @cons _ _ field rest low padding high tail =>
        have empty := footer_layout_empty _ tail
        subst empty
        have leaf := cap_span_is_leaf node span
        have rawSize : (rawFieldsBytes [field]).length=30 := by
          simp only [rawFieldsBytes,List.flatMap_cons,List.flatMap_nil,List.append_nil,RawField.bytes,low,padding,
            List.length_append,List.length_cons,List.length_nil]
        simpa only [footerSubtreeCycles,mark,Bool.false_eq_true,↓reduceIte,show ¬node<256 by omega,rawFieldsLow,rawFieldsMeta,
          List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nil_append,rawSize] using
          walk_unmarked (fields := tailFields) ready span pc mark low padding high
    · have empty : fields=[] := footer_layout_empty _ (by simpa only [capFrontierNodes,mark,↓reduceIte] using layout)
      subst fields
      have looked := ready.lookup
      have nextPC : (footerLookupPrefix s 4).pc=12424 := by
        simpa only [mark,↓reduceIte] using footer_lookup_dispatch groups s node 0 pc ready.marks span ready.cursor
      have leaf : ¬footerWide (footerLookupPrefix s 4) := by
        rw [footer_wide_test _ node (cap_span_node node 0 span).2 looked.cursor looked.marks.limit]
        simpa only [decide_eq_true_eq] using (show ¬node<256 by
          have := cap_span_is_leaf node span
          omega)
      have block : RunsFooterBlock s (footerKnownPrefix (footerLookupPrefix s 4) 1) 5 :=
        (lookup_block ready span pc).next (fun fuel coins => footer_prune_execution _ nextPC fuel coins)
      refine ⟨_,?_,footer_prune_pc _ nextPC leaf,?_⟩
      · simpa only [footerSubtreeCycles,mark,↓reduceIte] using block
      · simpa only [rawFieldsLow,rawFieldsMeta,rawFieldsBytes,List.flatMap_nil,List.append_nil,List.nil_append,List.length_nil,Nat.add_zero] using looked.prune
  | succ height ih =>
    cases mark : capIsMarked groups node (height+1)
    · have single : FooterLayout [node] fields := by simpa only [capFrontierNodes,mark,Bool.false_eq_true,↓reduceIte] using layout
      cases single with
      | @cons _ _ field rest low padding high tail =>
        have empty := footer_layout_empty _ tail
        subst empty
        have internal := cap_span_is_internal node height span
        have rawSize : (rawFieldsBytes [field]).length=30 := by
          simp only [rawFieldsBytes,List.flatMap_cons,List.flatMap_nil,List.append_nil,RawField.bytes,low,padding,
            List.length_append,List.length_cons,List.length_nil]
        simpa only [footerSubtreeCycles,mark,Bool.false_eq_true,↓reduceIte,internal,rawFieldsLow,rawFieldsMeta,
          List.flatMap_cons,List.flatMap_nil,List.append_nil,List.nil_append,rawSize] using
          walk_unmarked (fields := tailFields) ready span pc mark low padding high
    · have combined : FooterLayout (capFrontierNodes groups (2*node) height++
          capFrontierNodes groups (2*node+1) height) fields := by
        simpa only [capFrontierNodes,mark,↓reduceIte] using layout
      obtain ⟨left,right,equal,leftLayout,rightLayout⟩ := footer_layout_split _ _ _ combined
      subst fields
      have looked := ready.lookup
      have nextPC : (footerLookupPrefix s 4).pc=12424 := by
        simpa only [mark,↓reduceIte] using footer_lookup_dispatch groups s node (height+1) pc ready.marks span ready.cursor
      have internal : footerWide (footerLookupPrefix s 4) := by
        rw [footer_wide_test _ node (cap_span_node node (height+1) span).2 looked.cursor looked.marks.limit]
        exact decide_eq_true (cap_span_is_internal node height span)
      have children := cap_span_children node height span
      have leftReady : FooterReady groups (left++(right++tailFields)) suffix outputPrefix metaPrefix
          (footerKnownPrefix (footerLookupPrefix s 4) 3) (2*node) source outputBase metaBase := by
        simpa only [List.append_assoc] using looked.descend internal
      obtain ⟨leftEnd,leftRun,leftPC,leftDone⟩ := ih left (right++tailFields) outputPrefix metaPrefix _ (2*node)
        source leftLayout leftReady children.1 (footer_descend_pc _ nextPC internal)
      have positive := (cap_span_node node (height+1) span).1
      obtain ⟨across,acrossPC,acrossReady⟩ := footer_move_sibling leftDone positive (cap_span_node _ _ children.1).2 leftPC
      obtain ⟨rightEnd,rightRun,rightPC,rightDone⟩ := ih right tailFields (outputPrefix++rawFieldsLow left)
        (metaPrefix++rawFieldsMeta left) _ (2*node+1) (source+(rawFieldsBytes left).length)
        rightLayout acrossReady children.2 acrossPC
      obtain ⟨up,upPC,upReady⟩ := footer_move_parent rightDone positive (cap_span_node _ _ children.2).2 rightPC
      have ran := (((((lookup_block ready span pc).next
        (fun fuel coins => footer_descend_execution _ nextPC internal fuel coins)).next leftRun).next across).next rightRun).next up
      refine ⟨_,?_,upPC,?_⟩
      · have accounting : 4+3+footerSubtreeCycles groups (2*node) height+6+
            footerSubtreeCycles groups (2*node+1) height+6=footerSubtreeCycles groups node (height+1) := by
          rw [footerSubtreeCycles,mark]
          simp only [↓reduceIte]
          omega
        rw [←accounting]
        exact ran
      · simpa only [rawFieldsLow,rawFieldsMeta,rawFieldsBytes,List.flatMap_append,List.length_append,
          List.append_assoc,Nat.add_assoc] using upReady

theorem footer_subtree_bound (groups : List Nat) (node height : Nat) :
    footerSubtreeCycles groups node height≤130*(2^(height+1)-1) := by
  induction height generalizing node with
  | zero => simp only [footerSubtreeCycles]; split <;> decide
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    rw [footerSubtreeCycles,Nat.pow_succ 2 (height+1)]
    have positive : 0<2^(height+1) := by positivity
    split <;> omega

theorem footer_range_unmarked (groups : List Nat) (remaining node height source output metadata count : Nat)
    (s : MachineState) (proofBase : Word)
    (ready : FooterRangeReady groups (remaining+1) s node source output metadata count proofBase)
    (span : CapSpan node height) (pc : s.pc=12408) (mark : capIsMarked groups node height=false) :
    ∃ after, RunsFooterBlock s after (4+(if node<256 then 126 else 125)) ∧ after.pc=12940 ∧
      FooterRangeReady groups remaining after node (source+30) (output+29) (metadata+2) (count+1) proofBase := by
  have nextPC : (footerLookupPrefix s 4).pc=12436 := by
    simpa only [mark,Bool.false_eq_true,↓reduceIte] using
      footer_lookup_dispatch groups s node height pc ready.marks span ready.cursor
  have looked := ready.lookup
  have bounded := (cap_span_node node height span).2
  have lookup : RunsFooterBlock s (footerLookupPrefix s 4) 4 :=
    fun fuel coins => footer_lookup_execution s pc
      (footer_lookup_access groups s node height ready.marks span ready.cursor) fuel coins
  have emit : RunsFooterBlock (footerLookupPrefix s 4) (footerEmitState (footerLookupPrefix s 4))
      (if node<256 then 126 else 125) := by
    intro fuel coins
    have separate := looked.separate
    have capacity := looked.capacity
    have run := footer_emit_execution _ nextPC source output metadata looked.sourcePointer looked.outputPointer
      looked.metaPointer looked.ordered (by omega) (by omega) fuel coins
    simpa only [footer_emit_cycles_node _ node bounded looked.cursor looked.marks.limit] using run
  exact ⟨_,lookup.next emit,footer_emit_pc _ nextPC,looked.emit⟩

theorem footer_subtree_range_execution (groups : List Nat) (height : Nat) (s : MachineState)
    (node source output metadata count tail : Nat) (proofBase : Word)
    (ready : FooterRangeReady groups ((capFrontierNodes groups node height).length+tail)
      s node source output metadata count proofBase)
    (span : CapSpan node height) (pc : s.pc=12408) :
    ∃ after, RunsFooterBlock s after (footerSubtreeCycles groups node height) ∧ after.pc=12940 ∧
      FooterRangeReady groups tail after node
        (source+30*(capFrontierNodes groups node height).length)
        (output+29*(capFrontierNodes groups node height).length)
        (metadata+2*(capFrontierNodes groups node height).length)
        (count+(capFrontierNodes groups node height).length) proofBase := by
  induction height generalizing s node source output metadata count tail with
  | zero =>
    cases mark : capIsMarked groups node 0
    · have oneReady : FooterRangeReady groups (tail+1) s node source output metadata count proofBase := by
        simpa only [capFrontierNodes,mark,Bool.false_eq_true,↓reduceIte,List.length_singleton,Nat.add_comm 1] using ready
      have leaf := cap_span_is_leaf node span
      simpa only [capFrontierNodes,footerSubtreeCycles,mark,Bool.false_eq_true,↓reduceIte,
        show ¬node<256 by omega,List.length_singleton,Nat.mul_one] using
        footer_range_unmarked groups tail node 0 source output metadata count s proofBase oneReady span pc mark
    · have looked := ready.lookup
      have nextPC : (footerLookupPrefix s 4).pc=12424 := by
        simpa only [mark,↓reduceIte] using footer_lookup_dispatch groups s node 0 pc ready.marks span ready.cursor
      have leaf : ¬footerWide (footerLookupPrefix s 4) := by
        rw [footer_wide_test _ node (cap_span_node node 0 span).2 looked.cursor looked.marks.limit]
        simpa only [decide_eq_true_eq] using (show ¬node<256 by have := cap_span_is_leaf node span; omega)
      have lookup : RunsFooterBlock s (footerLookupPrefix s 4) 4 :=
        fun fuel coins => footer_lookup_execution s pc
          (footer_lookup_access groups s node 0 ready.marks span ready.cursor) fuel coins
      have block : RunsFooterBlock s (footerKnownPrefix (footerLookupPrefix s 4) 1) 5 :=
        lookup.next (fun fuel coins => footer_prune_execution _ nextPC fuel coins)
      refine ⟨_,?_,footer_prune_pc _ nextPC leaf,?_⟩
      · simpa only [footerSubtreeCycles,mark,↓reduceIte] using block
      · simpa only [capFrontierNodes,mark,↓reduceIte,List.length_nil,Nat.zero_add,Nat.mul_zero,Nat.add_zero] using looked.prune
  | succ height ih =>
    cases mark : capIsMarked groups node (height+1)
    · have oneReady : FooterRangeReady groups (tail+1) s node source output metadata count proofBase := by
        simpa only [capFrontierNodes,mark,Bool.false_eq_true,↓reduceIte,List.length_singleton,Nat.add_comm 1] using ready
      have internal := cap_span_is_internal node height span
      simpa only [capFrontierNodes,footerSubtreeCycles,mark,Bool.false_eq_true,↓reduceIte,
        internal,List.length_singleton,Nat.mul_one] using
        footer_range_unmarked groups tail node (height+1) source output metadata count s proofBase oneReady span pc mark
    · have looked := ready.lookup
      have nextPC : (footerLookupPrefix s 4).pc=12424 := by
        simpa only [mark,↓reduceIte] using footer_lookup_dispatch groups s node (height+1) pc ready.marks span ready.cursor
      have internal : footerWide (footerLookupPrefix s 4) := by
        rw [footer_wide_test _ node (cap_span_node node (height+1) span).2 looked.cursor looked.marks.limit]
        exact decide_eq_true (cap_span_is_internal node height span)
      have children := cap_span_children node height span
      have leftReady : FooterRangeReady groups ((capFrontierNodes groups (2*node) height).length+
          ((capFrontierNodes groups (2*node+1) height).length+tail))
          (footerKnownPrefix (footerLookupPrefix s 4) 3) (2*node) source output metadata count proofBase := by
        simpa only [capFrontierNodes,mark,↓reduceIte,List.length_append,Nat.add_assoc] using looked.descend internal
      obtain ⟨leftEnd,leftRun,leftPC,leftDone⟩ := ih _ (2*node) source output metadata count
        ((capFrontierNodes groups (2*node+1) height).length+tail) leftReady children.1
        (footer_descend_pc _ nextPC internal)
      have positive := (cap_span_node node (height+1) span).1
      obtain ⟨across,acrossPC,acrossReady⟩ := footer_range_move_sibling leftDone positive (cap_span_node _ _ children.1).2 leftPC
      obtain ⟨rightEnd,rightRun,rightPC,rightDone⟩ := ih _ (2*node+1)
        (source+30*(capFrontierNodes groups (2*node) height).length)
        (output+29*(capFrontierNodes groups (2*node) height).length)
        (metadata+2*(capFrontierNodes groups (2*node) height).length)
        (count+(capFrontierNodes groups (2*node) height).length) tail acrossReady children.2 acrossPC
      obtain ⟨up,upPC,upReady⟩ := footer_range_move_parent rightDone positive (cap_span_node _ _ children.2).2 rightPC
      have lookup : RunsFooterBlock s (footerLookupPrefix s 4) 4 :=
        fun fuel coins => footer_lookup_execution s pc
          (footer_lookup_access groups s node (height+1) ready.marks span ready.cursor) fuel coins
      have ran := (((((lookup.next
        (fun fuel coins => footer_descend_execution _ nextPC internal fuel coins)).next leftRun).next across).next rightRun).next up)
      refine ⟨_,?_,upPC,?_⟩
      · have accounting : 4+3+footerSubtreeCycles groups (2*node) height+6+
            footerSubtreeCycles groups (2*node+1) height+6=footerSubtreeCycles groups node (height+1) := by
          rw [footerSubtreeCycles,mark]
          simp only [↓reduceIte]
          omega
        rw [←accounting]
        exact ran
      · simpa only [capFrontierNodes,mark,↓reduceIte,List.length_append,Nat.mul_add,Nat.add_assoc] using upReady

end CommitGolfCandidate.Chained.Native
