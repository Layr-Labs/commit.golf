import CommitGolfCandidate.ChainedCheckerFooterControl
import CommitGolfCandidate.ChainedFooterFrame

section

/-! Trusted width-prefix, mark and ABI frames for the installed footer DFS. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

def checkerFooterHighWidth (node : Nat) : Nat := InteriorCodec.footerWidth node-232

structure CheckerFooterWidthsReady (groups priorWidths : List Nat) (origin s : MachineState) (node : Nat) : Prop where
  base : s.getReg .x4=4096
  limit : s.getReg .x29=256
  marks : ∀ index, index<512 → s.getMem (BitVec.ofNat 64 (4096+8*index))=markWord groups index
  cursor : s.getReg .x30=BitVec.ofNat 64 node
  metadata : s.getReg .x7=BitVec.ofNat 64 (checkingMetadataBase+2*priorWidths.length)
  count : s.getReg .x22=BitVec.ofNat 64 priorWidths.length
  capacity : priorWidths.length≤256
  widths : ParseWidthsAt s (BitVec.ofNat 64 checkingMetadataBase) priorWidths
  outside : ∀ query, (query<checkingMetadataBase ∨ checkingMetadataBase+512≤query) → query<2^64 →
    s.getByte (BitVec.ofNat 64 query)=origin.getByte (BitVec.ofNat 64 query)
  registers : ∀ reg, reg∉[.x7,.x9,.x10,.x22,.x30,.x31] → s.getReg reg=origin.getReg reg

theorem CheckerFooterWidthsReady.move {groups priorWidths : List Nat} {origin s after : MachineState} {node next : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node)
    (cursor : after.getReg .x30=BitVec.ofNat 64 next)
    (register : ∀ reg, reg≠.x30 → reg≠.x31 → after.getReg reg=s.getReg reg)
    (memory : ∀ query, after.getMem query=s.getMem query)
    (bytes : ∀ query, after.getByte query=s.getByte query) :
    CheckerFooterWidthsReady groups priorWidths origin after next := by
  refine ⟨?_,?_,?_,cursor,?_,?_,ready.capacity,?_,?_,?_⟩
  · rw [register .x4 (by decide) (by decide)]; exact ready.base
  · rw [register .x29 (by decide) (by decide)]; exact ready.limit
  · intro index inside; rw [memory]; exact ready.marks index inside
  · rw [register .x7 (by decide) (by decide)]; exact ready.metadata
  · rw [register .x22 (by decide) (by decide)]; exact ready.count
  · intro index inside; rw [bytes]; exact ready.widths index inside
  · intro query outside fit; rw [bytes]; exact ready.outside query outside fit
  · intro reg kept
    cases reg <;> simp at kept
    all_goals rw [register _ (by decide) (by decide)]; exact ready.registers _ (by decide)

theorem checker_footer_width_word_frame (s : MachineState) (node metadata address : Nat)
    (fit : node<2^64) (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256)
    (pointer : s.getReg .x7=BitVec.ofNat 64 metadata)
    (metaFit : metadata+2<2^64) (addressFit : address+8<2^64) (aligned : address%8=0)
    (apart : address+8≤metadata ∨ metadata+2≤address) :
    (checkerFooterWidthState s).getMem (BitVec.ofNat 64 address)=s.getMem (BitVec.ofNat 64 address) := by
  apply aligned_word_of_byte_frame s _ address aligned
  intro index inside
  rw [checker_footer_width_byte s node fit cursor limit]
  apply ite_eq_right
  rw [pointer]
  change BitVec.ofNat 64 (address+index)≠BitVec.ofNat 64 metadata+BitVec.ofNat 64 1
  rw [←BitVec.ofNat_add]
  apply word_of_nat_ne _ _ (by omega) (by omega)
  rcases apart with left | right <;> omega

theorem checker_footer_width_access {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) :
    accessValid (s.getReg .x7+1) 1=true := by
  have count := ready.capacity
  have room := checking_metadata_room
  have memoryRoom : checkingMetadataBase+514≤MEMORY_BYTES := by decide +kernel
  rw [ready.metadata]
  change accessValid (BitVec.ofNat 64 (checkingMetadataBase+2*priorWidths.length)+BitVec.ofNat 64 1) 1=true
  rw [←BitVec.ofNat_add]
  have fit : checkingMetadataBase+2*priorWidths.length+1<2^64 := by omega
  have natural : (BitVec.ofNat 64 (checkingMetadataBase+2*priorWidths.length+1)).toNat=
      checkingMetadataBase+2*priorWidths.length+1 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  simp only [accessValid,rangeValid,natural]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  omega

theorem CheckerFooterWidthsReady.emit {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) (bounded : node<512) (space : priorWidths.length<256) :
    CheckerFooterWidthsReady groups (priorWidths++[checkerFooterHighWidth node]) origin (checkerFooterWidthState s) node := by
  have room := checking_metadata_room
  have fit : node<2^64 := by omega
  have location : s.getReg .x7+1#64=
      BitVec.ofNat 64 checkingMetadataBase+BitVec.ofNat 64 (2*priorWidths.length+1) := by
    rw [ready.metadata]
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add,Nat.add_assoc]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [checker_footer_width_register _ .x4 (by decide)]; exact ready.base
  · rw [checker_footer_width_register _ .x29 (by decide)]; exact ready.limit
  · intro index inside
    rw [checker_footer_width_word_frame s node (checkingMetadataBase+2*priorWidths.length) (4096+8*index)
      fit ready.cursor ready.limit ready.metadata (by omega) (by omega) (by omega) (Or.inl (by
        have low : 8192≤checkingMetadataBase := by decide +kernel
        omega))]
    exact ready.marks index inside
  · rw [checker_footer_width_register _ .x30 (by decide)]; exact ready.cursor
  · rw [checker_footer_width_pointer,ready.metadata,List.length_append,List.length_singleton]
    change BitVec.ofNat 64 (checkingMetadataBase+2*priorWidths.length)+BitVec.ofNat 64 2=_
    rw [←BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [checker_footer_width_count,ready.count,List.length_append,List.length_singleton]
    change BitVec.ofNat 64 priorWidths.length+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  · simp only [List.length_append,List.length_singleton]
    omega
  · intro index inside
    simp only [List.length_append,List.length_singleton] at inside
    by_cases before : index<priorWidths.length
    · have away : BitVec.ofNat 64 checkingMetadataBase+BitVec.ofNat 64 (2*index+1)≠s.getReg .x7+1 := by
        change _≠s.getReg .x7+1#64
        rw [location]
        intro equal
        have same := byte_offset_inj (BitVec.ofNat 64 checkingMetadataBase) (2*index+1) (2*priorWidths.length+1)
          (by omega) (by omega) equal
        omega
      rw [checker_footer_width_byte s node fit ready.cursor ready.limit,ite_eq_right away,
        List.getD_append _ _ _ _ before]
      exact ready.widths index before
    · have last : index=priorWidths.length := by omega
      subst index
      have address : BitVec.ofNat 64 checkingMetadataBase+BitVec.ofNat 64 (2*priorWidths.length+1)=s.getReg .x7+1 := by
        change _=s.getReg .x7+1#64
        exact location.symm
      rw [checker_footer_width_byte s node fit ready.cursor ready.limit,ite_eq_left address,
        List.getD_append_right _ _ _ _ (by omega),Nat.sub_self]
      rfl
  · intro query outside queryFit
    rw [checker_footer_width_byte s node fit ready.cursor ready.limit]
    have away : BitVec.ofNat 64 query≠s.getReg .x7+1 := by
      rw [ready.metadata]
      change BitVec.ofNat 64 query≠BitVec.ofNat 64 (checkingMetadataBase+2*priorWidths.length)+BitVec.ofNat 64 1
      rw [←BitVec.ofNat_add]
      apply word_of_nat_ne _ _ queryFit (by omega)
      rcases outside with left | right <;> omega
    rw [ite_eq_right away]
    exact ready.outside query outside queryFit
  · intro reg kept
    cases reg <;> simp at kept
    all_goals rw [checker_footer_width_register _ _ (by decide)]; exact ready.registers _ (by decide)

theorem checker_footer_widths_initial (groups : List Nat) (s : MachineState)
    (base : s.getReg .x4=4096) (limit : s.getReg .x29=256)
    (marks : ∀ index, index<512 → s.getMem (BitVec.ofNat 64 (4096+8*index))=markWord groups index)
    (cursor : s.getReg .x30=1) (metadata : s.getReg .x7=BitVec.ofNat 64 checkingMetadataBase) (count : s.getReg .x22=0) :
    CheckerFooterWidthsReady groups [] s s 1 := by
  refine ⟨base,limit,marks,cursor,?_,count,by decide,?_,?_,?_⟩
  · simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using metadata
  · intro index inside; simp at inside
  · intro query outside fit; rfl
  · intro reg kept; rfl

end CommitGolfCandidate.Chained.Native

end

section

/-! Compose installed DFS edges while preserving trusted widths and physical ABI frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

def RunsCheckerFooterBlock (before after : MachineState) (cycles : Nat) : Prop :=
  ∀ fuel coins, execute (Artifact.submission.image .check) (cycles+fuel) before coins=
    (do let result ← execute (Artifact.submission.image .check) fuel after coins
        return result.charge cycles 0)

theorem RunsCheckerFooterBlock.next {before middle after : MachineState} {a b : Nat}
    (first : RunsCheckerFooterBlock before middle a) (second : RunsCheckerFooterBlock middle after b) :
    RunsCheckerFooterBlock before after (a+b) := by
  intro fuel coins
  rw [Nat.add_assoc,first (b+fuel) coins,second fuel coins]
  simp [Execution.charge,←Nat.add_assoc]

theorem checker_footer_wide_test (s : MachineState) (node : Nat) (bounded : node<512)
    (cursor : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256) :
    footerWide s=decide (node<256) := by
  rw [footerWide,cursor,limit,BitVec.ult_eq_decide]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : node<2^64)]
  rfl

theorem checker_footer_node_low_bit (node : Nat) (bounded : node<512) :
    BitVec.ofNat 64 node&&&1#64=BitVec.ofNat 64 (node%2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : node<2^64)]
  rw [Nat.mod_eq_of_lt (by omega : node%2<2^64)]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

theorem checker_footer_lookup_access {groups priorWidths : List Nat} {origin s : MachineState} {node height : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) (span : CapSpan node height) :
    accessValid (checkerFooterMarkAddress s) 8=true := by
  rw [checker_footer_mark_address s node ready.base ready.cursor]
  have bound := (cap_span_node node height span).2
  have natural : (BitVec.ofNat 64 (4096+8*node)).toNat=4096+8*node := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [accessValid,rangeValid,natural,MEMORY_BYTES]
  omega

theorem CheckerFooterWidthsReady.lookup {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) :
    CheckerFooterWidthsReady groups priorWidths origin (checkerFooterLookupState s) node := by
  apply ready.move
  · rw [checker_footer_lookup_register _ .x30 (by decide)]; exact ready.cursor
  · intro reg first second; exact checker_footer_lookup_register s reg second
  · exact checker_footer_lookup_memory s
  · exact checker_footer_lookup_byte s

theorem CheckerFooterWidthsReady.descend {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) (internal : footerWide s) :
    CheckerFooterWidthsReady groups priorWidths origin (checkerFooterKnownPrefix s 3) (2*node) := by
  apply ready.move
  · rw [checker_footer_descend_node s internal,ready.cursor,BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 node*BitVec.ofNat 64 2=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm node]
  · intro reg first second; exact checker_footer_descend_register s internal reg first
  · exact checker_footer_descend_memory s internal
  · exact checker_footer_descend_byte s internal

theorem CheckerFooterWidthsReady.prune {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) :
    CheckerFooterWidthsReady groups priorWidths origin (checkerFooterKnownPrefix s 1) node := by
  apply ready.move
  · rw [checker_footer_prune_register]; exact ready.cursor
  · intro reg first second; exact checker_footer_prune_register s reg
  · exact checker_footer_prune_memory s
  · exact checker_footer_prune_byte s

theorem CheckerFooterWidthsReady.decision {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) :
    CheckerFooterWidthsReady groups priorWidths origin (checkerFooterDecisionPrefix s 4) node := by
  apply ready.move
  · rw [checker_footer_decision_register _ .x30 (by decide)]; exact ready.cursor
  · intro reg first second; exact checker_footer_decision_register s reg second
  · exact checker_footer_decision_memory s
  · exact checker_footer_decision_byte s

theorem checker_footer_move_sibling {groups priorWidths : List Nat} {origin s : MachineState} {parent : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s (2*parent))
    (positive : 0<parent) (bounded : 2*parent<512) (pc : s.pc=4096+4*2182) :
    let after := checkerFooterSiblingPrefix (checkerFooterDecisionPrefix s 4) 2
    RunsCheckerFooterBlock s after 6 ∧ after.pc=4096+4*2168 ∧
    CheckerFooterWidthsReady groups priorWidths origin after (2*parent+1) := by
  have notRoot : s.getReg .x30≠1#64 := by
    rw [ready.cursor]
    exact word_of_nat_ne _ _ (by omega) (by decide) (by omega)
  have even : s.getReg .x30&&&1#64=0#64 := by
    rw [ready.cursor,checker_footer_node_low_bit _ bounded,show (2*parent)%2=0 by omega]
  have nextPC : (checkerFooterDecisionPrefix s 4).pc=4096+4*2188 := by
    rw [checker_footer_decision_pc s pc notRoot,ite_eq_left even]
  dsimp only
  refine ⟨(show RunsCheckerFooterBlock s (checkerFooterDecisionPrefix s 4) 4 from
    fun fuel coins => checker_footer_decision_execution s pc notRoot fuel coins).next
    (fun fuel coins => checker_footer_sibling_execution _ nextPC fuel coins),checker_footer_sibling_pc _ nextPC,?_⟩
  apply ready.decision.move
  · rw [checker_footer_sibling_node,checker_footer_decision_register _ .x30 (by decide),ready.cursor]
    change BitVec.ofNat 64 (2*parent)+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  · intro reg first second; exact checker_footer_sibling_register _ reg first
  · exact checker_footer_sibling_memory _
  · exact checker_footer_sibling_byte _

theorem checker_footer_move_parent {groups priorWidths : List Nat} {origin s : MachineState} {parent : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s (2*parent+1))
    (positive : 0<parent) (bounded : 2*parent+1<512) (pc : s.pc=4096+4*2182) :
    let after := checkerFooterParentPrefix (checkerFooterDecisionPrefix s 4) 2
    RunsCheckerFooterBlock s after 6 ∧ after.pc=4096+4*2182 ∧
    CheckerFooterWidthsReady groups priorWidths origin after parent := by
  have notRoot : s.getReg .x30≠1#64 := by
    rw [ready.cursor]
    exact word_of_nat_ne _ _ (by omega) (by decide) (by omega)
  have odd : s.getReg .x30&&&1#64≠0#64 := by
    rw [ready.cursor,checker_footer_node_low_bit _ bounded,show (2*parent+1)%2=1 by omega]
    decide
  have nextPC : (checkerFooterDecisionPrefix s 4).pc=4096+4*2186 := by
    rw [checker_footer_decision_pc s pc notRoot,ite_eq_right odd]
  dsimp only
  refine ⟨(show RunsCheckerFooterBlock s (checkerFooterDecisionPrefix s 4) 4 from
    fun fuel coins => checker_footer_decision_execution s pc notRoot fuel coins).next
    (fun fuel coins => checker_footer_parent_execution _ nextPC fuel coins),checker_footer_parent_pc _ nextPC,?_⟩
  apply ready.decision.move
  · rw [checker_footer_parent_node,checker_footer_decision_register _ .x30 (by decide),ready.cursor]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 2*parent+1<2^64),Nat.mod_eq_of_lt (by omega : parent<2^64)]
    omega
  · intro reg first second; exact checker_footer_parent_register _ reg first
  · exact checker_footer_parent_memory _
  · exact checker_footer_parent_byte _

end CommitGolfCandidate.Chained.Native

end

section

/-! Installed footer DFS constructs exactly the cap-frontier width table. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

def checkerFooterWidthSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 10
  | height+1 => if capIsMarked groups node (height+1) then
      19+checkerFooterWidthSubtreeCycles groups (2*node) height+
        checkerFooterWidthSubtreeCycles groups (2*node+1) height
    else 11

private theorem merged_ChainedCheckerFooterSubtree_lookup_block {groups priorWidths : List Nat} {origin s : MachineState} {node height : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) (span : CapSpan node height)
    (pc : s.pc=4096+4*2168) : RunsCheckerFooterBlock s (checkerFooterLookupState s) 4 :=
  fun fuel coins => checker_footer_lookup_execution s pc (checker_footer_lookup_access ready span) fuel coins

private theorem merged_ChainedCheckerFooterSubtree_emit_block {groups priorWidths : List Nat} {origin s : MachineState} {node : Nat}
    (ready : CheckerFooterWidthsReady groups priorWidths origin s node) (bounded : node<512)
    (pc : s.pc=4096+4*2175) :
    RunsCheckerFooterBlock s (checkerFooterWidthState s) (if node<256 then 7 else 6) := by
  intro fuel coins
  rw [←checker_footer_width_cycles s node bounded ready.cursor ready.limit]
  exact checker_footer_width_execution s pc (checker_footer_width_access ready) fuel coins

theorem checker_footer_widths_subtree (groups : List Nat) (height : Nat) (origin s : MachineState)
    (node : Nat) (priorWidths : List Nat) (ready : CheckerFooterWidthsReady groups priorWidths origin s node)
    (span : CapSpan node height) (pc : s.pc=4096+4*2168)
    (space : priorWidths.length+(capFrontierNodes groups node height).length≤256) :
    ∃ after, RunsCheckerFooterBlock s after (checkerFooterWidthSubtreeCycles groups node height) ∧
      after.pc=4096+4*2182 ∧
      CheckerFooterWidthsReady groups (priorWidths++(capFrontierNodes groups node height).map checkerFooterHighWidth) origin after node := by
  induction height generalizing s node priorWidths with
  | zero =>
    have bounded := (cap_span_node node 0 span).2
    have leafBound := cap_span_is_leaf node span
    have looked := ready.lookup
    cases mark : capIsMarked groups node 0 with
    | false =>
      have nextPC : (checkerFooterLookupState s).pc=4096+4*2175 := by
        simpa [mark,↓reduceIte] using
          checker_footer_lookup_dispatch groups s node 0 pc ready.base ready.cursor span ready.marks
      have room : priorWidths.length<256 := by
        simp [capFrontierNodes,mark,↓reduceIte,List.length_cons,List.length_nil] at space
        omega
      have ran := (merged_ChainedCheckerFooterSubtree_lookup_block ready span pc).next (merged_ChainedCheckerFooterSubtree_emit_block looked bounded nextPC)
      refine ⟨_,?_,checker_footer_width_pc _ nextPC,?_⟩
      · simpa [checkerFooterWidthSubtreeCycles,mark,↓reduceIte,ite_eq_right (by omega : ¬node<256)] using ran
      · simpa [capFrontierNodes,mark,↓reduceIte,List.map_cons,List.map_nil] using looked.emit bounded room
    | true =>
      have nextPC : (checkerFooterLookupState s).pc=4096+4*2172 := by
        simpa [mark,↓reduceIte] using
          checker_footer_lookup_dispatch groups s node 0 pc ready.base ready.cursor span ready.marks
      have leaf : ¬footerWide (checkerFooterLookupState s) := by
        rw [checker_footer_wide_test _ node bounded looked.cursor looked.limit]
        simp [decide_eq_true_eq]
        omega
      have ran := (merged_ChainedCheckerFooterSubtree_lookup_block ready span pc).next
        (fun fuel coins => checker_footer_prune_execution _ nextPC fuel coins)
      refine ⟨_,?_,checker_footer_prune_pc _ nextPC leaf,?_⟩
      · simpa [checkerFooterWidthSubtreeCycles,mark,↓reduceIte] using ran
      · simpa [capFrontierNodes,mark,↓reduceIte,List.map_nil,List.append_nil] using looked.prune
  | succ height ih =>
    have bounded := (cap_span_node node (height+1) span).2
    have internalBound := cap_span_is_internal node height span
    have looked := ready.lookup
    cases mark : capIsMarked groups node (height+1) with
    | false =>
      have nextPC : (checkerFooterLookupState s).pc=4096+4*2175 := by
        simpa [mark,↓reduceIte] using
          checker_footer_lookup_dispatch groups s node (height+1) pc ready.base ready.cursor span ready.marks
      have room : priorWidths.length<256 := by
        simp [capFrontierNodes,mark,↓reduceIte,List.length_cons,List.length_nil] at space
        omega
      have ran := (merged_ChainedCheckerFooterSubtree_lookup_block ready span pc).next (merged_ChainedCheckerFooterSubtree_emit_block looked bounded nextPC)
      refine ⟨_,?_,checker_footer_width_pc _ nextPC,?_⟩
      · simpa [checkerFooterWidthSubtreeCycles,mark,↓reduceIte,ite_eq_left internalBound] using ran
      · simpa [capFrontierNodes,mark,↓reduceIte,List.map_cons,List.map_nil] using looked.emit bounded room
    | true =>
      have nextPC : (checkerFooterLookupState s).pc=4096+4*2172 := by
        simpa [mark,↓reduceIte] using
          checker_footer_lookup_dispatch groups s node (height+1) pc ready.base ready.cursor span ready.marks
      have internal : footerWide (checkerFooterLookupState s) := by
        rw [checker_footer_wide_test _ node bounded looked.cursor looked.limit]
        exact decide_eq_true internalBound
      have children := cap_span_children node height span
      have room : priorWidths.length+(capFrontierNodes groups (2*node) height).length+
          (capFrontierNodes groups (2*node+1) height).length≤256 := by
        simpa [capFrontierNodes,mark,↓reduceIte,List.length_append,Nat.add_assoc] using space
      have leftSpace : priorWidths.length+(capFrontierNodes groups (2*node) height).length≤256 := by omega
      obtain ⟨leftEnd,leftRun,leftPC,leftDone⟩ := ih _ (2*node) priorWidths (looked.descend internal)
        children.1 (checker_footer_descend_pc _ nextPC internal) leftSpace
      have positive := (cap_span_node node (height+1) span).1
      obtain ⟨across,acrossPC,acrossReady⟩ := checker_footer_move_sibling leftDone positive
        (cap_span_node _ _ children.1).2 leftPC
      have rightSpace : (priorWidths++(capFrontierNodes groups (2*node) height).map checkerFooterHighWidth).length+
          (capFrontierNodes groups (2*node+1) height).length≤256 := by
        simpa [List.length_append,List.length_map] using room
      obtain ⟨rightEnd,rightRun,rightPC,rightDone⟩ := ih _ (2*node+1)
        (priorWidths++(capFrontierNodes groups (2*node) height).map checkerFooterHighWidth)
        acrossReady children.2 acrossPC rightSpace
      obtain ⟨up,upPC,upReady⟩ := checker_footer_move_parent rightDone positive
        (cap_span_node _ _ children.2).2 rightPC
      have ran := (((((merged_ChainedCheckerFooterSubtree_lookup_block ready span pc).next
        (fun fuel coins => checker_footer_descend_execution _ nextPC internal fuel coins)).next leftRun).next across).next rightRun).next up
      refine ⟨_,?_,upPC,?_⟩
      · have accounting : 4+3+checkerFooterWidthSubtreeCycles groups (2*node) height+6+
            checkerFooterWidthSubtreeCycles groups (2*node+1) height+6=checkerFooterWidthSubtreeCycles groups node (height+1) := by
          rw [checkerFooterWidthSubtreeCycles,mark]
          simp [↓reduceIte]
          omega
        rw [←accounting]
        exact ran
      · simpa [capFrontierNodes,mark,↓reduceIte,List.map_append,List.append_assoc] using upReady

theorem checker_footer_widths_subtree_bound (groups : List Nat) (node height : Nat) :
    checkerFooterWidthSubtreeCycles groups node height+19≤29*2^height := by
  induction height generalizing node with
  | zero => simp [checkerFooterWidthSubtreeCycles]; split <;> decide
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have positive : 0<2^height := by positivity
    rw [checkerFooterWidthSubtreeCycles,Nat.pow_succ]
    split <;> omega

theorem checker_footer_frontier_count (groups : List Nat) (node height : Nat) :
    (capFrontierNodes groups node height).length≤2^height := by
  induction height generalizing node with
  | zero => simp [capFrontierNodes]; split <;> simp
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have positive : 0<2^height := by positivity
    rw [capFrontierNodes,Nat.pow_succ]
    split <;> simp [List.length_append,List.length_cons,List.length_nil] <;> omega

theorem checker_footer_high_width_small (node : Nat) : checkerFooterHighWidth node≤6 := by
  have upper : InteriorCodec.footerWidth node≤238 := by
    unfold InteriorCodec.footerWidth
    split <;> omega
  change InteriorCodec.footerWidth node-232≤6
  omega

theorem checker_footer_widths_complete (groups : List Nat) (origin s : MachineState)
    (ready : CheckerFooterWidthsReady groups [] origin s 1) (pc : s.pc=4096+4*2168) :
    ∃ after cycles, RunsCheckerFooterBlock s after cycles ∧ cycles≤7407 ∧ after.pc=4096+4*2190 ∧
      CheckerFooterWidthsReady groups ((capFrontierNodes groups 1 8).map checkerFooterHighWidth) origin after 1 := by
  obtain ⟨beforeRoot,ran,rootPC,done⟩ := checker_footer_widths_subtree groups 8 origin s 1 [] ready cap_span_root pc
    (by simpa using checker_footer_frontier_count groups 1 8)
  have root : beforeRoot.getReg .x30=1#64 := done.cursor
  refine ⟨checkerFooterDecisionPrefix beforeRoot 2,checkerFooterWidthSubtreeCycles groups 1 8+2,
    ran.next (fun fuel coins => checker_footer_root_execution beforeRoot rootPC root fuel coins),?_,
    checker_footer_root_pc beforeRoot rootPC root,?_⟩
  · have bound := checker_footer_widths_subtree_bound groups 1 8
    rw [show 29*2^8=7424 by decide] at bound
    omega
  · simp [List.nil_append] at done
    apply done.move
    · rw [checker_footer_root_register beforeRoot root .x30 (by decide)]; exact done.cursor
    · intro reg first second; exact checker_footer_root_register beforeRoot root reg second
    · exact checker_footer_root_memory beforeRoot root
    · exact checker_footer_root_byte beforeRoot root

end CommitGolfCandidate.Chained.Native

end
