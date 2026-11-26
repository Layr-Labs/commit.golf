import CommitGolfCandidate.ChainedCheckerCapRefinement

/-! In-heap frames for the delivered cap DFS and its recorded path composition. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker (CapPosition)
open RecordLeaf CheckerCap CheckerCap.Visit
set_option maxRecDepth 8192
attribute [local irreducible] capTreeTrace capLookup capAfterTests capRight

theorem cap_interval_parent_apart (node height query : Nat)
    (outside : query<node ∨ (node+1)*2^height≤query) : query≠node := by
  have grow := Nat.le_mul_of_pos_right (node+1) (by positivity : 0<2^height)
  omega

theorem cap_interval_children (node height query : Nat)
    (outside : query<node ∨ (node+1)*2^(height+1)≤query) :
    (query<2*node ∨ (2*node+1)*2^height≤query) ∧
      (query<2*node+1 ∨ (2*node+2)*2^height≤query) ∧
      query≠node ∧ query≠2*node ∧ query≠2*node+1 := by
  have upper : (node+1)*2^(height+1)=(2*node+2)*2^height := by rw [Nat.pow_succ]; ring
  have left := Nat.mul_le_mul_right (2^height) (by omega : 2*node+1≤2*node+2)
  have grow := Nat.le_mul_of_pos_right (2*node+2) (by positivity : 0<2^height)
  rw [upper] at outside
  omega

theorem cap_tree_unmarked_heap_word_frame {groups : List Nat} {state out : MachineState}
    {node height pointer finish : Nat} (small : height≤8) (position : CapPosition groups state node pointer)
    (span : TwoPermutationPrototype.Opening.CapSpan node height)
    (endReg : state.getReg .x22=BitVec.ofNat 64 finish) (endBound : finish≤MEMORY_BYTES)
    (room : pointer+30≤finish) (marked : capIsMarked groups node height=false)
    (reached : out∈support (capTreeTrace groups height small node state))
    (query : Nat) (queryBound : query<512) (apart : query≠node) (word : Fin 4) :
    out.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val))=
      state.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val)) := by
  rw [(cap_tree_unmarked groups height small node state marked).1] at reached
  simp only [support_pure,Set.mem_singleton_iff] at reached
  subst out
  obtain ⟨target,next,mem⟩ := cap_lookup_position position span
  have looked : CapPosition groups (capLookup state) node pointer := by simpa [marked] using next
  have ready : FrontierReady (capLookup state) node pointer :=
    ⟨by simpa [marked] using target,looked.heap,looked.context.controls.roots,looked.proof,
      (TwoPermutationPrototype.Opening.cap_span_node node height span).2,looked.above,looked.even,by omega⟩
  have finishReg : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
    ((cap_lookup_stable state) .x22 (by decide)).trans endReg
  have fits := cap_frontier_fits looked finishReg endBound room
  exact (cap_frontier_heap_word_frame _ node pointer ready fits query queryBound apart word).trans (congrFun mem _)

theorem cap_tree_heap_word_frame (groups : List Nat) (height finish : Nat) (endBound : finish≤MEMORY_BYTES) :
    ∀ (small : height≤8) (node pointer : Nat) (state out : MachineState),
    CapPosition groups state node pointer → TwoPermutationPrototype.Opening.CapSpan node height →
    state.pc=4096+4*2661 → state.getReg .x22=BitVec.ofNat 64 finish →
    pointer+30*(capFrontierNodes groups node height).length≤finish →
    out∈support (capTreeTrace groups height small node state) →
    ∀ query, query<512 → (query<node ∨ (node+1)*2^height≤query) → ∀ word : Fin 4,
    out.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val))=
      state.getMem (BitVec.ofNat 64 (16384+32*query+8*word.val)) := by
  induction height with
  | zero =>
    intro small node pointer state out position span pc endReg room reached query queryBound outside word
    by_cases marked : capIsMarked groups node 0=true
    · simp only [capTreeTrace,marked,ite_true,support_pure,Set.mem_singleton_iff] at reached
      subst out
      exact congrFun (cap_lookup_position position span).2.2 _
    · have unmarked : capIsMarked groups node 0=false := by simpa using marked
      exact cap_tree_unmarked_heap_word_frame small position span endReg endBound
        (by simpa [capFrontierNodes,unmarked] using room) unmarked reached query queryBound
        (cap_interval_parent_apart node 0 query outside) word
  | succ height ih =>
    intro small node pointer state out position span pc endReg room reached query queryBound outside word
    by_cases marked : capIsMarked groups node (height+1)=true
    · have children := TwoPermutationPrototype.Opening.cap_span_children node height span
      have fields : (capFrontierNodes groups node (height+1)).length=
          (capFrontierNodes groups (2*node) height).length+(capFrontierNodes groups (2*node+1) height).length := by
        simp [capFrontierNodes,marked]
      rw [fields] at room
      have bound : 0<node ∧ 2*node<512 := by
        have := (TwoPermutationPrototype.Opening.cap_span_node node (height+1) span).1
        have := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
        omega
      obtain ⟨target,next,mem⟩ := cap_lookup_position position span
      have leftPC : (capLookup state).pc=4096+4*2661 := by simpa [marked] using target
      have leftPos : CapPosition groups (capLookup state) (2*node) pointer := by simpa [marked] using next
      have leftEnd : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
        ((cap_lookup_stable state) .x22 (by decide)).trans endReg
      have leftOk := cap_tree_correct groups height finish endBound (by omega) (2*node) pointer
        (capLookup state) leftPos children.1 leftPC leftEnd (by omega)
      simp only [capTreeTrace,marked,ite_true,mem_support_bind_iff] at reached
      obtain ⟨left,reachedLeft,right,reachedRight,reachedParent⟩ := reached
      have postLeft := leftOk.post left reachedLeft
      have sibling := cap_sibling_position postLeft.2.1 postLeft.1 bound
      have stable := ((cap_lookup_stable state).trans postLeft.2.2.1).trans
        ((cap_tests_stable left).trans (cap_right_stable (capAfterTests left)))
      have rightEnd := (stable .x22 (by decide)).trans endReg
      have rightOk := cap_tree_correct groups height finish endBound (by omega) (2*node+1)
        (pointer+30*(capFrontierNodes groups (2*node) height).length) (capRight (capAfterTests left))
        sibling.2.1 children.2 sibling.1 rightEnd (by omega)
      have postRight := rightOk.post right reachedRight
      let parent : Fin 256 := ⟨node,TwoPermutationPrototype.Opening.cap_span_is_internal node height span⟩
      let level : Fin 8 := ⟨height,by omega⟩
      have ascend := cap_ascend_ready level parent span right postRight.2.1 postRight.1
      rcases cap_interval_children node height query outside with
        ⟨leftOutside,rightOutside,parentApart,leftApart,rightApart⟩
      have last := cap_loop_heap_word_frame level parent (cap_range_from_span level parent span)
        (capAfterTests right) out ascend.1 ascend.2.heap ascend.2.context.controls.roots reachedParent
        query queryBound parentApart leftApart rightApart word
      have leftFrame := ih (by omega) (2*node) pointer (capLookup state) left leftPos children.1 leftPC leftEnd
        (by omega) reachedLeft query queryBound leftOutside word
      have rightFrame := ih (by omega) (2*node+1) _ (capRight (capAfterTests left)) right sibling.2.1 children.2
        sibling.1 rightEnd (by omega) reachedRight query queryBound rightOutside word
      exact last.trans ((congrFun (cap_tests_memory right) _).trans (rightFrame.trans
        ((congrFun sibling.2.2 _).trans (leftFrame.trans (congrFun mem _)))))
    · have unmarked : capIsMarked groups node (height+1)=false := by simpa using marked
      exact cap_tree_unmarked_heap_word_frame small position span endReg endBound
        (by simpa [capFrontierNodes,unmarked] using room) unmarked reached query queryBound
        (cap_interval_parent_apart node (height+1) query outside) word

theorem cap_tree_heap_buffer_frame {groups : List Nat} {height finish node pointer : Nat}
    (endBound : finish≤MEMORY_BYTES) (small : height≤8) (state out : MachineState)
    (position : CapPosition groups state node pointer) (span : TwoPermutationPrototype.Opening.CapSpan node height)
    (pc : state.pc=4096+4*2661) (endReg : state.getReg .x22=BitVec.ofNat 64 finish)
    (room : pointer+30*(capFrontierNodes groups node height).length≤finish)
    (reached : out∈support (capTreeTrace groups height small node state))
    (query : Nat) (queryBound : query<512) (outside : query<node ∨ (node+1)*2^height≤query) :
    readBuffer out (16384+32*query) 32=readBuffer state (16384+32*query) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  exact cap_tree_heap_word_frame groups height finish endBound small node pointer state out position span pc endReg room
    reached query queryBound outside ⟨word,inside⟩

@[irreducible] noncomputable def capTreeObservation (oracle : Oracle) (groups : List Nat)
    (height : Nat) (small : height≤8) (node : Nat) (state : MachineState) :=
  checkEvaluation oracle (recordRows (capTreeTrace groups height small node state))

theorem cap_tree_observation_eq (oracle : Oracle) (groups : List Nat)
    (height : Nat) (small : height≤8) (node : Nat) (state : MachineState) :
    capTreeObservation oracle groups height small node state=
      checkEvaluation oracle (recordRows (capTreeTrace groups height small node state)) := by
  rw [capTreeObservation]

theorem cap_tree_observation_support (oracle : Oracle) (groups : List Nat)
    (height : Nat) (small : height≤8) (node : Nat) (state : MachineState) :
    (capTreeObservation oracle groups height small node state).1.1∈support (capTreeTrace groups height small node state) := by
  rw [cap_tree_observation_eq]
  exact recorded_evaluation_support oracle _

theorem cap_tree_observation_leaf (oracle : Oracle) (groups : List Nat) (node : Nat) (state : MachineState)
    (marked : capIsMarked groups node 0=true) :
    capTreeObservation oracle groups 0 (by decide) node state=((capLookup state,[]),0) := by
  rw [cap_tree_observation_eq,capTreeTrace]
  simp only [marked,ite_true,record_rows_pure,check_evaluation_pure]

theorem cap_tree_observation_branch (oracle : Oracle) (groups : List Nat) (height : Nat)
    (small : height+1≤8) (node : Nat) (state : MachineState)
    (marked : capIsMarked groups node (height+1)=true) :
    capTreeObservation oracle groups (height+1) small node state=
      let left := capTreeObservation oracle groups height (by omega) (2*node) (capLookup state)
      let right := capTreeObservation oracle groups height (by omega) (2*node+1) (capRight (capAfterTests left.1.1))
      let parent := capLoopObservation oracle ⟨height,by omega⟩ (capAfterTests right.1.1)
      ((parent.1.1,left.1.2++(right.1.2++parent.1.2)),left.2+(right.2+parent.2)) := by
  rw [cap_tree_observation_eq,capTreeTrace]
  simp only [marked,ite_true]
  rw [recorded_bind_evaluation,←cap_tree_observation_eq oracle groups height (by omega) (2*node) (capLookup state)]
  dsimp only
  rw [recorded_bind_evaluation,
    ←cap_tree_observation_eq oracle groups height (by omega) (2*node+1)
      (capRight (capAfterTests (capTreeObservation oracle groups height (by omega) (2*node) (capLookup state)).1.1))]
  dsimp only
  rw [←cap_loop_observation_eq]

@[irreducible] def capHeapNode (state : MachineState) (node : Nat) : Node :=
  (readBuffer state (16384+32*node) 32).setWidth 238

theorem cap_heap_node_memory (before after : MachineState) (memory : before.mem=after.mem) (node : Nat) :
    capHeapNode before node=capHeapNode after node := by
  rw [capHeapNode,capHeapNode,read_buffer_memory_congr before after memory]

theorem cap_heap_node_buffer (before after : MachineState) (node : Nat)
    (buffer : readBuffer before (16384+32*node) 32=readBuffer after (16384+32*node) 32) :
    capHeapNode before node=capHeapNode after node := by rw [capHeapNode,capHeapNode,buffer]

theorem cap_leaf_bounds (group node height : Nat) (span : TwoPermutationPrototype.Opening.CapSpan node height)
    (atNode : group/2^height=node) :
    256≤group ∧ group<512 ∧ node*2^height≤group ∧ group<(node+1)*2^height := by
  have small := span.heightBound
  have low := span.start
  have high := span.finish
  interval_cases height <;> norm_num at atNode low high ⊢ <;> omega

theorem cap_loop_left_heap_path (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    RecordedPath canonicalEncoding calls width (capLoopObservation oracle height state).1.2
      (2*node.val) (16+height.val) 1 (capHeapNode state (2*node.val))
      (capHeapNode (capLoopObservation oracle height state).1.1 node.val) := by
  simpa only [capHeapNode,show 16384+32*(2*node.val)=16384+64*node.val by omega]
    using cap_loop_left_recorded_path oracle height node range state pc child heap

theorem cap_loop_right_heap_path (oracle : Oracle) (height : Fin 8) (node : Fin 256)
    (range : CapNodeRange height node) (state : MachineState) (pc : state.pc=4096+4*2708)
    (child : state.getReg .x6=BitVec.ofNat 64 (2*node.val+1)) (heap : state.getReg .x25=16384) :
    RecordedPath canonicalEncoding calls width (capLoopObservation oracle height state).1.2
      (2*node.val+1) (16+height.val) 1 (capHeapNode state (2*node.val+1))
      (capHeapNode (capLoopObservation oracle height state).1.1 node.val) := by
  simpa only [capHeapNode,show 16384+32*(2*node.val+1)=16384+64*node.val+32 by omega]
    using cap_loop_right_recorded_path oracle height node range state pc child heap

theorem cap_tree_recorded_path (oracle : Oracle) (groups : List Nat) (height finish : Nat)
    (endBound : finish≤MEMORY_BYTES) :
    ∀ (small : height≤8) (node pointer : Nat) (state : MachineState),
    CapPosition groups state node pointer → TwoPermutationPrototype.Opening.CapSpan node height →
    state.pc=4096+4*2661 → state.getReg .x22=BitVec.ofNat 64 finish →
    pointer+30*(capFrontierNodes groups node height).length≤finish →
    ∀ group, group∈groups → group/2^height=node →
    RecordedPath canonicalEncoding calls width (capTreeObservation oracle groups height small node state).1.2
      group 16 height (capHeapNode state group)
      (capHeapNode (capTreeObservation oracle groups height small node state).1.1 node) := by
  induction height with
  | zero =>
    intro small node pointer state position span pc endReg room group member atNode
    have marked : capIsMarked groups node 0=true := by
      simp only [capIsMarked,List.any_eq_true,beq_iff_eq]
      exact ⟨group,member,atNode⟩
    have index : group=node := by simpa using atNode
    rw [cap_tree_observation_leaf oracle groups node state marked]
    change RecordedPath canonicalEncoding calls width [] group 16 0 (capHeapNode state group)
      (capHeapNode (capLookup state) node)
    rw [index,cap_heap_node_memory _ _ (cap_lookup_position position span).2.2]
    exact RecordedPath.done _ _ _
  | succ height ih =>
    intro small node pointer state position span pc endReg room group member atNode
    have marked : capIsMarked groups node (height+1)=true := by
      simp only [capIsMarked,List.any_eq_true,beq_iff_eq]
      exact ⟨group,member,atNode⟩
    have children := TwoPermutationPrototype.Opening.cap_span_children node height span
    have fields : (capFrontierNodes groups node (height+1)).length=
        (capFrontierNodes groups (2*node) height).length+(capFrontierNodes groups (2*node+1) height).length := by
      simp [capFrontierNodes,marked]
    rw [fields] at room
    have bound : 0<node ∧ 2*node<512 := by
      have := (TwoPermutationPrototype.Opening.cap_span_node node (height+1) span).1
      have := TwoPermutationPrototype.Opening.cap_span_is_internal node height span
      omega
    obtain ⟨target,next,mem⟩ := cap_lookup_position position span
    have leftPC : (capLookup state).pc=4096+4*2661 := by simpa [marked] using target
    have leftPos : CapPosition groups (capLookup state) (2*node) pointer := by simpa [marked] using next
    have leftEnd : (capLookup state).getReg .x22=BitVec.ofNat 64 finish :=
      ((cap_lookup_stable state) .x22 (by decide)).trans endReg
    let left := capTreeObservation oracle groups height (by omega) (2*node) (capLookup state)
    have reachedLeft := cap_tree_observation_support oracle groups height (by omega) (2*node) (capLookup state)
    have leftOk := cap_tree_correct groups height finish endBound (by omega) (2*node) pointer
      (capLookup state) leftPos children.1 leftPC leftEnd (by omega)
    have postLeft := leftOk.post left.1.1 reachedLeft
    have sibling := cap_sibling_position postLeft.2.1 postLeft.1 bound
    have stable := ((cap_lookup_stable state).trans postLeft.2.2.1).trans
      ((cap_tests_stable left.1.1).trans (cap_right_stable (capAfterTests left.1.1)))
    have rightEnd := (stable .x22 (by decide)).trans endReg
    let right := capTreeObservation oracle groups height (by omega) (2*node+1) (capRight (capAfterTests left.1.1))
    have reachedRight := cap_tree_observation_support oracle groups height (by omega) (2*node+1)
      (capRight (capAfterTests left.1.1))
    have rightOk := cap_tree_correct groups height finish endBound (by omega) (2*node+1)
      (pointer+30*(capFrontierNodes groups (2*node) height).length) (capRight (capAfterTests left.1.1))
      sibling.2.1 children.2 sibling.1 rightEnd (by omega)
    have postRight := rightOk.post right.1.1 reachedRight
    let parent : Fin 256 := ⟨node,TwoPermutationPrototype.Opening.cap_span_is_internal node height span⟩
    let level : Fin 8 := ⟨height,by omega⟩
    have ascend := cap_ascend_ready level parent span right.1.1 postRight.2.1 postRight.1
    let last := capLoopObservation oracle level (capAfterTests right.1.1)
    have whole := cap_tree_observation_branch oracle groups height small node state marked
    change capTreeObservation oracle groups (height+1) small node state=
      ((last.1.1,left.1.2++(right.1.2++last.1.2)),left.2+(right.2+last.2)) at whole
    rw [whole]
    change RecordedPath canonicalEncoding calls width (left.1.2++(right.1.2++last.1.2)) group 16 (height+1)
      (capHeapNode state group) (capHeapNode last.1.1 node)
    have half : (group/2^height)/2=node := by rw [Nat.div_div_eq_div_mul,←Nat.pow_succ]; exact atNode
    have sides : group/2^height=2*node ∨ group/2^height=2*node+1 := by omega
    have includeParent : ∀ row∈last.1.2, row∈left.1.2++(right.1.2++last.1.2) := by
      intro row found
      exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr found)))
    rcases sides with onLeft | onRight
    · have partialPath := ih (by omega) (2*node) pointer (capLookup state) leftPos children.1 leftPC leftEnd
        (by omega) group member onLeft
      have middleFrame := cap_tree_heap_buffer_frame endBound (by omega) _ right.1.1 sibling.2.1 children.2
        sibling.1 rightEnd (by omega) reachedRight (2*node) (by omega) (.inl (by omega))
      have middle : capHeapNode (capAfterTests right.1.1) (2*node)=capHeapNode left.1.1 (2*node) :=
        (cap_heap_node_memory _ _ (cap_tests_memory right.1.1) _).trans
          ((cap_heap_node_buffer _ _ _ middleFrame).trans (cap_heap_node_memory _ _ sibling.2.2 _))
      rw [cap_heap_node_memory _ _ mem group,←middle] at partialPath
      have included : ∀ row∈left.1.2, row∈left.1.2++(right.1.2++last.1.2) := by
        intro row found
        exact List.mem_append.mpr (.inl found)
      apply recorded_path_append (partialPath.mono included)
      rw [onLeft]
      exact (cap_loop_left_heap_path oracle level parent (cap_range_from_span level parent span)
        _ ascend.1 ascend.2.heap ascend.2.context.controls.roots).mono includeParent
    · have partialPath := ih (by omega) (2*node+1) _ (capRight (capAfterTests left.1.1)) sibling.2.1 children.2
        sibling.1 rightEnd (by omega) group member onRight
      have leafBounds := cap_leaf_bounds group (2*node+1) height children.2 onRight
      have startFrame := cap_tree_heap_buffer_frame endBound (by omega) _ left.1.1 leftPos children.1 leftPC leftEnd
        (by omega) reachedLeft group leafBounds.2.1 (.inr leafBounds.2.2.1)
      have start : capHeapNode (capRight (capAfterTests left.1.1)) group=capHeapNode state group :=
        (cap_heap_node_memory _ _ sibling.2.2 _).trans
          ((cap_heap_node_buffer _ _ _ startFrame).trans (cap_heap_node_memory _ _ mem _))
      have middle := cap_heap_node_memory _ _ (cap_tests_memory right.1.1) (2*node+1)
      rw [start,←middle] at partialPath
      have included : ∀ row∈right.1.2, row∈left.1.2++(right.1.2++last.1.2) := by
        intro row found
        exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl found)))
      apply recorded_path_append (partialPath.mono included)
      rw [onRight]
      exact (cap_loop_right_heap_path oracle level parent (cap_range_from_span level parent span)
        _ ascend.1 ascend.2.heap ascend.2.context.controls.roots).mono includeParent

theorem cap_eight_recorded_path (oracle : Oracle) (groups : List Nat) (finish pointer : Nat)
    (endBound : finish≤MEMORY_BYTES) (state : MachineState) (position : CapPosition groups state 1 pointer)
    (pc : state.pc=4096+4*2661) (endReg : state.getReg .x22=BitVec.ofNat 64 finish)
    (room : pointer+30*(capFrontierNodes groups 1 8).length≤finish) (group : Nat)
    (member : group∈groups) (bounds : 256≤group ∧ group<512) :
    RecordedPath canonicalEncoding calls width (capTreeObservation oracle groups 8 (by decide) 1 state).1.2
      group 16 8 (capHeapNode state group)
      (capHeapNode (capTreeObservation oracle groups 8 (by decide) 1 state).1.1 1) :=
  cap_tree_recorded_path oracle groups 8 finish endBound (by decide) 1 pointer state position
    TwoPermutationPrototype.Opening.cap_span_root pc endReg room group member (by norm_num;omega)

theorem lower_cap_recorded_path (oracle : Oracle) (groups : List Nat) (finish pointer : Nat)
    (endBound : finish≤MEMORY_BYTES) (state : MachineState) (position : CapPosition groups state 1 pointer)
    (pc : state.pc=4096+4*2661) (endReg : state.getReg .x22=BitVec.ofNat 64 finish)
    (room : pointer+30*(capFrontierNodes groups 1 8).length≤finish)
    (rows : List PublicRow) (node : Nat) (start : Node)
    (member : node/2^16∈groups) (bounds : 256≤node/2^16 ∧ node/2^16<512)
    (lower : RecordedPath canonicalEncoding calls width rows node 0 16 start (capHeapNode state (node/2^16))) :
    RecordedPath canonicalEncoding calls width
      (rows++(capTreeObservation oracle groups 8 (by decide) 1 state).1.2) node 0 24 start
      (capHeapNode (capTreeObservation oracle groups 8 (by decide) 1 state).1.1 1) := by
  have cap := cap_eight_recorded_path oracle groups finish pointer endBound state position pc endReg room
    (node/2^16) member bounds
  have before : ∀ row∈rows, row∈rows++(capTreeObservation oracle groups 8 (by decide) 1 state).1.2 := by
    intro row found
    exact List.mem_append.mpr (.inl found)
  have after : ∀ row∈(capTreeObservation oracle groups 8 (by decide) 1 state).1.2,
      row∈rows++(capTreeObservation oracle groups 8 (by decide) 1 state).1.2 := by
    intro row found
    exact List.mem_append.mpr (.inr found)
  exact recorded_path_append (lower.mono before) (cap.mono after)

@[irreducible] noncomputable def capDfsObservation (oracle : Oracle) (groups : List Nat) (state : MachineState) :=
  checkEvaluation oracle (recordRows (capDfsEntryTrace groups state))

theorem cap_dfs_observation_map (oracle : Oracle) (groups : List Nat) (state : MachineState) :
    capDfsObservation oracle groups state=
      ((capRootTest (capTreeObservation oracle groups 8 (by decide) 1 (capStart state)).1.1,
        (capTreeObservation oracle groups 8 (by decide) 1 (capStart state)).1.2),
        (capTreeObservation oracle groups 8 (by decide) 1 (capStart state)).2) := by
  have mapped := record_map_evaluation oracle capRootTest (capTreeTrace groups 8 (by decide) 1 (capStart state))
  rw [←cap_tree_observation_eq] at mapped
  rw [capDfsObservation]
  simpa only [capDfsEntryTrace,map_eq_bind_pure_comp,Function.comp_def] using mapped

theorem cap_dfs_eight_recorded_path (oracle : Oracle) {groups : List Nat} {state : MachineState}
    {pointer finish : Nat} (ready : CapDfsEntryReady groups state pointer finish)
    (group : Nat) (member : group∈groups) (bounds : 256≤group ∧ group<512) :
    RecordedPath canonicalEncoding calls width (capDfsObservation oracle groups state).1.2 group 16 8
      (capHeapNode state group) (capHeapNode (capDfsObservation oracle groups state).1.1 1) := by
  have start := cap_start_position ready
  have endReg := (cap_start_register state .x22 (by decide) (by decide) (by decide)).trans ready.endReg
  have path := cap_eight_recorded_path oracle groups finish pointer ready.endBound (capStart state)
    start.2.1 start.1 endReg ready.room group member bounds
  have correct := cap_tree_correct groups 8 finish ready.endBound (by decide) 1 pointer (capStart state)
    start.2.1 TwoPermutationPrototype.Opening.cap_span_root start.1 endReg ready.room
  have post := correct.post _ (cap_tree_observation_support oracle groups 8 (by decide) 1 (capStart state))
  have root := cap_root_position post.2.1 post.1
  rw [cap_heap_node_memory _ _ start.2.2 group] at path
  rw [cap_dfs_observation_map]
  change RecordedPath canonicalEncoding calls width
    (capTreeObservation oracle groups 8 (by decide) 1 (capStart state)).1.2 group 16 8
    (capHeapNode state group)
    (capHeapNode (capRootTest (capTreeObservation oracle groups 8 (by decide) 1 (capStart state)).1.1) 1)
  rw [cap_heap_node_memory _ _ root.2.2.2 1]
  exact path

attribute [local irreducible] markMachine capMarkedState

theorem cap_marked_memory_word (state : MachineState) (base : state.getReg .x26=4096#64)
    (word : Nat) (bounded : word<2^61) (outside : 768≤word) :
    memoryView (capMarkedState state) word=memoryView state word := by
  have pc : (startMark state).pc=4096+4*2648 := rfl
  have count : (startMark state).getReg .x6=BitVec.ofNat 64 255 := by
    simp [startMark,TwoPermutationPrototype.Opening.getReg_setReg]
  have markBase : (startMark state).getReg .x26=BitVec.ofNat 64 TwoPermutationPrototype.Opening.markBase := by
    simpa [startMark,TwoPermutationPrototype.Opening.markBase,TwoPermutationPrototype.Opening.getReg_setReg] using base
  have frame := mark_sweep_word (startMark state) 255 (by decide) pc markBase count word bounded (.inr outside)
  rw [capMarkedState]
  exact frame.trans rfl

theorem cap_marked_heap_buffer (state : MachineState) (base : state.getReg .x26=4096#64)
    (node : Nat) (bounded : node<512) :
    readBuffer (capMarkedState state) (16384+32*node) 32=readBuffer state (16384+32*node) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  have frame := cap_marked_memory_word state base (2048+4*node+word) (by omega) (by omega)
  have address : wordAddress (2048+4*node+word)=BitVec.ofNat 64 (16384+32*node+8*word) := by
    unfold wordAddress
    congr 1
    omega
  change (capMarkedState state).getMem (wordAddress (2048+4*node+word))=
    state.getMem (wordAddress (2048+4*node+word)) at frame
  simpa only [address] using frame

theorem cap_marked_eight_recorded_path (oracle : Oracle) {groups : List Nat} {state : MachineState}
    {pointer finish : Nat} (ready : CapMarkReady groups state pointer finish)
    (group : Nat) (member : group∈groups) (bounds : 256≤group ∧ group<512) :
    RecordedPath canonicalEncoding calls width (capDfsObservation oracle groups (capMarkedState state)).1.2 group 16 8
      (capHeapNode state group) (capHeapNode (capDfsObservation oracle groups (capMarkedState state)).1.1 1) := by
  have path := cap_dfs_eight_recorded_path oracle (cap_mark_ready ready) group member bounds
  rw [cap_heap_node_buffer _ _ group (cap_marked_heap_buffer state ready.markBase group bounds.2)] at path
  exact path

end CommitGolfCandidate.Chained.Native.Refinement
