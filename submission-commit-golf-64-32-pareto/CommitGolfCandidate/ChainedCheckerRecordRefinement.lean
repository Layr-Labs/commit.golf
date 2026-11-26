import CommitGolfCandidate.ChainedCheckerCapPaths

/-! Typed per-record observations and their stored lower-path witnesses. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open RecordLeaf RecordTail SplitCodec
set_option maxRecDepth 8192

@[irreducible] noncomputable def recordLeafObservation (oracle : Oracle) (input : CheckInput)
    (record source : Nat) (state : MachineState) :=
  checkEvaluation oracle (recordRows (leafQueries (checkerRecordCoreNonceState state) source
    (checkerRecordInputIndex input record)))

theorem record_leaf_observation_eq (oracle : Oracle) (input : CheckInput) (record source : Nat) (state : MachineState) :
    recordLeafObservation oracle input record source state=
      checkEvaluation oracle (recordRows (leafQueries (checkerRecordCoreNonceState state) source
        (checkerRecordInputIndex input record))) := by rw [recordLeafObservation]

@[irreducible] noncomputable def recordPathState (oracle : Oracle) (input : CheckInput)
    (record source : Nat) (state : MachineState) : MachineState :=
  checkerLeafPathState (recordLeafObservation oracle input record source state).1.1

theorem record_path_state_eq (oracle : Oracle) (input : CheckInput) (record source : Nat) (state : MachineState) :
    recordPathState oracle input record source state=
      checkerLeafPathState (recordLeafObservation oracle input record source state).1.1 := by rw [recordPathState]

theorem record_path_ready (oracle : Oracle) {input : CheckInput} {record source : Nat}
    {base : CheckerRecordBase} {state : MachineState} (ready : CheckerRecordCoreReady input record base source state) :
    CheckerFirstPathReady input (recordPathState oracle input record source state) base record := by
  rw [record_path_state_eq,record_leaf_observation_eq]
  have reached := recorded_evaluation_support oracle
    (leafQueries (checkerRecordCoreNonceState state) source (checkerRecordInputIndex input record))
  generalize equality : checkEvaluation oracle
    (recordRows (leafQueries (checkerRecordCoreNonceState state) source (checkerRecordInputIndex input record)))=observed at *
  rcases observed with ⟨⟨after,rows⟩,calls⟩
  simp only [leafQueries,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨a,_,b,_,rfl⟩ := reached
  exact checker_record_core_path_ready ready a b

theorem record_path_node (oracle : Oracle) {input : CheckInput} {record source : Nat}
    {base : CheckerRecordBase} {state : MachineState} (ready : CheckerRecordCoreReady input record base source state) :
    ((recordPathState oracle input record source state).getReg .x6).toNat=
      LENGTH+(checkerRecordInputIndex input record).val := by
  have stored := (record_path_ready oracle ready).node
  change (recordPathState oracle input record source state).getReg .x6=
    BitVec.ofNat 64 (LENGTH+(checkerRecordInputIndex input record).val) at stored
  rw [stored,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have small := (checkerRecordInputIndex input record).isLt
  unfold LENGTH LOG_LENGTH at *
  omega

@[irreducible] noncomputable def recordLowerObservation (oracle : Oracle) (input : CheckInput)
    (record source : Nat) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerRecordLowerTrace input record source state))

theorem record_lower_observation_eq (oracle : Oracle) (input : CheckInput) (record source : Nat) (state : MachineState) :
    recordLowerObservation oracle input record source state=
      checkEvaluation oracle (recordRows (checkerRecordLowerTrace input record source state)) := by rw [recordLowerObservation]

theorem record_lower_observation_bind (oracle : Oracle) (input : CheckInput) (record source : Nat) (state : MachineState) :
    recordLowerObservation oracle input record source state=
      let first := recordLeafObservation oracle input record source state
      let later := lowerSixteenObservation oracle (recordPathState oracle input record source state)
      ((later.1.1,first.1.2++later.1.2),first.2+later.2) := by
  rw [record_lower_observation_eq,checkerRecordLowerTrace,recorded_bind_evaluation,←record_leaf_observation_eq]
  dsimp only
  rw [←record_path_state_eq,←lower_sixteen_observation_eq]

theorem recorded_observation_suffix {α : Type} {enc : Encoding} {schedule widths : Height → Nat}
    (digest : α → Node) (first later whole : (α × List PublicRow) × Nat)
    (node level count : Nat) (start : Node)
    (mapped : whole=((later.1.1,first.1.2++later.1.2),first.2+later.2))
    (tail : RecordedPath enc schedule widths later.1.2 node level count start (digest later.1.1)) :
    RecordedPath enc schedule widths whole.1.2 node level count start (digest whole.1.1) := by
  rw [mapped]
  exact tail.mono (fun _ found => List.mem_append.mpr (.inr found))

theorem record_lower_observation_path (oracle : Oracle) {input : CheckInput} {record source : Nat}
    {base : CheckerRecordBase} {state : MachineState} (ready : CheckerRecordCoreReady input record base source state) :
    RecordedPath canonicalEncoding calls width (recordLowerObservation oracle input record source state).1.2
      (LENGTH+(checkerRecordInputIndex input record).val) 0 16
      ((readBuffer (recordPathState oracle input record source state) 12288 32).setWidth 238)
      ((readBuffer (recordLowerObservation oracle input record source state).1.1 12288 32).setWidth 238) := by
  have path := lower_sixteen_observation_path oracle input _ (record_path_ready oracle ready)
  rw [record_path_node oracle ready] at path
  exact recorded_observation_suffix (fun s : MachineState => (readBuffer s 12288 32).setWidth 238)
    (recordLeafObservation oracle input record source state)
    (lowerSixteenObservation oracle (recordPathState oracle input record source state))
    (recordLowerObservation oracle input record source state) _ 0 16 _
    (record_lower_observation_bind oracle input record source state) path

theorem masked_leaf_node (value : Output) :
    (BitVec.ofNat 256 (value.toNat%2^238)).setWidth 238=nodeDigest 238 value := by
  exact final_value_node (CheckerCap.capHeight ⟨0,by decide⟩) value

theorem record_path_typed_node (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    let message := entryWords (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega)))
    let nonce := saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record))
    (readBuffer (recordPathState oracle input record (754975239+32*record) state) 12288 32).setWidth 238=
      nodeDigest 238 (pinnedLeafDigest oracle.permutation (checkerRecordInputIndex input record) nonce message) := by
  dsimp only
  rw [record_path_state_eq,record_leaf_observation_eq,checker_record_typed_leaf_path_digest oracle decoded boundary active]
  exact masked_leaf_node _

theorem record_lower_typed_path (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    let message := entryWords (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega)))
    let nonce := saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record))
    RecordedPath canonicalEncoding calls width (recordLowerObservation oracle input record (754975239+32*record) state).1.2
      (LENGTH+(checkerRecordInputIndex input record).val) 0 16
      (nodeDigest 238 (pinnedLeafDigest oracle.permutation (checkerRecordInputIndex input record) nonce message))
      ((readBuffer (recordLowerObservation oracle input record (754975239+32*record) state).1.1 12288 32).setWidth 238) := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  have path := record_lower_observation_path oracle core
  rw [record_path_typed_node oracle decoded boundary active] at path
  exact path

theorem group_run_heap_node {state : MachineState} {node remaining : Nat}
    (ready : GroupReady node remaining state) (accepted : TwoPermutationPrototype.Checker.GroupAccepted state node) :
    capHeapNode (groupRun state node).1 node=(readBuffer state 12288 32).setWidth 238 := by
  have frame := (group_run_state state node remaining ready).memory
  have root := TwoPermutationPrototype.Checker.group_memory_root state node ready.high accepted
  rw [show 8*(2048+4*node)=16384+32*node by omega] at root
  calc
    capHeapNode (groupRun state node).1 node=capHeapNode (TwoPermutationPrototype.Checker.groupMemory state node) node :=
      cap_heap_node_memory (groupRun state node).1 (TwoPermutationPrototype.Checker.groupMemory state node) frame node
    _=(readBuffer state 12288 32).setWidth 238 := by rw [capHeapNode,root]

structure RecordedLowerOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Node)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation (pinnedFirstRow oracle.permutation (entryWords entry)).1
    (pinnedFirstRow oracle.permutation (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pinnedSecondRow oracle.permutation index nonce (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).1
    (pinnedSecondRow oracle.permutation index nonce (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2 ∈ rows
  path : RecordedPath canonicalEncoding calls width rows (LENGTH+index.val) 0 16
    (nodeDigest 238 (pinnedLeafDigest oracle.permutation index nonce (entryWords entry))) root

def RecordedLowerOpening.mono {oracle index entry root earlier later}
    (opening : RecordedLowerOpening oracle index entry root earlier)
    (included : ∀ row∈earlier, row∈later) : RecordedLowerOpening oracle index entry root later :=
  ⟨opening.nonce,included _ opening.first,included _ opening.second,opening.path.mono included⟩

theorem record_lower_has_leaf_rows (oracle : Oracle) (input : CheckInput) (record source : Nat) (state : MachineState)
    (row : PublicRow) (present : row∈(recordLeafObservation oracle input record source state).1.2) :
    row∈(recordLowerObservation oracle input record source state).1.2 := by
  rw [record_lower_observation_bind]
  exact List.mem_append.mpr (.inl present)

noncomputable def record_lower_opening (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    RecordedLowerOpening oracle (checkerRecordInputIndex input record)
      (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega)))
      ((readBuffer (recordLowerObservation oracle input record (754975239+32*record) state).1.1 12288 32).setWidth 238)
      (recordLowerObservation oracle input record (754975239+32*record) state).1.2 := by
  refine ⟨saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record)),?_,?_,
    record_lower_typed_path oracle decoded boundary active⟩
  · apply record_lower_has_leaf_rows
    rw [record_leaf_observation_eq,checker_record_typed_leaf_rows oracle decoded boundary active]
    exact List.mem_cons_self
  · apply record_lower_has_leaf_rows
    rw [record_leaf_observation_eq,checker_record_typed_leaf_rows oracle decoded boundary active]
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem record_lower_heap_node {input : CheckInput} {record source : Nat} {base : CheckerRecordBase}
    {state out : MachineState} (ready : CheckerRecordCoreReady input record base source state)
    (reached : out∈support (checkerRecordLowerTrace input record source state)) (sourceBound : 4096 ≤ source)
    (node : Nat) (bounded : node<512) : capHeapNode out node=capHeapNode state node := by
  apply cap_heap_node_buffer
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  have frame := checker_record_lower_memory ready reached (2048+4*node+word) (by omega) (by omega) (.inl (by omega))
  have address : wordAddress (2048+4*node+word)=BitVec.ofNat 64 (16384+32*node+8*word) := by
    unfold wordAddress
    congr 1
    omega
  change out.getMem (wordAddress (2048+4*node+word))=state.getMem (wordAddress (2048+4*node+word)) at frame
  simpa only [address] using frame

theorem group_memory_other_heap (state : MachineState) (node query : Nat) (bounded : node<512)
    (queryBound : query<512) (apart : query≠node) :
    capHeapNode (TwoPermutationPrototype.Checker.groupMemory state node) query=capHeapNode state query := by
  apply cap_heap_node_buffer
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  have frame := TwoPermutationPrototype.Checker.group_memory_other state node (2048+4*query+word)
    bounded (by omega) (by omega) (by omega)
  have address : wordAddress (2048+4*query+word)=BitVec.ofNat 64 (16384+32*query+8*word) := by
    unfold wordAddress
    congr 1
    omega
  simpa only [address] using frame

theorem record_group_prior_heap {input : CheckInput} {reference state out : MachineState} {record remaining : Nat}
    (boundary : CheckerRecordBoundary input reference record (remaining+1) state)
    (reached : out∈support (checkerRecordLowerTrace input record (754975239+32*record) state))
    (query : Nat) (bounds : 256≤query ∧ query<512) (prior : query∈checkerProcessedGroups input record) :
    capHeapNode (groupRun out (checkerRecordGroup input record)).1 query=capHeapNode state query := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
  have cardinal : input.positions.card≤16777216 := boundary.limit
  have small : remaining<2^64 := by have := boundary.balance;omega
  have ready := checker_record_group_ready core reached remaining boundary.counter small boundary.roots boundary.marks
  have frame := (group_run_state out _ remaining ready).memory
  have lower := record_lower_heap_node core reached (by omega) query bounds.2
  apply (cap_heap_node_memory _ _ frame query).trans
  by_cases same : query=checkerRecordGroup input record
  · have occupied : out.getMem (wordAddress (512+checkerRecordGroup input record))=1 := by
      change memoryView out (512+checkerRecordGroup input record)=1
      rw [←same,checker_record_lower_mark_memory core reached _ (by omega) (by omega),boundary.marked query bounds.1 bounds.2,
        ite_eq_left prior]
    have unchanged : TwoPermutationPrototype.Checker.groupMemory out (checkerRecordGroup input record)=out := by
      rw [TwoPermutationPrototype.Checker.groupMemory,ite_eq_right (by rw [occupied];decide)]
    rw [unchanged]
    exact lower
  · exact (group_memory_other_heap out _ query (checker_record_group_bounds input record).2 bounds.2 same).trans lower

end CommitGolfCandidate.Chained.Native.Refinement
