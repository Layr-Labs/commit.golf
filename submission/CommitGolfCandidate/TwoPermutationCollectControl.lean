import CommitGolfCandidate.TwoPermutationCollectTable
import CommitGolfCandidate.TwoPermutationGroupRun

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem group_after_record_ready (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state) :
    let index := (honestIndex input.positions ordinal present).val
    GroupReady (capGroup index) (input.positions.card-(ordinal+1))
      (recordLower oracle state (checkSourceWord ordinal) index).state := by
  let index := (honestIndex input.positions ordinal present).val
  have pre := record_cursor_ready input ordinal state cursor loaded present
  obtain ⟨pc, node, _⟩ := record_lower_geometry oracle pre
  have saved := (record_lower_frame oracle pre).1
  obtain ⟨lo, hi⟩ := checker_cap_group index
  have bounded := checker_positions_bound input
  refine ⟨pc, node, lo, hi,
    (saved .x23 (by unfold RecordRegisterPreserved; decide)).trans cursor.digest,
    (saved .x25 (by unfold RecordRegisterPreserved; decide)).trans cursor.capRoots,
    (saved .x26 (by unfold RecordRegisterPreserved; decide)).trans cursor.marks, ?_, by omega⟩
  rw [saved .x18 (by unfold RecordRegisterPreserved; decide), cursor.remaining,
    show input.positions.card-ordinal=input.positions.card-(ordinal+1)+1 by omega]

theorem group_after_record_cursor (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state) :
    let index := (honestIndex input.positions ordinal present).val
    let lower := (recordLower oracle state (checkSourceWord ordinal) index).state
    GroupAccepted lower (capGroup index) →
    RecordCursor input (ordinal+1) (groupRun lower (capGroup index)).1 := by
  let index := (honestIndex input.positions ordinal present).val
  let lower := (recordLower oracle state (checkSourceWord ordinal) index).state
  let next := (groupRun lower (capGroup index)).1
  have ready := record_cursor_ready input ordinal state cursor loaded present
  have phase := group_after_record_ready oracle input ordinal present state cursor loaded
  have frame := group_run_state lower (capGroup index) (input.positions.card-(ordinal+1)) phase
  have savedLower := (record_lower_frame oracle ready).1
  have nonce := (record_lower_geometry oracle ready).2.2
  change GroupAccepted lower (capGroup index) → RecordCursor input (ordinal+1) next
  intro accepted
  obtain ⟨indices, values, remaining⟩ := frame.advanced accepted
  have keep (r : Reg) (a : RecordRegisterPreserved r) (b : GroupSaved r) :
      next.getReg r = state.getReg r := (frame.saved r b).trans (savedLower r a)
  refine ⟨?_, ?_, ?_, ?_, remaining, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame.pc, ite_eq_left accepted]
    simp only [show input.positions.card-(ordinal+1)=0 ↔ ordinal+1=input.positions.card by omega]
  · rw [indices, savedLower .x8 (by unfold RecordRegisterPreserved; decide), cursor.index]
    change wordAddress (checkIndexWord ordinal) + wordAddress 1 = _
    rw [← wordAddress_add]
    congr 1
  · rw [values, savedLower .x19 (by unfold RecordRegisterPreserved; decide), cursor.value]
    change wordAddress (checkSourceWord ordinal) + wordAddress 32 = _
    rw [← wordAddress_add]
    congr 1
  · rw [frame.saved .x21 (by unfold GroupSaved; decide), nonce]
    congr 1
  all_goals first
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.tag
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.commitment
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.challengeLength
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.proofEnd
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.digest
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.pair
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.capRoots
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.marks
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.capCount
    | exact (keep _ (by unfold RecordRegisterPreserved; decide) (by unfold GroupSaved; decide)).trans cursor.selector

theorem execute_record_group (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state)
    (fuel : Nat) :
    let index := (honestIndex input.positions ordinal present).val
    let leaf := recordLeaf oracle state (checkSourceWord ordinal) index
    let lower := recordLower oracle state (checkSourceWord ordinal) index
    let group := groupRun lower.state (capGroup index)
    let tail := checkEvaluation oracle (recordRows (execute checkerImage fuel group.1 false))
    checkEvaluation oracle (recordRows (execute checkerImage (25+lower.steps+group.2+fuel) state false)) =
      ((tail.1.1.charge (39+lower.cycles+group.2) 18, (leaf.2 ++ lower.rows) ++ tail.1.2), 18+tail.2) := by
  let index := (honestIndex input.positions ordinal present).val
  let lower := recordLower oracle state (checkSourceWord ordinal) index
  let group := groupRun lower.state (capGroup index)
  have ready := record_cursor_ready input ordinal state cursor loaded present
  have phase := group_after_record_ready oracle input ordinal present state cursor loaded
  have run := group_run_execute lower.state (capGroup index) (input.positions.card-(ordinal+1)) phase fuel
  dsimp only
  rw [show 25+lower.steps+group.2+fuel=25+lower.steps+(group.2+fuel) by omega,
    execute_check_record oracle ready (group.2+fuel), run]
  simp only [bind_pure_comp, check_recorded_map, Execution.charge, List.append_assoc, Nat.add_assoc, Nat.zero_add]
  rfl

theorem canonical_record_digest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let index := (honestIndex input.positions ordinal present).val
    let lower := recordLower oracle state (checkSourceWord ordinal) index
    readBuffer lower.state 12288 32 = honestHeap oracle message salts (capGroup index) := by
  have framed : RecordInputFrame (honestCheckInput oracle message input.positions salts) ordinal state :=
    canonical ▸ loaded
  obtain ⟨salt, value, siblings⟩ := record_honest_inputs oracle message input.positions salts ordinal present state framed
  exact honest_record_group oracle message salts (record_cursor_ready input ordinal state cursor loaded present)
    salt value siblings

theorem group_accepts_honest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state)
    (rows : List PublicRow) (table : CollectedTable oracle input ordinal state rows)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let index := (honestIndex input.positions ordinal present).val
    let lower := recordLower oracle state (checkSourceWord ordinal) index
    GroupAccepted lower.state (capGroup index) := by
  let index := (honestIndex input.positions ordinal present).val
  let lower := recordLower oracle state (checkSourceWord ordinal) index
  let group := capGroup index
  have bound := (checker_cap_group index).2
  obtain ⟨sameMark, sameRoot⟩ :=
    record_lower_preserves_cap oracle (record_cursor_ready input ordinal state cursor loaded present)
      (by unfold checkSourceWord; omega) group bound
  change GroupAccepted lower.state group
  by_cases member : group ∈ Opening.groupsBefore input.positions ordinal
  · right
    exact sameRoot.trans ((table.honest message salts canonical group member).trans
      (canonical_record_digest oracle input ordinal present state cursor loaded message salts canonical).symm)
  · left
    change memoryView lower.state (512+group) = 0
    rw [← checker_marks_as_word, sameMark, table.marks group bound, ite_eq_right member]

theorem group_collect_transition (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state)
    (rows : List PublicRow) (table : CollectedTable oracle input ordinal state rows) :
    let index := (honestIndex input.positions ordinal present).val
    let leaf := recordLeaf oracle state (checkSourceWord ordinal) index
    let lower := recordLower oracle state (checkSourceWord ordinal) index
    let group := groupRun lower.state (capGroup index)
    GroupAccepted lower.state (capGroup index) →
    RecordCursor input (ordinal+1) group.1 ∧ RecordInputFrame input (ordinal+1) group.1 ∧
      CollectedTable oracle input (ordinal+1) group.1 (rows++(leaf.2++lower.rows)) := by
  let attached := honestIndex input.positions ordinal present
  let index := attached.val
  let leaf := recordLeaf oracle state (checkSourceWord ordinal) index
  let lower := recordLower oracle state (checkSourceWord ordinal) index
  let group := capGroup index
  let next := (groupRun lower.state group).1
  have recordReady := record_cursor_ready input ordinal state cursor loaded present
  have phase := group_after_record_ready oracle input ordinal present state cursor loaded
  have physical := group_run_state lower.state group (input.positions.card-(ordinal+1)) phase
  have bound := (checker_cap_group index).2
  have sourceAbove : 4096 ≤ checkSourceWord ordinal := by unfold checkSourceWord; omega
  have lowerCap := record_lower_preserves_cap oracle recordReady sourceAbove
  have nextWord (word : Nat) : memoryView next word = memoryView (groupMemory lower.state group) word :=
    congrFun physical.memory (wordAddress word)
  have same (word : Nat) (fit : word < 2^61) (mark : word ≠ 512+group)
      (roots : word < 2048+4*group ∨ 2048+4*group+4 ≤ word) :
      memoryView next word = memoryView lower.state word :=
    (nextWord word).trans (group_memory_other lower.state group word bound fit mark roots)
  change GroupAccepted lower.state group → RecordCursor input (ordinal+1) next ∧
    RecordInputFrame input (ordinal+1) next ∧
    CollectedTable oracle input (ordinal+1) next (rows++(leaf.2++lower.rows))
  intro accepted
  refine ⟨group_after_record_cursor oracle input ordinal present state cursor loaded accepted, ?_, ?_⟩
  · apply record_input_frame_step input ordinal state next loaded
    intro word fit used
    have above : 4096 ≤ word := by
      rcases used with h | h | h
      · omega
      · unfold checkIndexWord at h
        omega
      · unfold checkSourceWord at h
        omega
    obtain ⟨source, scratch⟩ := record_input_address_after input ordinal word used
    exact (same word (by omega) (by omega) (Or.inr (by omega))).trans
      ((record_lower_frame oracle recordReady).2 word fit source scratch)
  have targetRoot : capRootAt next group = readBuffer lower.state 12288 32 :=
    (read_buffer_memory_congr _ _ physical.memory _ _).trans (group_memory_root lower.state group bound accepted)
  have oldMark : memoryView lower.state (512+group) =
      if group ∈ Opening.groupsBefore input.positions ordinal then 1 else 0 := by
    rw [← checker_marks_as_word, (lowerCap group bound).1, table.marks group bound]
  apply collected_table_append oracle input ordinal present state next rows (leaf.2++lower.rows) table
  · intro node inside
    by_cases hit : node = group
    · subst node
      have observed : memoryView next (512+group) =
          if memoryView lower.state (512+group) = 0 then 1 else memoryView lower.state (512+group) :=
        (nextWord _).trans (group_memory_mark lower.state group)
      rw [checker_marks_as_word, observed]
      simp only [show capGroup (honestIndex input.positions ordinal present).val = group from rfl, ite_true]
      by_cases seen : group ∈ Opening.groupsBefore input.positions ordinal
      · simp [oldMark, seen]
      · simp [oldMark, seen]
    · rw [ite_eq_right hit, checker_marks_as_word, checker_marks_as_word state]
      exact (same _ (by omega) (by omega) (Or.inl (by omega))).trans
        ((checker_marks_as_word _ _).symm.trans ((lowerCap node inside).1.trans (checker_marks_as_word _ _)))
  · intro node inside outside
    have separate : node ≠ group := outside
    change readBuffer next (8*(2048+4*node)) 32 = capRootAt state node
    refine (aligned_digest_frame lower.state next _ ?_).trans (lowerCap node inside).2
    intro offset small
    apply same _ (by omega) (by omega)
    omega
  · intro seen
    have used : lower.state.getMem (wordAddress (512+group)) ≠ 0 := by
      change memoryView lower.state (512+group) ≠ 0
      rw [oldMark, ite_eq_left seen]
      decide
    have eq : (groupMemory lower.state group).mem = lower.state.mem := by
      unfold groupMemory
      rw [ite_eq_right used]
    exact (read_buffer_memory_congr _ _ (physical.memory.trans eq) _ _).trans (lowerCap group bound).2
  · have decoded := record_input_value input ordinal present state loaded
    have authentic := record_lower_evidence oracle recordReady (input.values attached) decoded
    dsimp only at authentic ⊢
    rw [targetRoot]
    exact authentic
  · intro message salts canonical
    exact targetRoot.trans (canonical_record_digest oracle input ordinal present state cursor loaded message salts canonical)

end TwoPermutationPrototype.Checker
