import CommitGolfCandidate.CapCheckRecordsCollected
import CommitGolfCandidate.CapBatchBudget

/-! Successful actual records add at most one occupied cap group, for every
supported oracle reply sequence. This history-sensitive bound is separate from
the fixed-oracle parser agreement and supplies the checker query budget. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_insert_known_count (roots next : CapRootMap) (key : Nat)
    (value : Digest) (inserted : capInsert roots key value = some next) :
    capMarkedCount (capKnownView next 7 0) ≤
      capMarkedCount (capKnownView roots 7 0) + 1 := by
  classical
  rw [cap_known_view_card, cap_known_view_card]
  have subset :
      (Finset.range 128).filter (fun group => (next group).isSome = true) ⊆
        insert key ((Finset.range 128).filter (fun group => (roots group).isSome = true)) := by
    intro group member
    obtain ⟨inside, occupied⟩ := Finset.mem_filter.mp member
    rcases (cap_insert_domain roots next key group value inserted).mp occupied with same | old
    · exact Finset.mem_insert.mpr (Or.inl same)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨inside, old⟩))
  exact (Finset.card_le_card subset).trans (Finset.card_insert_le _ _)

theorem cap_check_record_supported_count (input : CheckInput)
    (ordinal remaining : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal (remaining+1) state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (result : MachineState × Bool) (reachable : result ∈ support (capCheckRecordRun state))
    (passed : result.2 = true) :
    ∃ next : CapRootMap, CapCheckCollected result.1 next ∧
      capMarkedCount (capKnownView next 7 0) ≤
        capMarkedCount (capKnownView roots 7 0) + 1 := by
  obtain ⟨index, bounded, loaded⟩ :=
    cap_check_records_ready_index input ordinal (remaining+1) state ready (by omega)
  obtain ⟨lower, lowerReachable, equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  have groupReady := cap_check_lower_group_ready state lower index bounded loaded
    ready.scratch ready.leaves ready.marks ready.roots ready.one lowerReachable
  have lowerCollected := cap_check_lower_record_collected state lower ready.scratch
    lowerReachable roots collected
  have groupPassed : (capCheckGroupResult lower).2 = true := by
    rw [← cap_check_record_result_passed]
    exact passed
  have inserted := (cap_check_group_insert lower roots lowerCollected (index/2^17)
    groupReady.bounded groupReady.index groupReady.leaves groupReady.marks
    groupReady.roots groupReady.scratch groupReady.one).mp groupPassed
  cases insertion : capInsert roots (index/2^17) (readBuffer lower 256 32) with
  | none =>
    rw [insertion] at inserted
    contradiction
  | some next =>
    exact ⟨next, cap_check_record_result_collected lower roots next (index/2^17)
      groupReady lowerCollected insertion, cap_insert_known_count roots next
      (index/2^17) (readBuffer lower 256 32) insertion⟩

theorem cap_check_records_supported_count (input : CheckInput) (ordinal count : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal count state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (result : MachineState × Bool) (reachable : result ∈ support (capCheckRecordsRun count state))
    (passed : result.2 = true) :
    ∃ finalRoots : CapRootMap, CapCheckCollected result.1 finalRoots ∧
      capMarkedCount (capKnownView finalRoots 7 0) ≤
        capMarkedCount (capKnownView roots 7 0) + count := by
  induction count generalizing ordinal state roots with
  | zero =>
    simp only [capCheckRecordsRun, support_pure, Set.mem_singleton_iff] at reachable
    subst result
    exact ⟨roots, collected, by omega⟩
  | succ count ih =>
    simp only [capCheckRecordsRun, mem_support_bind_iff] at reachable
    obtain ⟨head, headReachable, tailReachable⟩ := reachable
    cases headPassed : head.2
    · simp only [headPassed, Bool.false_eq_true, ↓reduceIte, support_pure,
        Set.mem_singleton_iff] at tailReachable
      subst result
      rw [headPassed] at passed
      contradiction
    · simp only [headPassed, ↓reduceIte] at tailReachable
      obtain ⟨next, nextCollected, headCount⟩ := cap_check_record_supported_count input
        ordinal count state ready roots collected head headReachable headPassed
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        head headReachable headPassed
      obtain ⟨finalRoots, finalCollected, tailCount⟩ :=
        ih (ordinal+1) head.1 nextReady next nextCollected tailReachable
      exact ⟨finalRoots, finalCollected, by omega⟩

theorem cap_check_records_empty_count (input : CheckInput) (count : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input 0 count state)
    (collected : CapCheckCollected state (fun _ => none))
    (result : MachineState × Bool) (reachable : result ∈ support (capCheckRecordsRun count state))
    (passed : result.2 = true) :
    ∃ roots : CapRootMap, CapCheckCollected result.1 roots ∧
      capMarkedCount (capKnownView roots 7 0) ≤ count := by
  obtain ⟨roots, finalCollected, bounded⟩ := cap_check_records_supported_count input 0
    count state ready (fun _ => none) collected result reachable passed
  have empty : capMarkedCount (capKnownView (fun _ => none) 7 0) = 0 := by
    rw [cap_known_view_card]
    simp
  exact ⟨roots, finalCollected, by simpa only [empty, Nat.zero_add] using bounded⟩

end CommitGolfCandidate
