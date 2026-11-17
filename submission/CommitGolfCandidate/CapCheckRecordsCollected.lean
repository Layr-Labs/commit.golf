import CommitGolfCandidate.CapCheckRecordsRun
import CommitGolfCandidate.CapCheckLowerCollected

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_record_supported_collected (input : CheckInput)
    (ordinal remaining : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal (remaining+1) state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (result : MachineState × Bool) (reachable : result ∈ support (capCheckRecordRun state))
    (passed : result.2=true) :
    ∃ next : CapRootMap, CapCheckCollected result.1 next := by
  obtain ⟨index,bounded,loaded⟩ :=
    cap_check_records_ready_index input ordinal (remaining+1) state ready (by omega)
  obtain ⟨lower,lowerReachable,equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  have groupReady := cap_check_lower_group_ready state lower index bounded loaded
    ready.scratch ready.leaves ready.marks ready.roots ready.one lowerReachable
  have lowerCollected := cap_check_lower_record_collected state lower ready.scratch
    lowerReachable roots collected
  have groupPassed : (capCheckGroupResult lower).2=true := by
    rw [← cap_check_record_result_passed]
    exact passed
  have inserted := (cap_check_group_insert lower roots lowerCollected (index/2^16)
    groupReady.bounded groupReady.index groupReady.leaves groupReady.marks
    groupReady.roots groupReady.scratch groupReady.one).mp groupPassed
  cases insertion : capInsert roots (index/2^16) (readBuffer lower 256 32) with
  | none =>
    rw [insertion] at inserted
    contradiction
  | some next =>
    exact ⟨next,cap_check_record_result_collected lower roots next (index/2^16)
      groupReady lowerCollected insertion⟩

theorem cap_check_records_supported_collected (input : CheckInput) (ordinal count : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal count state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (result : MachineState × Bool) (reachable : result ∈ support (capCheckRecordsRun count state))
    (passed : result.2=true) :
    ∃ finalRoots : CapRootMap, CapCheckCollected result.1 finalRoots := by
  induction count generalizing ordinal state roots with
  | zero =>
    simp only [capCheckRecordsRun,support_pure,Set.mem_singleton_iff] at reachable
    subst result
    exact ⟨roots,collected⟩
  | succ count ih =>
    simp only [capCheckRecordsRun,mem_support_bind_iff] at reachable
    obtain ⟨head,headReachable,tailReachable⟩ := reachable
    cases headPassed : head.2
    · simp only [headPassed,Bool.false_eq_true,↓reduceIte,support_pure,
        Set.mem_singleton_iff] at tailReachable
      subst result
      rw [headPassed] at passed
      contradiction
    · simp only [headPassed,↓reduceIte] at tailReachable
      obtain ⟨next,nextCollected⟩ := cap_check_record_supported_collected input
        ordinal count state ready roots collected head headReachable headPassed
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        head headReachable headPassed
      exact ih (ordinal+1) head.1 nextReady next nextCollected tailReachable

end CommitGolfCandidate
