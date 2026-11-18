import CommitGolfCandidate.CapCheckRecordsReady

/-! A pure phase result for the record loop, before the real mark/DFS tail.
Every record performs its 17 paid queries before consistency handling.
Failure short-circuits; successful zero residual is an identity phase result,
not a claim that the machine has halted. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckRecordsRun : Nat → MachineState → OracleComp World (MachineState × Bool)
  | 0,state => pure (state,true)
  | count+1,state => do
      let result ← capCheckRecordRun state
      if result.2 then capCheckRecordsRun count result.1 else pure result

theorem cap_check_records_run_queries (count : Nat) (state : MachineState) :
    (capCheckRecordsRun count state).IsTotalQueryBound (17*count) := by
  induction count generalizing state with
  | zero => trivial
  | succ count ih =>
    rw [capCheckRecordsRun]
    have tail : ∀ result : MachineState × Bool,
        (if result.2 then capCheckRecordsRun count result.1 else pure result).IsTotalQueryBound
          (17*count) := by
      intro result
      cases passed : result.2
      · simp only [Bool.false_eq_true,↓reduceIte]
        trivial
      · simp only [↓reduceIte]
        exact ih _
    have total := isTotalQueryBound_bind (cap_check_record_run_queries state) tail
    convert total using 1 <;> omega

theorem cap_check_records_run_ready (input : CheckInput) (ordinal count : Nat)
    (state : MachineState) (ready : CapCheckRecordsReady input ordinal count state)
    (result : MachineState × Bool)
    (reachable : result ∈ support (capCheckRecordsRun count state))
    (passed : result.2=true) :
    CapCheckRecordsReady input (ordinal+count) 0 result.1 := by
  induction count generalizing ordinal state with
  | zero =>
    simp only [capCheckRecordsRun,support_pure,Set.mem_singleton_iff] at reachable
    subst result
    simpa only [Nat.add_zero] using ready
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
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        head headReachable headPassed
      have finished := ih (ordinal+1) head.1 nextReady tailReachable
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finished

end CommitGolfCandidate
