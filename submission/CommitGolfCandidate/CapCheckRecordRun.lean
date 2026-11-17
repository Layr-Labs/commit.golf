import CommitGolfCandidate.CapCheckLowerRecordBudget
import CommitGolfCandidate.CapCheckGroupInsert
import CommitGolfCandidate.CapCheckRecordNext
import CommitGolfCandidate.CapCheckLowerGroupReady

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckRecordResult (lower : MachineState) : MachineState × Bool :=
  let result := capCheckGroupResult lower
  if result.2 then (capCheckRecordNextPrefix result.1 3,true) else result

def capCheckRecordRun (state : MachineState) : OracleComp World (MachineState × Bool) := do
  let lower ← capCheckLowerRecord state
  pure (capCheckRecordResult lower)

def capCheckRecordTailSteps (lower : MachineState) : Nat :=
  capCheckGroupSteps lower + if (capCheckGroupResult lower).2 then 3 else 0

theorem cap_check_record_tail_steps_bound (lower : MachineState) :
    capCheckRecordTailSteps lower ≤ 25 := by
  have bound := cap_check_group_steps_bound lower
  unfold capCheckRecordTailSteps
  split <;> omega

theorem cap_check_record_result_passed (lower : MachineState) :
    (capCheckRecordResult lower).2 = (capCheckGroupResult lower).2 := by
  unfold capCheckRecordResult
  cases passed : (capCheckGroupResult lower).2 <;>
    simp only [passed,Bool.false_eq_true,↓reduceIte]

theorem cap_check_record_run_support (state : MachineState) (result : MachineState × Bool) :
    result ∈ support (capCheckRecordRun state) ↔
      ∃ lower ∈ support (capCheckLowerRecord state), result = capCheckRecordResult lower := by
  simp only [capCheckRecordRun,mem_support_bind_iff,support_pure,Set.mem_singleton_iff]

theorem cap_check_record_run_queries (state : MachineState) :
    (capCheckRecordRun state).IsTotalQueryBound 24 := by
  unfold capCheckRecordRun
  have tailBound : ∀ lower : MachineState,
      IsTotalQueryBound (pure (capCheckRecordResult lower) :
        OracleComp World (MachineState × Bool)) 0 := fun _ => by trivial
  exact isTotalQueryBound_bind (cap_check_lower_record_query_bound state) tailBound

theorem cap_check_record_result_collected (lower : MachineState) (roots next : CapRootMap)
    (group : Nat) (ready : CapCheckGroupReady lower group)
    (collected : CapCheckCollected lower roots)
    (accepted : capInsert roots group (readBuffer lower 256 32) = some next) :
    CapCheckCollected (capCheckRecordResult lower).1 next := by
  have stored := cap_check_group_insert_collected lower roots next collected group
    ready.bounded ready.index ready.leaves ready.marks ready.roots ready.scratch ready.one accepted
  have passed : (capCheckGroupResult lower).2 = true :=
    (cap_check_group_insert lower roots collected group ready.bounded ready.index
      ready.leaves ready.marks ready.roots ready.scratch ready.one).mpr
      (by rw [accepted]; rfl)
  simp only [capCheckRecordResult,passed,↓reduceIte]
  exact cap_check_collected_memory _ _ next (cap_check_record_next_memory _) stored

end CommitGolfCandidate
