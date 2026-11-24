import CommitGolfCandidate.ChainedRelocation
import CommitGolfCandidate.ChainedPrefixInvariant

/-! Successful zero-query executions commute with relocation when private syscalls cannot succeed. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def relocatedExecution (delta : Word) (result : Execution) : Execution :=
  { result with state := relocatedState delta result.state }

private theorem execute_ordinary_match (image : Image) (s : MachineState) (instruction : Instruction)
    (steps : Nat) (coins : Bool) (fetched : fetch image s=some instruction) (ordinary : instruction≠.base .ECALL) :
    execute image (steps+1) s coins=
      match ordinaryStep s instruction with
      | none => pure ⟨.failure,s,1,0⟩
      | some next => do
          let result ← execute image steps next coins
          return result.charge (instructionCycles instruction) 0 := by
  cases instruction with
  | base instruction => cases instruction <;> simp_all [execute] <;> rfl
  | word op rd rs1 rs2 => simp only [execute,fetched]; rfl
  | sraiw rd rs shift => simp only [execute,fetched]; rfl

theorem relocate_successful_run (source target : Image) (delta : Word)
    (same : ∀ s instruction, fetch source s=some instruction →
      fetch target (relocatedState delta s)=some instruction)
    (commutes : ∀ s instruction, fetch source s=some instruction →
      ordinaryStep (relocatedState delta s) instruction=
        (ordinaryStep s instruction).map (relocatedState delta))
    (coins : Bool)
    (randomFails : ∀ s bytes (answer : BitVec (8*bytes)) steps result,
      fetch source s=some (.base .ECALL) →
      result∈support (execute source steps (writeBits s (s.getReg .x10) answer) coins) → result.exit≠.success)
    (steps : Nat) (s : MachineState) (result : Execution)
    (reached : result∈support (execute source steps s coins))
    (success : result.exit=.success) (calls : result.oracleCalls=0) :
    execute target steps (relocatedState delta s) coins=pure (relocatedExecution delta result) := by
  induction steps generalizing s result with
  | zero =>
    simp only [execute,support_pure,Set.mem_singleton_iff] at reached
    subst result
    contradiction
  | succ steps ih =>
    cases fetched : fetch source s with
    | none =>
      simp only [execute,fetched,support_pure,Set.mem_singleton_iff] at reached
      subst result
      contradiction
    | some instruction =>
      have movedFetch := same s instruction fetched
      by_cases ecall : instruction=.base .ECALL
      · subst instruction
        simp only [execute,fetched] at reached
        by_cases query : s.getReg .x5=0
        · simp only [query,ite_true] at reached
          cases input : oracleInput s with
          | none =>
            simp only [input,support_pure,Set.mem_singleton_iff] at reached
            subst result
            contradiction
          | some input =>
            simp only [input,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
            obtain ⟨answer,_,tail,_,rfl⟩ := reached
            change 1+tail.oracleCalls=0 at calls
            omega
        · by_cases halt : s.getReg .x5=1
          · simp only [query,halt,ite_true,ite_false,support_pure,Set.mem_singleton_iff] at reached
            subst result
            simp only [execute,movedFetch,relocated_reg,query,halt,ite_true,ite_false]
            rfl
          · simp only [query,halt,ite_false] at reached
            split at reached
            · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
              obtain ⟨answer,_,tail,live,rfl⟩ := reached
              exact False.elim ((randomFails s _ answer steps tail fetched live) success)
            · simp only [support_pure,Set.mem_singleton_iff] at reached
              subst result
              contradiction
      · rw [execute_ordinary_match source s instruction steps coins fetched ecall] at reached
        cases stepped : ordinaryStep s instruction with
        | none =>
          simp only [stepped,support_pure,Set.mem_singleton_iff] at reached
          subst result
          contradiction
        | some next =>
          simp only [stepped,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
          obtain ⟨tail,live,rfl⟩ := reached
          have movedStep : ordinaryStep (relocatedState delta s) instruction=some (relocatedState delta next) := by
            rw [commutes s instruction fetched,stepped]
            rfl
          have noCalls : tail.oracleCalls=0 := by simpa only [Execution.charge,Nat.zero_add] using calls
          rw [execute_ordinary_step target instruction _ _ steps coins movedFetch movedStep,
            ih next tail live success noCalls]
          rfl

end CommitGolfCandidate.Chained.Native
