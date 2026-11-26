import CommitGolfCandidate.ChainedRelocationRun
import CommitGolfCandidate.ChainedSplicedFetch

/-! Whole chained-controller execution at the delivered cached-prefix dispatch address. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute
attribute [local irreducible] openingControllerWords

theorem controller_random_cannot_succeed (s : MachineState) (bytes : Nat) (answer : BitVec (8*bytes))
    (steps : Nat) (coins : Bool) (result : Execution)
    (fetched : fetch openingControllerImage s=some (.base .ECALL))
    (reached : result∈support (execute openingControllerImage steps (writeBits s (s.getReg .x10) answer) coins)) :
    result.exit≠.success := by
  obtain ⟨i,pc,instruction⟩ := controller_fetched s (.base .ECALL) fetched
  have last := controller_ecall_last i (Instruction.base.inj instruction.symm)
  have nextPC : (writeBits s (s.getReg .x10) answer).pc=13088#64 := by
    change s.pc+4=13088#64
    rw [pc,last]
    rfl
  have noFetch : fetch openingControllerImage (writeBits s (s.getReg .x10) answer)=none := by
    rw [fetch,nextPC,ite_eq_left (by decide)]
    change (match openingControllerWords[2248]? with | some word => decodeInstruction word | none => none)=none
    rw [List.getElem?_eq_none_iff.mpr (by rw [opening_controller_words_length])]
  cases steps <;> simp only [execute,noFetch,support_pure,Set.mem_singleton_iff] at reached <;>
    subst result <;> simp

theorem controller_run_relocated (steps : Nat) (s : MachineState) (coins : Bool) (result : Execution)
    (reached : result∈support (execute openingControllerImage steps s coins))
    (success : result.exit=.success) (calls : result.oracleCalls=0) :
    execute cachedControllerImage steps (relocatedState 5740 s) coins=
      pure (relocatedExecution 5740 result) := by
  apply relocate_successful_run openingControllerImage cachedControllerImage 5740 cached_controller_same
    ?_ coins ?_ steps s result reached success calls
  · intro before instruction fetched
    obtain ⟨i,pc,rfl⟩ := controller_fetched before instruction fetched
    exact ordinary_step_relocated 5740 before _ (opening_controller_relative i)
  · intro before bytes answer fuel outcome fetched live
    exact controller_random_cannot_succeed before bytes answer fuel coins outcome fetched live

theorem controller_execution_relocated (steps : Nat) (s : MachineState) (coins : Bool)
    (after : MachineState) (cycles : Nat)
    (ran : execute openingControllerImage steps s coins=pure ⟨.success,after,cycles,0⟩) :
    execute cachedControllerImage steps (relocatedState 5740 s) coins=
      pure ⟨.success,relocatedState 5740 after,cycles,0⟩ := by
  apply controller_run_relocated steps s coins ⟨.success,after,cycles,0⟩ ?_ rfl rfl
  rw [ran]
  simp only [support_pure,Set.mem_singleton_iff]

end CommitGolfCandidate.Chained.Native
