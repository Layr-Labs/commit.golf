import CommitGolfCandidate.NonceOpeningTrace

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

theorem nonce_execute_none_no_success (image : Image) (fuel : Nat) (state : MachineState)
    (coins : Bool) (absent : fetch image state=none) (result : Execution)
    (reached : result∈support (execute image fuel state coins)) : result.exit≠.success := by
  cases fuel with
  | zero =>
    simp only [execute, support_pure, Set.mem_singleton_iff] at reached
    subst result
    change Exit.unfinished≠Exit.success
    decide
  | succ fuel =>
    simp only [execute, absent, support_pure, Set.mem_singleton_iff] at reached
    subst result
    change Exit.failure≠Exit.success
    decide

theorem nonce_execute_fault (image : Image) (fuel : Nat) (state : MachineState)
    (coins : Bool) (instruction : Instruction)
    (ordinary : instruction≠.base .ECALL)
    (fetched : fetch image state=some instruction)
    (failed : ordinaryStep state instruction=none) :
    execute image (fuel+1) state coins=pure ⟨.failure,state,1,0⟩ := by
  cases instruction with
  | base instruction => cases instruction <;> simp_all [execute, ordinaryStep]
  | word op rd rs1 rs2 => simp_all [execute, ordinaryStep]
  | sraiw rd rs shift => simp_all [execute, ordinaryStep]

theorem nonce_write_bits_pc {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) : (writeBits state address answer).pc=state.pc+4 := rfl

theorem nonce_write_answer_pc (state : MachineState) (address : Word)
    (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    (writeOracleAnswer state address query answer).pc=state.pc+4 := by
  cases query with
  | inl input => rfl
  | inr query => cases query <;> rfl

theorem nonce_after_halt_no_success (fuel : Nat) (state : MachineState) (coins : Bool)
    (pc : state.pc=4540) (result : Execution)
    (reached : result∈support (execute nonceOldOpeningImage fuel state coins)) :
    result.exit≠.success :=
  nonce_execute_none_no_success nonceOldOpeningImage fuel state coins
    (nonce_opening_after_halt_fetch state pc) result reached

theorem nonce_opening_ecall_success (fuel : Nat) (state : MachineState) (coins : Bool)
    (result : Execution) (fetched : fetch nonceOldOpeningImage state=some (.base .ECALL))
    (reached : result∈support (execute nonceOldOpeningImage (fuel+1) state coins))
    (success : result.exit=.success) :
    result=⟨.success,state,1,0⟩ ∧ state.getReg .x5=1 ∧ state.getReg .x10=0 := by
  have pc:=nonce_opening_ecall_pc state fetched
  by_cases oracleSelector : state.getReg .x5=0
  · rw [execute, fetched, if_pos oracleSelector] at reached
    cases input : oracleInput state with
    | none =>
      rw [input] at reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst result
      cases success
    | some query =>
      rw [input] at reached
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
      obtain ⟨answer,_,tail,tailReached,rfl⟩:=reached
      have nextPc : (writeOracleAnswer state (state.getReg .x12) query answer).pc=4540 := by
        rw [nonce_write_answer_pc, pc]
        decide
      exact False.elim ((nonce_after_halt_no_success fuel _ coins nextPc tail tailReached) success)
  · by_cases haltSelector : state.getReg .x5=1
    · rw [execute, fetched, if_neg oracleSelector, if_pos haltSelector] at reached
      by_cases exitZero : state.getReg .x10=0
      · rw [if_pos exitZero] at reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst result
        exact ⟨rfl,haltSelector,exitZero⟩
      · rw [if_neg exitZero] at reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst result
        cases success
    · rw [execute, fetched, if_neg oracleSelector, if_neg haltSelector] at reached
      by_cases random : coins && state.getReg .x5=2 && randomArgumentsValid state
      · rw [if_pos random] at reached
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
        obtain ⟨answer,_,tail,tailReached,rfl⟩:=reached
        have nextPc : (writeBits state (state.getReg .x10) answer).pc=4540 := by
          rw [nonce_write_bits_pc, pc]
          decide
        exact False.elim ((nonce_after_halt_no_success fuel _ coins nextPc tail tailReached) success)
      · rw [if_neg random] at reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst result
        cases success

theorem nonce_opening_success_trace (fuel : Nat) (state : MachineState) (coins : Bool)
    (result : Execution) (reached : result∈support (execute nonceOldOpeningImage fuel state coins))
    (success : result.exit=.success) :
    ∃ count, count ≤ fuel ∧ NonceOpeningTrace count state result := by
  induction fuel generalizing state result with
  | zero =>
    simp only [execute, support_pure, Set.mem_singleton_iff] at reached
    subst result
    cases success
  | succ fuel ih =>
    cases fetched : fetch nonceOldOpeningImage state with
    | none =>
      simp only [execute, fetched, support_pure, Set.mem_singleton_iff] at reached
      subst result
      cases success
    | some instruction =>
      by_cases syscall : instruction=.base .ECALL
      · subst instruction
        obtain ⟨equal,selector,exitZero⟩:=nonce_opening_ecall_success fuel state coins result
          fetched reached success
        subst result
        exact ⟨1,by omega,NonceOpeningTrace.halt state fetched selector exitZero⟩
      · cases stepped : ordinaryStep state instruction with
        | none =>
          rw [nonce_execute_fault nonceOldOpeningImage fuel state coins instruction syscall fetched stepped]
            at reached
          simp only [support_pure, Set.mem_singleton_iff] at reached
          subst result
          cases success
        | some next =>
          rw [execute_ordinary_step nonceOldOpeningImage instruction state next fuel coins fetched stepped]
            at reached
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
          obtain ⟨tail,tailReached,rfl⟩:=reached
          obtain ⟨count,bounded,trace⟩:=ih next tail tailReached success
          exact ⟨count+1,by omega,NonceOpeningTrace.step instruction fetched stepped trace⟩

end CommitGolfCandidate
