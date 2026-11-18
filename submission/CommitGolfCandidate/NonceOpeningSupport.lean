import CommitGolfCandidate.NonceOpeningTrace

/-! Generic support facts about runs: a missing instruction or a faulting ordinary step ends the
run without success, and syscall replies advance the pc by one instruction. -/
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

end CommitGolfCandidate
