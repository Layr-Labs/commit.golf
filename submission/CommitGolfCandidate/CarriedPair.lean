import CommitGolfCandidate.CarriedInput
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem carried_pair_args (state : MachineState) (cursor : Nat)
    (input : state.getReg .x10=BitVec.ofNat 64 cursor)
    (output : state.getReg .x12=BitVec.ofNat 64 (cursor+32)) :
    streamingArgsState (state.setPC (state.pc-8)) cursor=state := by
  have same10 : state.setReg .x10 (BitVec.ofNat 64 cursor)=state := by
    rw [← input]
    cases state
    simp only [MachineState.setReg,MachineState.getReg]
    congr 1
    funext reg
    cases reg <;> rfl
  have same12 : state.setReg .x12 (BitVec.ofNat 64 (cursor+32))=state := by
    rw [← output]
    cases state
    simp only [MachineState.setReg,MachineState.getReg]
    congr 1
    funext reg
    cases reg <;> rfl
  unfold streamingArgsState
  change ((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
    (BitVec.ofNat 64 (cursor+32))).setPC (state.pc-8+8)=state
  rw [same10,same12,BitVec.sub_add_cancel,hoist_pc_self]

/-- With both carried arguments ready, the first block is the syscall alone. -/
theorem streaming_carried_pair (image : Image) (state : MachineState) (cursor : Nat)
    (input : state.getReg .x10=BitVec.ofNat 64 cursor)
    (output : state.getReg .x12=BitVec.ofNat 64 (cursor+32))
    (ready : StreamingOracleReady state) (aligned : cursor%8=0)
    (bounded : cursor+64≤MEMORY_BYTES)
    (fetched : fetch image state=some (.base .ECALL))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel
            (streamingReplyState (state.setPC (state.pc-8)) cursor answer) allowCoins
          return result.charge 8 1) := by
  let virtual := state.setPC (state.pc-8)
  have same : streamingArgsState virtual cursor=state := carried_pair_args state cursor input output
  have valid : oracleInput state=some (.inl (readBuffer state cursor 64)) := by
    have h := streaming_oracle_input virtual cursor ready aligned bounded
    rw [same] at h
    have memory : readBuffer virtual cursor 64=readBuffer state cursor 64 :=
      read_buffer_memory_congr _ _ rfl _ _
    rw [memory] at h
    exact h
  rw [Nat.add_comm 1 fuel,execute,fetched,if_pos ready.1,valid]
  simp only [writeOracleAnswer,oracleCycles,COMPRESSION_CYCLES]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  unfold streamingReplyState
  rw [same]
  simp [output,Execution.charge]
  rfl
end CommitGolfCandidate
