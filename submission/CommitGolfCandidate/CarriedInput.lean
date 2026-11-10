import CommitGolfCandidate.StreamingExecution
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem prefix_first_identity (state : MachineState) (cursor : Nat)
    (input : state.getReg .x10=BitVec.ofNat 64 cursor) :
    streamingFirstState (state.setPC (state.pc-4)) cursor=state := by
  unfold streamingFirstState
  have same : state.setReg .x10 (state.getReg .x10)=state := by
    cases state
    simp only [MachineState.setReg,MachineState.getReg]
    congr 1
    funext reg
    cases reg <;> rfl
  rw [← input]
  change (state.setReg .x10 (state.getReg .x10)).setPC (state.pc-4+4)=state
  rw [same,BitVec.sub_add_cancel,hoist_pc_self]

theorem streaming_carried_args (state : MachineState) (cursor : Nat)
    (input : state.getReg .x10=BitVec.ofNat 64 cursor) :
    (state.setReg .x12 (BitVec.ofNat 64 (cursor+32))).setPC (state.pc+4)=
      streamingArgsState (state.setPC (state.pc-4)) cursor := by
  have same : state.setReg .x10 (BitVec.ofNat 64 cursor)=state := by
    rw [← input]
    cases state
    simp only [MachineState.setReg,MachineState.getReg]
    congr 1
    funext reg
    cases reg <;> rfl
  unfold streamingArgsState
  change (state.setReg .x12 (BitVec.ofNat 64 (cursor+32))).setPC (state.pc+4)=
    ((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
      (BitVec.ofNat 64 (cursor+32))).setPC (state.pc-4+8)
  rw [same]
  congr 1
  rw [show (8 : Word)=4+4 by decide,← BitVec.add_assoc,BitVec.sub_add_cancel]

/-- A carried first input pointer eliminates the first ordinary address instruction. -/
theorem streaming_carried_first (image : Image) (state : MachineState) (cursor : Nat)
    (outputOffset : BitVec 12)
    (input : state.getReg .x10=BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor%8=0)
    (bounded : cursor+64≤MEMORY_BYTES)
    (fetchOutput : fetch image state=some (.base (.ADDI .x12 .x8 outputOffset)))
    (stepOutput : ordinaryStep state (.base (.ADDI .x12 .x8 outputOffset))=
      some (streamingArgsState (state.setPC (state.pc-4)) cursor))
    (fetchCall : fetch image (streamingArgsState (state.setPC (state.pc-4)) cursor)=some (.base .ECALL))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (2+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel
            (streamingReplyState (state.setPC (state.pc-4)) cursor answer) allowCoins
          return result.charge 9 1) := by
  let virtual := state.setPC (state.pc-4)
  have virtualReady : StreamingOracleReady virtual := ready
  rw [show 2+fuel=(fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetchOutput stepOutput]
  have r5 := (streaming_args_ready virtual cursor virtualReady).1
  rw [execute,fetchCall,if_pos r5,streaming_oracle_input virtual cursor virtualReady aligned bounded]
  have memory : readBuffer virtual cursor 64=readBuffer state cursor 64 :=
    read_buffer_memory_congr _ _ rfl _ _
  rw [memory]
  simp only [writeOracleAnswer,oracleCycles,COMPRESSION_CYCLES,instructionCycles,bind_assoc,pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have output : (streamingArgsState virtual cursor).getReg .x12=BitVec.ofNat 64 (cursor+32) := rfl
  simp [output,streamingReplyState,Execution.charge,← Nat.add_assoc,virtual]
  rfl
end CommitGolfCandidate
