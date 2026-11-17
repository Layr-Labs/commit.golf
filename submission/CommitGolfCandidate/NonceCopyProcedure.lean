import CommitGolfCandidate.NonceCompressedFetch

namespace CommitGolfCandidate.NonceCopyProcedure
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def returnState (state : MachineState) : MachineState :=
  execInstrBr state (.JALR .x0 .x1 0)

theorem return_execute (image : Image) (state : MachineState) (fuel : Nat) (coins : Bool)
    (fetched : fetch image state=some (.base (.JALR .x0 .x1 0))) :
    execute image (1+fuel) state coins=
      (do let result ← execute image fuel (returnState state) coins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0))=some (returnState state) := by
    rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem return_memory (state : MachineState) : (returnState state).mem=state.mem := rfl

theorem return_register (state : MachineState) (reg : Reg) :
    (returnState state).getReg reg=state.getReg reg := by
  cases reg <;> rfl

theorem return_pc (state : MachineState)
    (aligned : state.getReg .x1 &&& ~~~(1:Word)=state.getReg .x1) :
    (returnState state).pc=state.getReg .x1 := by
  simpa [returnState, execInstrBr, signExtend12, MachineState.setPC] using aligned

theorem compact_return_fetched (state : MachineState) (pc : state.pc=4644) :
    fetch nonceCompactImage state=some (.base (.JALR .x0 .x1 0)) := by
  apply cap_image_fetch _ state 137 _ (by decide) pc
  rfl

theorem expanded_return_fetched (state : MachineState) (pc : state.pc=5120) :
    fetch nonceExpandedImage state=some (.base (.JALR .x0 .x1 0)) := by
  apply cap_image_fetch _ state 256 _ (by decide) pc
  rfl

private theorem charges (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0=result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem compact_copy_execute (source target count : Nat) (state : MachineState)
    (ready : NonceCopyReady.Forward 4620 source target count count state)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (6*count+1+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel
            (returnState (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) count state)) coins
          return result.charge (6*count+1) 0) := by
  let final := capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) count state
  have pc : final.pc=4644 := by
    have finished:=NonceCopyReady.forward_finished 4620 source target count count state ready
    have numeric : (4620:Word)+24=4644 := by decide
    simpa only [final, numeric] using finished.1
  rw [show 6*count+1+fuel=6*count+(1+fuel) by omega,
    NonceCopyReady.forward_execute nonceCompactImage 4620 source target count count state ready
      nonce_compact_copy_fetched (1+fuel) coins,
    return_execute nonceCompactImage final fuel coins (compact_return_fetched final pc)]
  simp only [bind_assoc, pure_bind, charges]
  rfl

theorem expanded_copy_execute (source target count : Nat) (state : MachineState)
    (ready : NonceBackwardReady.Backward 5096 source target count count state)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (6*count+1+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel
            (returnState (capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) count state)) coins
          return result.charge (6*count+1) 0) := by
  let final := capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) count state
  have pc : final.pc=5120 := by
    have finished:=NonceBackwardReady.backward_finished 5096 source target count count state ready
    have numeric : (5096:Word)+24=5120 := by decide
    simpa only [final, numeric] using finished.1
  rw [show 6*count+1+fuel=6*count+(1+fuel) by omega,
    NonceBackwardReady.backward_execute nonceExpandedImage 5096 source target count count state ready
      nonce_expanded_copy_fetched (1+fuel) coins,
    return_execute nonceExpandedImage final fuel coins (expanded_return_fetched final pc)]
  simp only [bind_assoc, pure_bind, charges]
  rfl

theorem loop_return_pc (backward : Bool) (state : MachineState) (count : Nat)
    (aligned : state.getReg .x1 &&& ~~~(1:Word)=state.getReg .x1) :
    (returnState (capCountedRun (fun current => NonceWordCopy.copyPrefix backward current 6) count state)).pc=
      state.getReg .x1 := by
  have kept:=NonceWordCopy.loop_register backward state count .x1 (by decide)
  rw [return_pc _ (by rw [kept]; exact aligned), kept]

end CommitGolfCandidate.NonceCopyProcedure
