import CommitGolfCandidate.Commit
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def copyOps : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56]
private def argOps : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

theorem outer_write {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (value : Word) :
    writeBits (state.setReg .x20 value) address answer =
      (writeBits state address answer).setReg .x20 value := by
  have byte_reg (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setReg .x20 value).setByte a b = (s.setByte a b).setReg .x20 value := by
    cases s; rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setReg .x20 value) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setReg .x20 value := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons,byte_reg] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  rfl

theorem outer_copy (state : MachineState) (value : Word) :
    commitLeafCopyState (state.setReg .x20 value) =
      (commitLeafCopyState state).setReg .x20 value := by
  change copyOps.foldl execInstrBr (state.setReg .x20 value) =
    (copyOps.foldl execInstrBr state).setReg .x20 value
  cases state
  dsimp [copyOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.getMem,MachineState.setMem,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_compression (state : MachineState) (value : Word) (answer : BitVec 256) :
    commitCompressionState (state.setReg .x20 value) answer =
      (commitCompressionState state answer).setReg .x20 value := by
  have argsShift : argOps.foldl execInstrBr (state.setReg .x20 value) =
      (argOps.foldl execInstrBr state).setReg .x20 value := by
    cases state
    dsimp [argOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
      MachineState.setReg,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  change writeBits (argOps.foldl execInstrBr (state.setReg .x20 value)) 256 answer =
    (writeBits (argOps.foldl execInstrBr state) 256 answer).setReg .x20 value
  rw [argsShift,outer_write]
theorem outer_step (state : MachineState) (value : Word) (answer : BitVec 256) :
    commitLeafStepState (state.setReg .x20 value) answer =
      (commitLeafStepState state answer).setReg .x20 value := by
  unfold commitLeafStepState
  rw [outer_copy,outer_compression]
  generalize commitCompressionState (commitLeafCopyState state) answer = middle
  cases middle
  dsimp [commitLeafNextState,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_ready (state : MachineState) (value : Word) :
    commitLeafReadyState (state.setReg .x20 value) =
      (commitLeafReadyState state).setReg .x20 value := by
  change argOps.foldl execInstrBr (((state.setReg .x20 value).setReg .x28 8).setPC 4436) =
    (argOps.foldl execInstrBr ((state.setReg .x28 8).setPC 4436)).setReg .x20 value
  cases state
  dsimp [argOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_loop_bind {α : Type} (state : MachineState) (value : Word) (count : Nat)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitLeafLoop (state.setReg .x20 value) count
        continuation finished) =
      (do let finished ← commitLeafLoop state count
          continuation (finished.setReg .x20 value)) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    have inputEq : readBuffer (commitLeafCopyState (state.setReg .x20 value)) 256 64 =
        readBuffer (commitLeafCopyState state) 256 64 := by
      rw [outer_copy]
      rfl
    have tailEq :
        (fun answer : BitVec 256 => do
          let finished ← commitLeafLoop (commitLeafStepState (state.setReg .x20 value) answer) count
          continuation finished) =
        (fun answer : BitVec 256 => do
          let finished ← commitLeafLoop (commitLeafStepState state answer) count
          continuation (finished.setReg .x20 value)) := by
      funext answer
      rw [outer_step]
      exact ih _
    simp only [commitLeafLoop,bind_assoc]
    exact congrArg₂ (fun (input : BitVec COMPRESSION_INPUT_LENGTH)
      (tail : BitVec 256 → OracleComp World α) =>
        (liftM (World.query (.inr (.inl input))) : OracleComp World (BitVec 256)) >>= tail)
      inputEq tailEq
private def mainOps (source destination : Reg) (offset : Nat) : List Instr :=
  [.LD .x6 source (BitVec.ofNat 12 offset),.SD destination .x6 0,
   .LD .x6 source (BitVec.ofNat 12 (offset+8)),.SD destination .x6 8,
   .LD .x6 source (BitVec.ofNat 12 (offset+16)),.SD destination .x6 16,
   .LD .x6 source (BitVec.ofNat 12 (offset+24)),.SD destination .x6 24]

set_option maxHeartbeats 2000000 in
theorem outer_main_copy (state : MachineState) (value : Word) (start : Nat)
    (location : start=46 ∨ start=55 ∨ start=79) :
    commitCopyState (state.setReg .x20 value) start =
      (commitCopyState state start).setReg .x20 value := by
  rcases location with rfl | rfl | rfl
  · change (mainOps .x18 .x21 0).foldl execInstrBr (state.setReg .x20 value) =
      ((mainOps .x18 .x21 0).foldl execInstrBr state).setReg .x20 value
    cases state
    dsimp [mainOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  · change (mainOps .x21 .x23 0).foldl execInstrBr (state.setReg .x20 value) =
      ((mainOps .x21 .x23 0).foldl execInstrBr state).setReg .x20 value
    cases state
    dsimp [mainOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  · change (mainOps .x9 .x26 32).foldl execInstrBr (state.setReg .x20 value) =
      ((mainOps .x9 .x26 32).foldl execInstrBr state).setReg .x20 value
    cases state
    dsimp [mainOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl

theorem outer_position_state (state : MachineState) (value : Word) :
    commitPositionState (state.setReg .x20 value) =
      (commitPositionState state).setReg .x20 value := by
  unfold commitPositionState
  rw [outer_main_copy state value 46 (Or.inl rfl)]
  unfold commitLeafCallState
  generalize commitCopyState state 46=middle
  cases middle
  dsimp [MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

def outerFinish (state : MachineState) (pc : Word) : MachineState :=
  (state.setReg .x20 0).setPC pc

theorem outer_next_erase (state : MachineState) (value pc : Word) :
    outerFinish (commitPositionNextState (state.setReg .x20 value)) pc =
      outerFinish (commitPositionNextState state) pc := by
  cases state
  dsimp [outerFinish,commitPositionNextState,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_pc (state : MachineState) (value pc : Word) :
    (state.setReg .x20 value).setPC pc=(state.setPC pc).setReg .x20 value := by
  cases state
  rfl

theorem outer_position_bind {α : Type} (state : MachineState) (value pc : Word)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitPositionRun (state.setReg .x20 value)
        continuation (outerFinish finished pc)) =
      (do let finished ← commitPositionRun state
          continuation (outerFinish finished pc)) := by
  simp only [commitPositionRun,bind_assoc,pure_bind]
  rw [outer_position_state,outer_ready]
  have frame :
      (do let leaf ← commitLeafLoop
            ((commitLeafReadyState (commitPositionState state)).setReg .x20 value) 8
          continuation (outerFinish (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)) pc)) =
      (do let leaf ← commitLeafLoop (commitLeafReadyState (commitPositionState state)) 8
          continuation (outerFinish (commitPositionNextState
            (commitCopyState ((leaf.setReg .x20 value).setPC 4316) 55)) pc)) :=
    outer_loop_bind (commitLeafReadyState (commitPositionState state)) value 8
      (fun leaf => continuation (outerFinish
        (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)) pc))
  rw [frame]
  apply congrArg (fun tail => commitLeafLoop (commitLeafReadyState (commitPositionState state)) 8 >>= tail)
  funext leaf
  rw [outer_pc,outer_main_copy _ value 55 (Or.inr (Or.inl rfl)),outer_next_erase]
set_option maxHeartbeats 2000000 in
theorem outer_main_copy_pc (state : MachineState) (pc : Word) (start : Nat)
    (location : start=46 ∨ start=55 ∨ start=79) :
    commitCopyState (state.setPC pc) start =
      (commitCopyState state start).setPC (pc+32) := by
  rcases location with rfl | rfl | rfl
  · change (mainOps .x18 .x21 0).foldl execInstrBr (state.setPC pc) =
      ((mainOps .x18 .x21 0).foldl execInstrBr state).setPC (pc+32)
    cases state
    dsimp [mainOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    congr 1
    simp [BitVec.add_assoc]
  · change (mainOps .x21 .x23 0).foldl execInstrBr (state.setPC pc) =
      ((mainOps .x21 .x23 0).foldl execInstrBr state).setPC (pc+32)
    cases state
    dsimp [mainOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    congr 1
    simp [BitVec.add_assoc]
  · change (mainOps .x9 .x26 32).foldl execInstrBr (state.setPC pc) =
      ((mainOps .x9 .x26 32).foldl execInstrBr state).setPC (pc+32)
    cases state
    dsimp [mainOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,
      MachineState.getMem,MachineState.setMem,MachineState.setPC]
    congr 1
    simp [BitVec.add_assoc]

theorem outer_position_state_pc (state : MachineState) (pc : Word) :
    commitPositionState (state.setPC pc)=commitPositionState state := by
  unfold commitPositionState
  rw [outer_main_copy_pc state pc 46 (Or.inl rfl)]
  unfold commitLeafCallState
  generalize commitCopyState state 46=middle
  cases middle
  rfl

theorem outer_position_run_pc (state : MachineState) (pc : Word) :
    commitPositionRun (state.setPC pc)=commitPositionRun state := by
  unfold commitPositionRun
  rw [outer_position_state_pc]
end CommitGolfCandidate
