import CommitGolfCandidate.CapCheckPathBlock
import CommitGolfCandidate.CapWordCopyPC
import CommitGolfCandidate.PathRefinement
import CommitGolfCandidate.CapCheckLeafReferenceBase

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer List.foldl capWordCopyPrefix checkPathCopyState

private theorem copy_even (state : MachineState) :
    capWordCopyPrefix .x25 .x21 0 32 state 8 = checkPathCopyState state 48 := by
  unfold capWordCopyPrefix checkPathCopyState
  apply congrArg (fun instructions : List Instr => instructions.foldl execInstrBr state)
  rfl

private theorem copy_current (state : MachineState) :
    capWordCopyPrefix .x21 .x21 0 32 state 8 = checkPathCopyState state 31 := by
  unfold capWordCopyPrefix checkPathCopyState
  apply congrArg (fun instructions : List Instr => instructions.foldl execInstrBr state)
  rfl

private theorem copy_odd (state : MachineState) :
    capWordCopyPrefix .x25 .x21 0 0 state 8 = checkPathCopyState state 39 := by
  unfold capWordCopyPrefix checkPathCopyState
  apply congrArg (fun instructions : List Instr => instructions.foldl execInstrBr state)
  rfl

theorem cap_check_path_prepared_reference (state : MachineState) :
    capCheckPathPreparedState state = (checkPathPreparedState state).setPC 4380 := by
  have branch :
      capCheckPathBranchState state = (checkPathBranchState state).setPC
        (if state.getReg .x20 &&& 1 = 0 then 4348 else 4280) := rfl
  unfold capCheckPathPreparedState checkPathPreparedState
  by_cases even : state.getReg .x20 &&& 1 = 0
  · rw [if_pos even, if_pos even, branch, if_pos even,
      cap_word_copy_pc_frame _ _ _ _ _ _ 8 (by decide), copy_even]
    rfl
  · rw [if_neg even, if_neg even, branch, if_neg even,
      cap_word_copy_pc_frame _ _ _ _ _ _ 8 (by decide), copy_current,
      cap_word_copy_pc_frame _ _ _ _ _ _ 8 (by decide), copy_odd]
    rfl

theorem cap_check_path_input (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address) (bounded : address+32 < 2^64) :
    readBuffer (capCheckPathPreparedState state) 256 64 =
      if state.getReg .x20 &&& 1 = 0 then
        readBuffer state address 32 ++ readBuffer state 256 32
      else readBuffer state 256 32 ++ readBuffer state address 32 := by
  rw [cap_check_path_prepared_reference]
  exact (read_buffer_memory_congr ((checkPathPreparedState state).setPC 4380)
    (checkPathPreparedState state) rfl 256 64).trans
    (check_path_input state address scratch pointer aligned above bounded)

end CommitGolfCandidate
