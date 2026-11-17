import CommitGolfCandidate.CapCheckSalt
import CommitGolfCandidate.PathRefinement

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer List.foldl capWordCopyPrefix
  checkPathCopyState capCheckSaltLoadedState capCheckSaltCopiedState

theorem cap_check_salt_copy_reference (state : MachineState) :
    capWordCopyPrefix .x25 .x21 0 0 state 8 = checkPathCopyState state 15 := by
  unfold capWordCopyPrefix checkPathCopyState
  apply congrArg (fun instructions : List Instr => instructions.foldl execInstrBr state)
  rfl

theorem cap_check_salt_loaded_memory (state : MachineState) :
    (capCheckSaltLoadedState state).mem = state.mem := by
  unfold capCheckSaltLoadedState
  rfl

theorem cap_check_salt_advance_memory (state : MachineState) :
    (capCheckSaltState state).mem = (capCheckSaltCopiedState state).mem := rfl

theorem cap_check_salt_digest (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 < 2^64) :
    readBuffer (capCheckSaltState state) 256 32 = readBuffer state address 32 := by
  have loadedScratch := (cap_check_salt_loaded_register state .x21 (by decide)).trans scratch
  have loadedPointer := (cap_check_salt_loaded_register state .x25 (by decide)).trans pointer
  have copied := check_salt_copy_digest (capCheckSaltLoadedState state) address
    loadedScratch loadedPointer aligned above bounded
  have copyReference : capCheckSaltCopiedState state =
      checkPathCopyState (capCheckSaltLoadedState state) 15 :=
    by
      unfold capCheckSaltCopiedState
      exact cap_check_salt_copy_reference _
  exact (read_buffer_memory_congr _ _ (cap_check_salt_advance_memory state) 256 32).trans
    ((congrArg (fun current => readBuffer current 256 32) copyReference).trans
      (copied.trans (read_buffer_memory_congr _ _
        (cap_check_salt_loaded_memory state) address 32)))

theorem cap_check_salt_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256 + 8*i)) :
    (capCheckSaltState state).getMem address = state.getMem address := by
  have loadedScratch := (cap_check_salt_loaded_register state .x21 (by decide)).trans scratch
  have copied := check_salt_copy_outside (capCheckSaltLoadedState state)
    address loadedScratch outside
  have copyReference : capCheckSaltCopiedState state =
      checkPathCopyState (capCheckSaltLoadedState state) 15 :=
    by
      unfold capCheckSaltCopiedState
      exact cap_check_salt_copy_reference _
  exact (congrArg (fun memory => memory address)
    (cap_check_salt_advance_memory state)).trans
      ((congrArg (fun current => current.getMem address) copyReference).trans
        (copied.trans (congrArg (fun memory => memory address)
          (cap_check_salt_loaded_memory state))))

end CommitGolfCandidate
