import CommitGolfCandidate.NonceCompactRecord
import CommitGolfCandidate.NonceCopyMemory

/-! Memory effects of the real copy procedures and compactor calls. Every
write is accounted for, including the frame outside the destination words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceWordMove (source target count : Nat) (before after : MachineState) : Prop where
  copied : ∀ index < count,
    after.getMem (address target index)=before.getMem (address source index)
  frame : ∀ location, (∀ index < count, location ≠ address target index) →
    after.getMem location=before.getMem location

theorem nonce_word_move_transfer (source target count : Nat)
    (before after before' after' : MachineState)
    (effect : NonceWordMove source target count before after)
    (first : before.mem=before'.mem) (last : after.mem=after'.mem) :
    NonceWordMove source target count before' after' := by
  constructor
  · intro index inside
    simpa only [MachineState.getMem, first, last] using effect.copied index inside
  · intro location outside
    simpa only [MachineState.getMem, first, last] using effect.frame location outside

theorem nonce_copy_returned_memory (source target count : Nat) (state : MachineState)
    (ready : NonceCopyReady.Forward 5144 source target count count state) :
    NonceWordMove source target count state (nonceCopyReturned state count) := by
  have copied:=NonceCopyMemory.loop_memory 5144 source target count state ready
  have memory : (nonceCopyReturned state count).mem=
      (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) count state).mem :=
    NonceCopyProcedure.return_memory _
  constructor
  · intro index inside
    simpa only [MachineState.getMem, memory] using copied.1 index inside
  · intro location outside
    simpa only [MachineState.getMem, memory] using copied.2 location outside

end CommitGolfCandidate
