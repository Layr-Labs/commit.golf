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
    (ready : NonceCopyReady.Forward 4620 source target count count state) :
    NonceWordMove source target count state (nonceCopyReturned state count) := by
  have copied:=NonceCopyMemory.loop_memory 4620 source target count state ready
  have memory : (nonceCopyReturned state count).mem=
      (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) count state).mem :=
    NonceCopyProcedure.return_memory _
  constructor
  · intro index inside
    simpa only [MachineState.getMem, memory] using copied.1 index inside
  · intro location outside
    simpa only [MachineState.getMem, memory] using copied.2 location outside

theorem nonce_compact_record_moves (state : MachineState) (source target : Nat)
    (nonceReady : NonceCopyReady.Forward 4620 source target 3 3 (nonceCompactNonceCall state))
    (siblingsReady : NonceCopyReady.Forward 4620 (source+32) (target+24) 64 64
      (nonceCompactSiblingCall state)) :
    NonceWordMove source target 3 state (nonceCompactNonceCopied state) ∧
    NonceWordMove (source+32) (target+24) 64
      (nonceCompactNonceCopied state) (nonceCompactSiblingsCopied state) ∧
    (nonceCompactRecordState state).mem=(nonceCompactSiblingsCopied state).mem := by
  refine ⟨?_,?_,nonce_compact_tail_memory _⟩
  · exact nonce_word_move_transfer source target 3 _ _ state (nonceCompactNonceCopied state)
      (nonce_copy_returned_memory source target 3 _ nonceReady)
      (nonce_compact_call_memory false state) rfl
  · exact nonce_word_move_transfer (source+32) (target+24) 64 _ _
      (nonceCompactNonceCopied state) (nonceCompactSiblingsCopied state)
      (nonce_copy_returned_memory (source+32) (target+24) 64 _ siblingsReady)
      (nonce_compact_call_memory true (nonceCompactNonceCopied state)) rfl

end CommitGolfCandidate
