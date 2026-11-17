import CommitGolfCandidate.NonceExpandRecord
import CommitGolfCandidate.NonceBackwardMemory
import CommitGolfCandidate.NonceCompactMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_backward_returned_memory (source target count : Nat) (state : MachineState)
    (ready : NonceBackwardReady.Backward 5096 source target count count state) :
    NonceWordMove source target count state (nonceBackwardReturned state count) := by
  have copied:=NonceBackwardMemory.loop_memory 5096 source target count state ready
  have memory : (nonceBackwardReturned state count).mem=
      (capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) count state).mem :=
    NonceCopyProcedure.return_memory _
  constructor
  · intro index inside
    simpa only [MachineState.getMem,memory] using copied.1 index inside
  · intro location outside
    simpa only [MachineState.getMem,memory] using copied.2 location outside

def nonceExpandPaddingState (state : MachineState) : MachineState :=
  (nonceExpandSiblingsCopied state).setMem ((nonceExpandSiblingsCopied state).getReg .x25) 0

theorem nonce_expand_record_moves (state : MachineState) (source target : Nat)
    (siblingsReady : NonceBackwardReady.Backward 5096 (source+24) (target+32) 64 64 (nonceExpandSiblingCall state))
    (nonceReady : NonceBackwardReady.Backward 5096 source target 3 3 (nonceExpandNonceCall state)) :
    NonceWordMove (source+24) (target+32) 64 state (nonceExpandSiblingsCopied state) ∧
    (nonceExpandPaddingState state).mem=((nonceExpandSiblingsCopied state).setMem (address target 3) 0).mem ∧
    NonceWordMove source target 3 (nonceExpandPaddingState state) (nonceExpandNonceCopied state) ∧
    (nonceExpandRecordState state).mem=(nonceExpandNonceCopied state).mem := by
  refine ⟨?_,?_,?_,nonce_expand_tail_memory _⟩
  · exact nonce_word_move_transfer (source+24) (target+32) 64 _ _ state (nonceExpandSiblingsCopied state)
      (nonce_backward_returned_memory (source+24) (target+32) 64 _ siblingsReady)
      (nonce_expand_call_memory false state) rfl
  · have copied:=nonce_backward_returned_finished _ _ 64 _ siblingsReady
    have targetPointer : (nonceExpandSiblingsCopied state).getReg .x25=address target 3 := copied.2.1
    unfold nonceExpandPaddingState
    rw [targetPointer]
  · exact nonce_word_move_transfer source target 3 _ _ (nonceExpandPaddingState state) (nonceExpandNonceCopied state)
      (nonce_backward_returned_memory source target 3 _ nonceReady)
      (nonce_expand_call_memory true (nonceExpandSiblingsCopied state)) rfl

end CommitGolfCandidate
