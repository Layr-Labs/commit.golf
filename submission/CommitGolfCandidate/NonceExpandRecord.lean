import CommitGolfCandidate.NonceExpandTail

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceBackwardReturned (state : MachineState) (count : Nat) : MachineState :=
  NonceCopyProcedure.returnState
    (capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) count state)

theorem nonce_backward_returned_register (state : MachineState) (count : Nat) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceBackwardReturned state count).getReg reg=state.getReg reg := by
  rw [nonceBackwardReturned,NonceCopyProcedure.return_register]
  exact NonceWordCopy.loop_register true state count reg outside

theorem nonce_backward_returned_finished (source target count : Nat) (state : MachineState)
    (ready : NonceBackwardReady.Backward 5096 source target count count state) :
    (nonceBackwardReturned state count).getReg .x23=BitVec.ofNat 64 (source-8) ∧
    (nonceBackwardReturned state count).getReg .x25=BitVec.ofNat 64 (target-8) ∧
    (nonceBackwardReturned state count).getReg .x28=0 := by
  have finished:=NonceBackwardReady.backward_finished 5096 source target count count state ready
  simpa only [nonceBackwardReturned,NonceCopyProcedure.return_register] using
    And.intro finished.2.2.1 (And.intro finished.2.2.2 finished.2.1)

def nonceExpandSiblingCall (state : MachineState) : MachineState := nonceExpandCallPrefix false state 2

def nonceExpandSiblingsCopied (state : MachineState) : MachineState :=
  nonceBackwardReturned (nonceExpandSiblingCall state) 64

def nonceExpandNonceCall (state : MachineState) : MachineState :=
  nonceExpandCallPrefix true (nonceExpandSiblingsCopied state) 4

def nonceExpandNonceCopied (state : MachineState) : MachineState :=
  nonceBackwardReturned (nonceExpandNonceCall state) 3

def nonceExpandRecordState (state : MachineState) : MachineState := nonceExpandTailState (nonceExpandNonceCopied state)

theorem nonce_expand_sibling_return_pc (state : MachineState) (pc : state.pc=5016) :
    (nonceExpandSiblingsCopied state).pc=5024 := by
  have control:=nonce_expand_call_control false state pc
  have link : (nonceExpandSiblingCall state).getReg .x1=5024 := control.2.2
  rw [nonceExpandSiblingsCopied,nonceBackwardReturned,NonceCopyProcedure.loop_return_pc]
  · exact link
  · rw [link]
    decide

theorem nonce_expand_nonce_return_pc (state : MachineState) (pc : state.pc=5016) :
    (nonceExpandNonceCopied state).pc=5040 := by
  have returned:=nonce_expand_sibling_return_pc state pc
  have control:=nonce_expand_call_control true (nonceExpandSiblingsCopied state) returned
  have link : (nonceExpandNonceCall state).getReg .x1=5040 := control.2.2
  rw [nonceExpandNonceCopied,nonceBackwardReturned,NonceCopyProcedure.loop_return_pc]
  · exact link
  · rw [link]
    decide

private theorem copy_execute (source target count : Nat) (state : MachineState)
    (ready : NonceBackwardReady.Backward 5096 source target count count state)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (6*count+1+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceBackwardReturned state count) coins
          return result.charge (6*count+1) 0) :=
  NonceCopyProcedure.expanded_copy_execute source target count state ready fuel coins

private theorem charges (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0=result.charge (second+first) 0 := by
  simp only [Execution.charge,Nat.zero_add,Nat.add_assoc]

theorem nonce_expand_record_execute (state : MachineState) (pc : state.pc=5016)
    (source target : Nat)
    (siblingsReady : NonceBackwardReady.Backward 5096 (source+24) (target+32) 64 64 (nonceExpandSiblingCall state))
    (paddingValid : accessValid ((nonceExpandSiblingsCopied state).getReg .x25) 8=true)
    (nonceReady : NonceBackwardReady.Backward 5096 source target 3 3 (nonceExpandNonceCall state))
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (412+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandRecordState state) coins
          return result.charge 412 0) := by
  have siblingPc:=nonce_expand_sibling_return_pc state pc
  have noncePc:=nonce_expand_nonce_return_pc state pc
  have firstCall:=nonce_expand_call_execute false state pc (by intro impossible; cases impossible)
    (385+(4+(19+(2+fuel)))) coins
  change execute nonceExpandedImage (2+(385+(4+(19+(2+fuel))))) state coins=_ at firstCall
  have secondCall:=nonce_expand_call_execute true (nonceExpandSiblingsCopied state) siblingPc
    (fun _ => paddingValid) (19+(2+fuel)) coins
  change execute nonceExpandedImage (4+(19+(2+fuel))) (nonceExpandSiblingsCopied state) coins=_ at secondCall
  rw [show 412+fuel=2+(385+(4+(19+(2+fuel)))) by omega,firstCall]
  change ((execute nonceExpandedImage (385+(4+(19+(2+fuel)))) (nonceExpandSiblingCall state) coins)
    >>= fun result => pure (result.charge 2 0))=_
  rw [copy_execute (source+24) (target+32) 64 _ siblingsReady (4+(19+(2+fuel))) coins]
  change (((execute nonceExpandedImage (4+(19+(2+fuel))) (nonceExpandSiblingsCopied state) coins)
    >>= fun result => pure (result.charge 385 0)) >>= fun result => pure (result.charge 2 0))=_
  rw [secondCall]
  change ((((execute nonceExpandedImage (19+(2+fuel)) (nonceExpandNonceCall state) coins)
    >>= fun result => pure (result.charge 4 0)) >>= fun result => pure (result.charge 385 0))
    >>= fun result => pure (result.charge 2 0))=_
  rw [copy_execute source target 3 _ nonceReady (2+fuel) coins]
  change (((((execute nonceExpandedImage (2+fuel) (nonceExpandNonceCopied state) coins)
    >>= fun result => pure (result.charge 19 0)) >>= fun result => pure (result.charge 4 0))
    >>= fun result => pure (result.charge 385 0)) >>= fun result => pure (result.charge 2 0))=_
  rw [nonce_expand_tail_execute _ noncePc fuel coins]
  simp only [bind_assoc,pure_bind,charges]
  rfl

end CommitGolfCandidate
