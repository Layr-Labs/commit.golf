import CommitGolfCandidate.NonceCompactTail
import CommitGolfCandidate.NonceFixedCopy

/-! One concrete outer record iteration consists of a three-word nonce copy,
a padding skip, a sixty-four-word sibling copy and the counted loop tail.
The exact cycle total is 402; memory-window readiness remains explicit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCopyReturned (state : MachineState) (count : Nat) : MachineState :=
  NonceCopyProcedure.returnState
    (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) count state)

theorem nonce_copy_returned_register (state : MachineState) (count : Nat) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceCopyReturned state count).getReg reg=state.getReg reg := by
  rw [nonceCopyReturned, NonceCopyProcedure.return_register]
  exact NonceWordCopy.loop_register false state count reg outside

theorem nonce_copy_returned_finished (source target count : Nat) (state : MachineState)
    (ready : NonceCopyReady.Forward 4620 source target count count state) :
    (nonceCopyReturned state count).getReg .x23=BitVec.ofNat 64 (source+8*count) ∧
    (nonceCopyReturned state count).getReg .x25=BitVec.ofNat 64 (target+8*count) ∧
    (nonceCopyReturned state count).getReg .x28=0 := by
  have finished:=NonceCopyReady.forward_finished 4620 source target count count state ready
  simpa only [nonceCopyReturned, NonceCopyProcedure.return_register] using
    And.intro finished.2.2.1 (And.intro finished.2.2.2 finished.2.1)

def nonceCompactNonceCall (state : MachineState) : MachineState :=
  nonceCompactCallPrefix false state 2

def nonceCompactNonceCopied (state : MachineState) : MachineState :=
  nonceCopyReturned (nonceCompactNonceCall state) 3

def nonceCompactSiblingCall (state : MachineState) : MachineState :=
  nonceCompactCallPrefix true (nonceCompactNonceCopied state) 3

def nonceCompactSiblingsCopied (state : MachineState) : MachineState :=
  nonceCopyReturned (nonceCompactSiblingCall state) 64

def nonceCompactRecordState (state : MachineState) : MachineState :=
  nonceCompactTailState (nonceCompactSiblingsCopied state)

theorem nonce_compact_nonce_return_pc (state : MachineState) (pc : state.pc=4560) :
    (nonceCompactNonceCopied state).pc=4568 := by
  have control:=nonce_compact_call_control false state pc
  have link : (nonceCompactNonceCall state).getReg .x1=4568 := control.2.2
  rw [nonceCompactNonceCopied, nonceCopyReturned, NonceCopyProcedure.loop_return_pc]
  · exact link
  · rw [link]
    decide

theorem nonce_compact_sibling_return_pc (state : MachineState) (pc : state.pc=4560) :
    (nonceCompactSiblingsCopied state).pc=4580 := by
  have returned:=nonce_compact_nonce_return_pc state pc
  have control:=nonce_compact_call_control true (nonceCompactNonceCopied state) returned
  have link : (nonceCompactSiblingCall state).getReg .x1=4580 := control.2.2
  rw [nonceCompactSiblingsCopied, nonceCopyReturned, NonceCopyProcedure.loop_return_pc]
  · exact link
  · rw [link]
    decide

theorem nonce_compact_record_outer_counter (state : MachineState) :
    (nonceCompactSiblingsCopied state).getReg .x24=state.getReg .x24 := by
  rw [nonceCompactSiblingsCopied, nonce_copy_returned_register _ _ .x24 (by decide)]
  change (nonceCompactCallPrefix true (nonceCompactNonceCopied state)
    (nonceCompactCallCount true)).getReg .x24=_
  rw [nonce_compact_call_register true _ .x24 (by decide)]
  rw [nonceCompactNonceCopied, nonce_copy_returned_register _ _ .x24 (by decide)]
  change (nonceCompactCallPrefix false state (nonceCompactCallCount false)).getReg .x24=_
  exact nonce_compact_call_register false state .x24 (by decide)

private theorem charges (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0=result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem nonce_compact_record_execute (state : MachineState) (pc : state.pc=4560)
    (source target : Nat)
    (nonceReady : NonceCopyReady.Forward 4620 source target 3 3 (nonceCompactNonceCall state))
    (siblingsReady : NonceCopyReady.Forward 4620 (source+32) (target+24) 64 64
      (nonceCompactSiblingCall state)) (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (402+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactRecordState state) coins
          return result.charge 402 0) := by
  have noncePc:=nonce_compact_nonce_return_pc state pc
  have siblingsPc:=nonce_compact_sibling_return_pc state pc
  have firstCall:=nonce_compact_call_execute false state pc (10+(3+(385+(2+fuel)))) coins
  change execute nonceCompactImage (2+(10+(3+(385+(2+fuel))))) state coins=_ at firstCall
  have secondCall:=nonce_compact_call_execute true (nonceCompactNonceCopied state) noncePc
    (385+(2+fuel)) coins
  change execute nonceCompactImage (3+(385+(2+fuel))) (nonceCompactNonceCopied state) coins=_ at secondCall
  rw [show 402+fuel=2+(10+(3+(385+(2+fuel)))) by omega, firstCall]
  change ((execute nonceCompactImage (10+(3+(385+(2+fuel))))
    ((nonceCompactNonceCall state).setPC 4648) coins) >>= fun result => pure (result.charge 2 0))=_
  rw [nonce_fixed_copy_execute source target _ nonceReady (3+(385+(2+fuel))) coins]
  change (((execute nonceCompactImage (3+(385+(2+fuel)))
    (nonceCompactNonceCopied state) coins) >>= fun result => pure (result.charge 10 0))
    >>= fun result => pure (result.charge 2 0))=_
  rw [secondCall]
  change ((((execute nonceCompactImage (385+(2+fuel)) (nonceCompactSiblingCall state) coins)
    >>= fun result => pure (result.charge 3 0)) >>= fun result => pure (result.charge 10 0))
    >>= fun result => pure (result.charge 2 0))=_
  rw [NonceCopyProcedure.compact_copy_execute (source+32) (target+24) 64 _ siblingsReady (2+fuel) coins]
  change (((((execute nonceCompactImage (2+fuel) (nonceCompactSiblingsCopied state) coins)
    >>= fun result => pure (result.charge 385 0)) >>= fun result => pure (result.charge 3 0))
    >>= fun result => pure (result.charge 10 0)) >>= fun result => pure (result.charge 2 0))=_
  rw [nonce_compact_tail_execute _ siblingsPc fuel coins]
  simp only [bind_assoc, pure_bind, charges]
  rfl

end CommitGolfCandidate
