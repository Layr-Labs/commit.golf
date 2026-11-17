import CommitGolfCandidate.NonceCompactTail

/-! The shared copy routine, still called by the footer, returns through x1.
Records are the straight-line blocks of `NonceCompactTail`. -/
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
    (ready : NonceCopyReady.Forward 5144 source target count count state) :
    (nonceCopyReturned state count).getReg .x23=BitVec.ofNat 64 (source+8*count) ∧
    (nonceCopyReturned state count).getReg .x25=BitVec.ofNat 64 (target+8*count) ∧
    (nonceCopyReturned state count).getReg .x28=0 := by
  have finished:=NonceCopyReady.forward_finished 5144 source target count count state ready
  simpa only [nonceCopyReturned, NonceCopyProcedure.return_register] using
    And.intro finished.2.2.1 (And.intro finished.2.2.2 finished.2.1)

end CommitGolfCandidate
