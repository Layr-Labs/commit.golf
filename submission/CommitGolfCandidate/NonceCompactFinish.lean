import CommitGolfCandidate.NonceCompactFooterControl

/-! Complete execution from the record-pass footer to the concrete success
halt. Empty footers skip the copy; positive footers pay its real call, loop
and return before reporting the reduced output length. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

private theorem copy_execute (source target count : Nat) (state : MachineState)
    (ready : NonceCopyReady.Forward 4620 source target count count state)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (6*count+1+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCopyReturned state count) coins
          return result.charge (6*count+1) 0) :=
  NonceCopyProcedure.compact_copy_execute source target count state ready fuel coins

theorem nonce_compact_finish_empty (state : MachineState) (pc : state.pc=4588)
    (source : Nat) (start : state.getReg .x23=BitVec.ofNat 64 source)
    (finish : state.getReg .x22=BitVec.ofNat 64 source) (small : source<2^64)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (7+fuel) state coins=
      pure ⟨.success, nonceCompactExitState (nonceCompactFooterPrefix state 3),7,0⟩ := by
  have footerPc : (nonceCompactFooterPrefix state 3).pc=4604 :=
    nonce_compact_footer_pc state pc source 0 start finish small
  rw [show 7+fuel=3+(4+fuel) by omega,
    nonce_compact_footer_execute state pc (4+fuel) coins,
    nonce_compact_exit _ footerPc fuel coins]
  simp [Execution.charge]

theorem nonce_compact_finish_positive (state : MachineState) (pc : state.pc=4588)
    (source target words : Nat) (positive : 0 < words)
    (start : state.getReg .x23=BitVec.ofNat 64 source)
    (finish : state.getReg .x22=BitVec.ofNat 64 (source+8*words))
    (small : source+8*words<2^64)
    (ready : NonceCopyReady.Forward 4620 source target words words
      (nonceCompactFooterCall (nonceCompactFooterPrefix state 3)))
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (9+6*words+fuel) state coins=
      pure ⟨.success, nonceCompactExitState
        (nonceCopyReturned (nonceCompactFooterCall (nonceCompactFooterPrefix state 3)) words),
        9+6*words,0⟩ := by
  have footerPc : (nonceCompactFooterPrefix state 3).pc=4600 := by
    have pcReady:=nonce_compact_footer_pc state pc source words start finish small
    simpa only [if_neg (by omega : words ≠ 0)] using pcReady
  have returnPc:=nonce_compact_footer_return_pc (nonceCompactFooterPrefix state 3) footerPc words
  rw [show 9+6*words+fuel=3+(1+(6*words+1+(4+fuel))) by omega,
    nonce_compact_footer_execute state pc (1+(6*words+1+(4+fuel))) coins,
    nonce_compact_footer_call_execute _ footerPc (6*words+1+(4+fuel)) coins,
    copy_execute source target words _ ready (4+fuel) coins,
    nonce_compact_exit _ returnPc fuel coins]
  simp [Execution.charge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

end CommitGolfCandidate
