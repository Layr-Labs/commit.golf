import CommitGolfCandidate.NonceExpandFooterControl

/-! Actual optional footer-copy and record-entry readiness. Alignment plus
the minimum length turns the footer division into an exact decomposition of
the packed proof, and the expanded window admits every backward access. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] nonceExpandHeaderPrefix nonceExpandMinimumPrefix
  nonceExpandCapacityPrefix nonceExpandFooterPrefix nonceBackwardReturned

abbrev nonceExpandFooterWords (count length : Nat) : Nat := (length-536*count)/8

def nonceExpandAfterFooter (state : MachineState) (words : Nat) : MachineState :=
  if words=0 then state else nonceBackwardReturned (nonceExpandFooterCall state) words

def nonceExpandRecordEntry (state : MachineState) (words : Nat) : MachineState :=
  nonceExpandGuardState (nonceExpandAfterFooter state words)

theorem nonce_expand_footer_ready (state : MachineState) (base count length : Nat)
    (facts : NonceExpandSetupFacts base count length state) (baseStart : 8 ≤ base)
    (baseAligned : base%8=0) (aligned : length%8=0) (enough : 536*count ≤ length)
    (window : base+length+8*count ≤ MEMORY_BYTES) (positive : 0 < nonceExpandFooterWords count length) :
    NonceBackwardReady.Backward 5096 (base+536*count) (base+544*count)
      (nonceExpandFooterWords count length) (nonceExpandFooterWords count length)
      (nonceExpandFooterCall (nonceExpandSetupState state)) := by
  have lengthEq : length=536*count+8*nonceExpandFooterWords count length := by
    dsimp only [nonceExpandFooterWords]
    omega
  have callPc : (nonceExpandSetupState state).pc=5008 := by
    simpa only [if_neg (by omega : (length-536*count)/8 ≠ 0)] using facts.pc
  have control:=nonce_expand_footer_call_pc _ callPc
  refine ⟨by omega,?_,by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · have bound:=window
    norm_num [MEMORY_BYTES] at bound
    dsimp only [nonceExpandFooterWords]
    omega
  · rw [nonce_expand_footer_call_register _ .x28 (by decide)]
    exact facts.words
  · simpa only [if_neg (by omega : nonceExpandFooterWords count length ≠ 0)] using control.1
  · rw [nonce_expand_footer_call_register _ .x23 (by decide),facts.source]
    congr 1
    omega
  · rw [nonce_expand_footer_call_register _ .x25 (by decide),facts.target]
    congr 1
    omega

theorem nonce_expand_after_footer_control (state : MachineState) (base count length : Nat)
    (facts : NonceExpandSetupFacts base count length state) (baseStart : 8 ≤ base)
    (baseAligned : base%8=0) (aligned : length%8=0) (enough : 536*count ≤ length)
    (window : base+length+8*count ≤ MEMORY_BYTES) :
    let final := nonceExpandAfterFooter (nonceExpandSetupState state) (nonceExpandFooterWords count length)
    final.pc=5012 ∧ final.getReg .x23=BitVec.ofNat 64 (base+536*count-8) ∧
    final.getReg .x25=BitVec.ofNat 64 (base+544*count-8) ∧ final.getReg .x24=BitVec.ofNat 64 count := by
  have lengthEq : length=536*count+8*nonceExpandFooterWords count length := by
    dsimp only [nonceExpandFooterWords]
    omega
  by_cases empty : nonceExpandFooterWords count length=0
  · simp only [nonceExpandAfterFooter,if_pos empty]
    have noFooter : length=536*count := by omega
    refine ⟨?_,?_,?_,facts.counter⟩
    · simpa only [if_pos empty] using facts.pc
    · exact facts.source.trans (congrArg (BitVec.ofNat 64) (by omega))
    · exact facts.target.trans (congrArg (BitVec.ofNat 64) (by omega))
  · simp only [nonceExpandAfterFooter,if_neg empty]
    have ready:=nonce_expand_footer_ready state base count length facts baseStart baseAligned aligned enough window (by omega)
    have copied:=nonce_backward_returned_finished _ _ _ _ ready
    have callPc : (nonceExpandSetupState state).pc=5008 := by simpa only [if_neg empty] using facts.pc
    refine ⟨nonce_expand_footer_return_pc _ callPc _,copied.1,copied.2.1,?_⟩
    rw [nonce_backward_returned_register _ _ .x24 (by decide),
      nonce_expand_footer_call_register _ .x24 (by decide)]
    exact facts.counter

theorem nonce_expand_record_entry_ready (state : MachineState) (base count length : Nat)
    (facts : NonceExpandSetupFacts base count length state) (baseStart : 8 ≤ base) (countSmall : count<2^64)
    (baseAligned : base%8=0) (aligned : length%8=0) (enough : 536*count ≤ length)
    (window : base+length+8*count ≤ MEMORY_BYTES) :
    NonceExpandOuterReady base count count
      (nonceExpandRecordEntry (nonceExpandSetupState state) (nonceExpandFooterWords count length)) := by
  have footer:=nonce_expand_after_footer_control state base count length facts baseStart baseAligned aligned enough window
  refine ⟨by omega,countSmall,baseStart,by omega,baseAligned,?_,?_,?_,?_⟩
  · exact nonce_expand_guard_pc _ footer.1 count countSmall footer.2.2.2
  · change (nonceExpandGuardState _).getReg .x23=_
    rw [nonce_expand_guard_register]
    exact footer.2.1
  · change (nonceExpandGuardState _).getReg .x25=_
    rw [nonce_expand_guard_register]
    exact footer.2.2.1
  · change (nonceExpandGuardState _).getReg .x24=_
    rw [nonce_expand_guard_register]
    exact footer.2.2.2

end CommitGolfCandidate
