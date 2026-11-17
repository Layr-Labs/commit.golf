import CommitGolfCandidate.NonceExpandPointers

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceExpandRecordReady (base count remaining : Nat) (state : MachineState) : Prop where
  positive : 0 < remaining
  remaining_le : remaining ≤ count
  count_bound : count<2^64
  base_start : 8 ≤ base
  window : base+544*count ≤ MEMORY_BYTES
  aligned : base%8=0
  pc : state.pc=5016
  source : state.getReg .x23=BitVec.ofNat 64 (base+536*remaining-8)
  target : state.getReg .x25=BitVec.ofNat 64 (base+544*remaining-8)
  counter : state.getReg .x24=BitVec.ofNat 64 remaining

theorem nonce_expand_siblings_ready (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandRecordReady base count remaining state) :
    NonceBackwardReady.Backward 5096 (base+536*(remaining-1)+24)
      (base+544*(remaining-1)+32) 64 64 (nonceExpandSiblingCall state) := by
  have control:=nonce_expand_call_control false state ready.pc
  have remainingLe:=ready.remaining_le
  have positive:=ready.positive
  have baseStart:=ready.base_start
  have window:=ready.window
  have aligned:=ready.aligned
  refine ⟨by omega,by decide,by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · exact control.2.1
  · exact control.1
  · change (nonceExpandCallPrefix false state (nonceExpandCallCount false)).getReg .x23=_
    rw [nonce_expand_call_register false state .x23 (by decide),ready.source]
    congr 1
    omega
  · change (nonceExpandCallPrefix false state (nonceExpandCallCount false)).getReg .x25=_
    have kept : (nonceExpandCallPrefix false state (nonceExpandCallCount false)).getReg .x25=state.getReg .x25 := by
      simpa only [Bool.false_eq_true,ite_false] using nonce_expand_call_target false state
    rw [kept,ready.target]
    congr 1
    omega

theorem nonce_expand_padding_valid (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandRecordReady base count remaining state) :
    accessValid ((nonceExpandSiblingsCopied state).getReg .x25) 8=true := by
  have siblingsReady:=nonce_expand_siblings_ready base count remaining state ready
  have copied:=nonce_backward_returned_finished _ _ 64 _ siblingsReady
  have target : (nonceExpandSiblingsCopied state).getReg .x25=
      BitVec.ofNat 64 (base+544*(remaining-1)+24) := copied.2.1
  have window:=ready.window
  have remainingLe:=ready.remaining_le
  have positive:=ready.positive
  have aligned:=ready.aligned
  have small : base+544*(remaining-1)+24<2^64 := by
    norm_num [MEMORY_BYTES] at window
    omega
  rw [target]
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨by omega,by omega⟩

theorem nonce_expand_nonce_ready (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandRecordReady base count remaining state) :
    NonceBackwardReady.Backward 5096 (base+536*(remaining-1))
      (base+544*(remaining-1)) 3 3 (nonceExpandNonceCall state) := by
  have siblingsReady:=nonce_expand_siblings_ready base count remaining state ready
  have copied:=nonce_backward_returned_finished _ _ 64 _ siblingsReady
  have siblingPc:=nonce_expand_sibling_return_pc state ready.pc
  have control:=nonce_expand_call_control true (nonceExpandSiblingsCopied state) siblingPc
  have remainingLe:=ready.remaining_le
  have positive:=ready.positive
  have baseStart:=ready.base_start
  have window:=ready.window
  have aligned:=ready.aligned
  refine ⟨by omega,by decide,by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · exact control.2.1
  · exact control.1
  · change (nonceExpandCallPrefix true (nonceExpandSiblingsCopied state)
      (nonceExpandCallCount true)).getReg .x23=_
    rw [nonce_expand_call_register true _ .x23 (by decide)]
    exact copied.1
  · change (nonceExpandCallPrefix true (nonceExpandSiblingsCopied state)
      (nonceExpandCallCount true)).getReg .x25=_
    rw [nonce_expand_call_target]
    have target : (nonceExpandSiblingsCopied state).getReg .x25=
        BitVec.ofNat 64 (base+544*(remaining-1)+32-8) := copied.2.1
    rw [target,NonceBackwardReady.decrement_eight _ (by omega)]
    congr 1

end CommitGolfCandidate
