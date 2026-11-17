import CommitGolfCandidate.NonceCompactRecord

/-! Buffer and pointer obligations for a concrete compacting record. Each
iteration consumes 544 source bytes and emits 536 bytes at a lower address. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceCompactRecordReady (base count remaining : Nat) (state : MachineState) : Prop where
  positive : 0 < remaining
  remaining_le : remaining ≤ count
  count_bound : count < 2^64
  window : base+544*count ≤ MEMORY_BYTES
  aligned : base%8=0
  pc : state.pc=4560
  source : state.getReg .x23=BitVec.ofNat 64 (base+544*(count-remaining))
  target : state.getReg .x25=BitVec.ofNat 64 (base+536*(count-remaining))
  counter : state.getReg .x24=BitVec.ofNat 64 remaining

theorem nonce_compact_nonce_ready (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    NonceCopyReady.Forward 4620 (base+544*(count-remaining))
      (base+536*(count-remaining)) 3 3 (nonceCompactNonceCall state) := by
  have control:=nonce_compact_call_control false state ready.pc
  refine ⟨by omega, by decide, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have window:=ready.window
    have bound:=ready.remaining_le
    have positive:=ready.positive
    omega
  · have window:=ready.window
    have bound:=ready.remaining_le
    have positive:=ready.positive
    omega
  · have aligned:=ready.aligned
    omega
  · have aligned:=ready.aligned
    omega
  · exact control.2.1
  · exact control.1
  · change (nonceCompactCallPrefix false state (nonceCompactCallCount false)).getReg .x23=_
    rw [nonce_compact_call_source, ready.source]
    simp
  · change (nonceCompactCallPrefix false state (nonceCompactCallCount false)).getReg .x25=_
    rw [nonce_compact_call_register false state .x25 (by decide), ready.target]
    simp

theorem nonce_compact_siblings_ready (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    NonceCopyReady.Forward 4620 (base+544*(count-remaining)+32)
      (base+536*(count-remaining)+24) 64 64 (nonceCompactSiblingCall state) := by
  have nonceReady:=nonce_compact_nonce_ready base count remaining state ready
  have copied:=nonce_copy_returned_finished _ _ 3 _ nonceReady
  have returned:=nonce_compact_nonce_return_pc state ready.pc
  have control:=nonce_compact_call_control true (nonceCompactNonceCopied state) returned
  refine ⟨by omega, by decide, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have window:=ready.window
    have bound:=ready.remaining_le
    have positive:=ready.positive
    omega
  · have window:=ready.window
    have bound:=ready.remaining_le
    have positive:=ready.positive
    omega
  · have aligned:=ready.aligned
    omega
  · have aligned:=ready.aligned
    omega
  · exact control.2.1
  · exact control.1
  · change (nonceCompactCallPrefix true (nonceCompactNonceCopied state)
      (nonceCompactCallCount true)).getReg .x23=_
    rw [nonce_compact_call_source]
    have source : (nonceCompactNonceCopied state).getReg .x23=
        BitVec.ofNat 64 (base+544*(count-remaining)+8*3) := copied.1
    rw [source]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    change BitVec.ofNat 64 (base+544*(count-remaining)+8*3)+BitVec.ofNat 64 8=_
    rw [← BitVec.ofNat_add]
  · change (nonceCompactCallPrefix true (nonceCompactNonceCopied state)
      (nonceCompactCallCount true)).getReg .x25=_
    rw [nonce_compact_call_register true _ .x25 (by decide)]
    change (nonceCompactNonceCopied state).getReg .x25=_
    exact copied.2.1

theorem nonce_compact_record_effects (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    let final := nonceCompactRecordState state
    final.getReg .x23=BitVec.ofNat 64 (base+544*(count-remaining+1)) ∧
    final.getReg .x25=BitVec.ofNat 64 (base+536*(count-remaining+1)) ∧
    final.getReg .x24=BitVec.ofNat 64 (remaining-1) ∧
    final.pc=(if remaining=1 then 4588 else 4560) := by
  have siblingsReady:=nonce_compact_siblings_ready base count remaining state ready
  have copied:=nonce_copy_returned_finished _ _ 64 _ siblingsReady
  have copiedSource : (nonceCompactSiblingsCopied state).getReg .x23=
      BitVec.ofNat 64 (base+544*(count-remaining)+32+8*64) := copied.1
  have copiedTarget : (nonceCompactSiblingsCopied state).getReg .x25=
      BitVec.ofNat 64 (base+536*(count-remaining)+24+8*64) := copied.2.1
  have outer : (nonceCompactSiblingsCopied state).getReg .x24=BitVec.ofNat 64 remaining :=
    (nonce_compact_record_outer_counter state).trans ready.counter
  have positive:=ready.positive
  have remainingLe:=ready.remaining_le
  have countBound:=ready.count_bound
  have decrement : remaining-1+1=remaining := by omega
  have counterAfter:=nonce_compact_tail_counter (nonceCompactSiblingsCopied state) (remaining-1)
    (by omega) (by simpa only [decrement] using outer)
  have pcAfter:=nonce_compact_tail_pc (nonceCompactSiblingsCopied state) (remaining-1)
    (nonce_compact_sibling_return_pc state ready.pc) (by omega)
    (by simpa only [decrement] using outer)
  refine ⟨?_,?_,counterAfter,?_⟩
  · change (nonceCompactTailState (nonceCompactSiblingsCopied state)).getReg .x23=_
    rw [nonce_compact_tail_register _ .x23 (by decide), copiedSource]
    congr 1
  · change (nonceCompactTailState (nonceCompactSiblingsCopied state)).getReg .x25=_
    rw [nonce_compact_tail_register _ .x25 (by decide), copiedTarget]
    congr 1
  · have last : remaining-1=0 ↔ remaining=1 := by omega
    change (nonceCompactTailState (nonceCompactSiblingsCopied state)).pc=_
    simpa only [last] using pcAfter

end CommitGolfCandidate
