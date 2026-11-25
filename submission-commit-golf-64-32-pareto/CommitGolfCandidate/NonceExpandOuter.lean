import CommitGolfCandidate.NonceExpandReady

/-! Counted backward expansion of every lower record. The terminal pointers
are one word before the proof base, and the next real PC is the register
restoration epilogue. No copy reads or writes those terminal pointers. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceExpandOuterReady (base count remaining : Nat) (state : MachineState) : Prop where
  remaining_le : remaining ≤ count
  count_bound : count<2^64
  base_start : 8 ≤ base
  window : base+544*count ≤ MEMORY_BYTES
  aligned : base%8=0
  pc : state.pc=if remaining=0 then 5048 else 5016
  source : state.getReg .x23=BitVec.ofNat 64 (base+536*remaining-8)
  target : state.getReg .x25=BitVec.ofNat 64 (base+544*remaining-8)
  counter : state.getReg .x24=BitVec.ofNat 64 remaining

theorem nonce_expand_outer_record_ready (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandOuterReady base count (remaining+1) state) :
    NonceExpandRecordReady base count (remaining+1) state :=
  ⟨by omega,ready.remaining_le,ready.count_bound,ready.base_start,ready.window,ready.aligned,
    by simpa using ready.pc,ready.source,ready.target,ready.counter⟩

theorem nonce_expand_outer_next (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandOuterReady base count (remaining+1) state) :
    NonceExpandOuterReady base count remaining (nonceExpandRecordState state) := by
  have recordReady:=nonce_expand_outer_record_ready base count remaining state ready
  have nonceReady:=nonce_expand_nonce_ready base count (remaining+1) state recordReady
  have copied:=nonce_backward_returned_finished _ _ 3 _ nonceReady
  have source : (nonceExpandNonceCopied state).getReg .x23=
      BitVec.ofNat 64 (base+536*remaining-8) := by
    change (nonceBackwardReturned (nonceExpandNonceCall state) 3).getReg .x23=_
    simpa only [Nat.add_sub_cancel] using copied.1
  have target : (nonceExpandNonceCopied state).getReg .x25=
      BitVec.ofNat 64 (base+544*remaining-8) := by
    change (nonceBackwardReturned (nonceExpandNonceCall state) 3).getReg .x25=_
    simpa only [Nat.add_sub_cancel] using copied.2.1
  have outer : (nonceExpandNonceCopied state).getReg .x24=BitVec.ofNat 64 (remaining+1) :=
    (nonce_expand_outer_counter state).trans ready.counter
  have remainingLe:=ready.remaining_le
  have countBound:=ready.count_bound
  refine ⟨by omega,ready.count_bound,ready.base_start,ready.window,ready.aligned,?_,?_,?_,?_⟩
  · have pc:=nonce_expand_tail_pc (nonceExpandNonceCopied state) remaining
      (nonce_expand_nonce_return_pc state recordReady.pc) (by omega) outer
    exact pc
  · change (nonceExpandTailState (nonceExpandNonceCopied state)).getReg .x23=_
    rw [nonce_expand_tail_register _ .x23 (by decide)]
    exact source
  · change (nonceExpandTailState (nonceExpandNonceCopied state)).getReg .x25=_
    rw [nonce_expand_tail_register _ .x25 (by decide)]
    exact target
  · exact nonce_expand_tail_counter _ remaining (by omega) outer

theorem nonce_expand_outer_execute (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandOuterReady base count remaining state) (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (412*remaining+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel
            (capCountedRun nonceExpandRecordState remaining state) coins
          return result.charge (412*remaining) 0) := by
  refine cap_counted_run_execute nonceExpandedImage 412 nonceExpandRecordState
    (NonceExpandOuterReady base count)
    (fun remaining current => nonce_expand_outer_next base count remaining current)
    ?_ remaining state ready fuel coins
  intro remaining current currentReady extra allowCoins
  have recordReady:=nonce_expand_outer_record_ready base count remaining current currentReady
  exact nonce_expand_record_execute current recordReady.pc (base+536*remaining) (base+544*remaining)
    (by simpa only [Nat.add_sub_cancel] using nonce_expand_siblings_ready base count (remaining+1) current recordReady)
    (nonce_expand_padding_valid base count (remaining+1) current recordReady)
    (by simpa only [Nat.add_sub_cancel] using nonce_expand_nonce_ready base count (remaining+1) current recordReady)
    extra allowCoins

theorem nonce_expand_outer_finished (base count remaining : Nat) (state : MachineState)
    (ready : NonceExpandOuterReady base count remaining state) :
    let final := capCountedRun nonceExpandRecordState remaining state
    final.pc=5048 ∧ final.getReg .x23=BitVec.ofNat 64 (base-8) ∧
      final.getReg .x25=BitVec.ofNat 64 (base-8) ∧ final.getReg .x24=0 := by
  have final:=cap_counted_run_ready nonceExpandRecordState (NonceExpandOuterReady base count)
    (fun remaining current => nonce_expand_outer_next base count remaining current)
    remaining state ready
  exact ⟨by simpa using final.pc,by simpa using final.source,
    by simpa using final.target,by simpa using final.counter⟩

theorem nonce_expand_outer_register (state : MachineState) (count : Nat) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (capCountedRun nonceExpandRecordState count state).getReg reg=state.getReg reg := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [capCountedRun,ih,nonce_expand_record_register state reg outside]

end CommitGolfCandidate
