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

theorem nonce_compact_record_window (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    NonceRecordWindow (base+544*(count-remaining)) (base+536*(count-remaining)) state := by
  have window:=ready.window
  have bound:=ready.remaining_le
  have positive:=ready.positive
  have aligned:=ready.aligned
  refine ⟨by omega, ?_, by omega, by omega, ready.source, ready.target⟩
  have step : 544*(count-remaining)+544 ≤ 544*count := by
    have : count-remaining+1 ≤ count := by omega
    calc 544*(count-remaining)+544=544*(count-remaining+1) := by ring
      _ ≤ 544*count := Nat.mul_le_mul_left 544 this
  omega

theorem nonce_compact_record_execute (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (138+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactRecordState state) coins
          return result.charge 138 0) :=
  nonce_compact_record_block_execute _ _ state ready.pc
    (nonce_compact_record_window base count remaining state ready) fuel coins

theorem nonce_compact_record_effects (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    let final := nonceCompactRecordState state
    final.getReg .x23=BitVec.ofNat 64 (base+544*(count-remaining+1)) ∧
    final.getReg .x25=BitVec.ofNat 64 (base+536*(count-remaining+1)) ∧
    final.getReg .x24=BitVec.ofNat 64 (remaining-1) ∧
    final.pc=(if remaining=1 then 5112 else 4560) := by
  let pairs := nonceRecordPairs state 67
  have sourceReg : pairs.getReg .x23=BitVec.ofNat 64 (base+544*(count-remaining)) :=
    (nonce_record_pairs_register state 67 .x23 (by decide)).trans ready.source
  have targetReg : pairs.getReg .x25=BitVec.ofNat 64 (base+536*(count-remaining)) :=
    (nonce_record_pairs_register state 67 .x25 (by decide)).trans ready.target
  have counterReg : pairs.getReg .x24=BitVec.ofNat 64 remaining :=
    (nonce_record_pairs_register state 67 .x24 (by decide)).trans ready.counter
  have pairsPc : pairs.pc=4560+BitVec.ofNat 64 (8*67) := by
    rw [nonce_record_pairs_pc, ready.pc]
  have positive:=ready.positive
  have remainingLe:=ready.remaining_le
  have countBound:=ready.count_bound
  have adds:=nonce_record_tail_adds pairs
  have decremented : (nonceRecordTailAdds pairs).getReg .x24=BitVec.ofNat 64 (remaining-1) := by
    rw [adds.2.2.1, counterReg]
    have equation : remaining=remaining-1+1 := by omega
    conv_lhs => rw [equation]
    exact NonceWordCopy.decrement (remaining-1+1) (by omega)
  have zero : (BitVec.ofNat 64 (remaining-1) : Word)=0 ↔ remaining=1 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : remaining-1<2^64)] at numeric
      change remaining-1=0 at numeric
      omega
    · intro one
      rw [one]
      rfl
  refine ⟨?_,?_,?_,?_⟩
  · change (nonceRecordTailState pairs).getReg .x23=_
    rw [nonce_record_tail_state_register, adds.1, sourceReg,
      show signExtend12 (544 : BitVec 12)=BitVec.ofNat 64 544 from by decide, ← BitVec.ofNat_add]
    congr 1
  · change (nonceRecordTailState pairs).getReg .x25=_
    rw [nonce_record_tail_state_register, adds.2.1, targetReg,
      show signExtend12 (536 : BitVec 12)=BitVec.ofNat 64 536 from by decide, ← BitVec.ofNat_add]
    congr 1
  · change (nonceRecordTailState pairs).getReg .x24=_
    rw [nonce_record_tail_state_register]
    exact decremented
  · change (nonceRecordTailState pairs).pc=_
    rw [nonce_record_tail_state_pc, decremented, adds.2.2.2.1, pairsPc]
    by_cases last : remaining=1
    · rw [if_pos (zero.mpr last), if_pos last]
      decide
    · rw [if_neg (by rw [zero]; exact last), if_neg last]
      decide

end CommitGolfCandidate
