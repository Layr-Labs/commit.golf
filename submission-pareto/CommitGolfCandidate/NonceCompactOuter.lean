import CommitGolfCandidate.NonceCompactReady

/-! Counted execution of all lower records in the actual compactor. Buffer
readiness advances with each real iteration, including its final branch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceCompactOuterReady (base count remaining : Nat) (state : MachineState) : Prop where
  remaining_le : remaining ≤ count
  count_bound : count < 2^64
  window : base+544*count ≤ MEMORY_BYTES
  aligned : base%8=0
  pc : state.pc=if remaining=0 then 4588 else 4560
  source : state.getReg .x23=BitVec.ofNat 64 (base+544*(count-remaining))
  target : state.getReg .x25=BitVec.ofNat 64 (base+536*(count-remaining))
  counter : state.getReg .x24=BitVec.ofNat 64 remaining

theorem nonce_compact_outer_record_ready (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactOuterReady base count (remaining+1) state) :
    NonceCompactRecordReady base count (remaining+1) state :=
  ⟨by omega, ready.remaining_le, ready.count_bound, ready.window, ready.aligned,
    by simpa using ready.pc, ready.source, ready.target, ready.counter⟩

theorem nonce_compact_outer_next (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactOuterReady base count (remaining+1) state) :
    NonceCompactOuterReady base count remaining (nonceCompactRecordState state) := by
  have recordReady:=nonce_compact_outer_record_ready base count remaining state ready
  have effects:=nonce_compact_record_effects base count (remaining+1) state recordReady
  have remainingLe:=ready.remaining_le
  have progress : count-(remaining+1)+1=count-remaining := by omega
  refine ⟨by omega,ready.count_bound,ready.window,ready.aligned,?_,?_,?_,?_⟩
  · have last : remaining+1=1 ↔ remaining=0 := by omega
    simpa only [last] using effects.2.2.2
  · simpa only [progress] using effects.1
  · simpa only [progress] using effects.2.1
  · simpa only [Nat.add_sub_cancel] using effects.2.2.1

theorem nonce_compact_outer_execute (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactOuterReady base count remaining state) (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (402*remaining+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel
            (capCountedRun nonceCompactRecordState remaining state) coins
          return result.charge (402*remaining) 0) := by
  refine cap_counted_run_execute nonceCompactImage 402 nonceCompactRecordState
    (NonceCompactOuterReady base count)
    (fun remaining current => nonce_compact_outer_next base count remaining current)
    ?_ remaining state ready fuel coins
  intro remaining current currentReady extra allowCoins
  have recordReady:=nonce_compact_outer_record_ready base count remaining current currentReady
  exact nonce_compact_record_execute current recordReady.pc
    (base+544*(count-(remaining+1))) (base+536*(count-(remaining+1)))
    (nonce_compact_nonce_ready base count (remaining+1) current recordReady)
    (nonce_compact_siblings_ready base count (remaining+1) current recordReady) extra allowCoins

theorem nonce_compact_outer_finished (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactOuterReady base count remaining state) :
    let final := capCountedRun nonceCompactRecordState remaining state
    final.pc=4588 ∧ final.getReg .x23=BitVec.ofNat 64 (base+544*count) ∧
    final.getReg .x25=BitVec.ofNat 64 (base+536*count) ∧ final.getReg .x24=0 := by
  have final:=cap_counted_run_ready nonceCompactRecordState (NonceCompactOuterReady base count)
    (fun remaining current => nonce_compact_outer_next base count remaining current)
    remaining state ready
  exact ⟨by simpa using final.pc, by simpa using final.source,
    by simpa using final.target, by simpa using final.counter⟩

end CommitGolfCandidate
