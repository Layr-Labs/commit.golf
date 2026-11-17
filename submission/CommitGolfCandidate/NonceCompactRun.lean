import CommitGolfCandidate.NonceCompactInputs
import CommitGolfCandidate.NonceCompactFinish

/-! Complete concrete compactor execution from its real entry to success.
The bounds concern actual memory windows; the original proof contents remain
arbitrary. The two footer cases retain their exact instruction charges. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

private theorem records_execute (base count : Nat) (state : MachineState)
    (ready : NonceCompactOuterReady base count count (nonceCompactEntryState state))
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (411*count+fuel) (nonceCompactEntryState state) coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactRecordsEnd state count) coins
          return result.charge (411*count) 0) :=
  nonce_compact_outer_execute base count count (nonceCompactEntryState state) ready fuel coins

theorem nonce_compact_run_empty_footer (state : MachineState) (base count : Nat)
    (pc : state.pc=4540) (small : count<2^64)
    (window : base+544*count ≤ MEMORY_BYTES) (aligned : base%8=0)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (oldEnd : state.getReg .x25=BitVec.ofNat 64 (base+544*count))
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (12+411*count+fuel) state coins=
      pure ⟨.success, nonceCompactExitState
        (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3),12+411*count,0⟩ := by
  have ready:=nonce_compact_entry_ready base count state pc small window aligned proofBase counter
  have finished:=nonce_compact_outer_finished base count count (nonceCompactEntryState state) ready
  have saved:=nonce_compact_records_saved state count
  have finish:=nonce_compact_finish_empty (nonceCompactRecordsEnd state count) finished.1
    (base+544*count) finished.2.1 (saved.1.trans oldEnd)
    (by norm_num [MEMORY_BYTES] at window; omega) fuel coins
  rw [show 12+411*count+fuel=5+(411*count+(7+fuel)) by omega,
    nonce_compact_entry_execute state pc (411*count+(7+fuel)) coins,
    records_execute base count state ready (7+fuel) coins, finish]
  simp [Execution.charge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

theorem nonce_compact_run_positive_footer (state : MachineState) (base count words : Nat)
    (pc : state.pc=4540) (small : count<2^64) (positive : 0 < words)
    (window : base+544*count+8*words ≤ MEMORY_BYTES) (aligned : base%8=0)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (oldEnd : state.getReg .x25=BitVec.ofNat 64 (base+544*count+8*words))
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (14+411*count+6*words+fuel) state coins=
      pure ⟨.success, nonceCompactExitState
        (nonceCopyReturned (nonceCompactFooterCall
          (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3)) words),
        14+411*count+6*words,0⟩ := by
  have ready:=nonce_compact_entry_ready base count state pc small (by omega) aligned proofBase counter
  have finished:=nonce_compact_outer_finished base count count (nonceCompactEntryState state) ready
  have saved:=nonce_compact_records_saved state count
  have footerReady:=nonce_compact_footer_ready state base count words pc small positive
    window aligned proofBase counter oldEnd
  have finish:=nonce_compact_finish_positive (nonceCompactRecordsEnd state count) finished.1
    (base+544*count) (base+536*count) words positive finished.2.1 (saved.1.trans oldEnd)
    (by norm_num [MEMORY_BYTES] at window; omega) footerReady fuel coins
  rw [show 14+411*count+6*words+fuel=5+(411*count+(9+6*words+fuel)) by omega,
    nonce_compact_entry_execute state pc (411*count+(9+6*words+fuel)) coins,
    records_execute base count state ready (9+6*words+fuel) coins, finish]
  simp [Execution.charge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;> omega

end CommitGolfCandidate
