import CommitGolfCandidate.NonceCompactEntry
import CommitGolfCandidate.NonceCompactFrame
import CommitGolfCandidate.NonceCompactFooterControl

/-! Stable ABI inputs and saved endpoint through the concrete record pass.
These facts initialize the final footer move without assumptions on the
contents of the proof or trapdoor memory. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_compact_entry_saved (state : MachineState) :
    (nonceCompactEntryState state).getReg .x22=state.getReg .x25 ∧
    (nonceCompactEntryState state).getReg .x15=state.getReg .x15 := by
  constructor
  · rw [nonceCompactEntryState, nonce_compact_guard_register]
    exact (nonce_compact_header_registers state).1
  · rw [nonceCompactEntryState, nonce_compact_guard_register]
    rfl

def nonceCompactRecordsEnd (state : MachineState) (count : Nat) : MachineState :=
  capCountedRun nonceCompactRecordState count (nonceCompactEntryState state)

theorem nonce_compact_records_saved (state : MachineState) (count : Nat) :
    (nonceCompactRecordsEnd state count).getReg .x22=state.getReg .x25 ∧
    (nonceCompactRecordsEnd state count).getReg .x15=state.getReg .x15 := by
  constructor
  · rw [nonceCompactRecordsEnd, nonce_compact_outer_register _ _ .x22 (by decide)]
    exact (nonce_compact_entry_saved state).1
  · rw [nonceCompactRecordsEnd, nonce_compact_outer_register _ _ .x15 (by decide)]
    exact (nonce_compact_entry_saved state).2

theorem nonce_compact_footer_ready (state : MachineState) (base count words : Nat)
    (pc : state.pc=4540) (small : count<2^64) (positive : 0 < words)
    (window : base+544*count+8*words ≤ MEMORY_BYTES) (aligned : base%8=0)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (oldEnd : state.getReg .x25=BitVec.ofNat 64 (base+544*count+8*words)) :
    NonceCopyReady.Forward 5144 (base+544*count) (base+536*count) words words
      (nonceCompactFooterCall (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3)) := by
  have entryReady:=nonce_compact_entry_ready base count state pc small (by omega) aligned proofBase counter
  have records:=nonce_compact_outer_finished base count count (nonceCompactEntryState state) entryReady
  have saved:=nonce_compact_records_saved state count
  have footerPc:=nonce_compact_footer_pc (nonceCompactRecordsEnd state count) records.1
    (base+544*count) words records.2.1 (saved.1.trans oldEnd) (by
      norm_num [MEMORY_BYTES] at window
      omega)
  have footerCounter:=nonce_compact_footer_counter (nonceCompactRecordsEnd state count)
    (base+544*count) words records.2.1 (saved.1.trans oldEnd) (by
      norm_num [MEMORY_BYTES] at window
      omega)
  have callPc : (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3).pc=5124 := by
    simpa only [if_neg (by omega : words ≠ 0)] using footerPc
  have control:=nonce_compact_footer_call_pc _ callPc
  refine ⟨by omega,?_,by omega,window,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · norm_num [MEMORY_BYTES] at window
    omega
  · rw [nonce_compact_footer_call_register _ .x28 (by decide)]
    exact footerCounter
  · simpa only [if_neg (by omega : words ≠ 0)] using control.1
  · rw [nonce_compact_footer_call_register _ .x23 (by decide),
      nonce_compact_footer_register _ .x23 (by decide)]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact records.2.1
  · rw [nonce_compact_footer_call_register _ .x25 (by decide),
      nonce_compact_footer_register _ .x25 (by decide)]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact records.2.2.1

end CommitGolfCandidate
