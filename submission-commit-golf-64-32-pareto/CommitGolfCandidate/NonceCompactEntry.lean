import CommitGolfCandidate.NonceCompactGuard

/-! Composition of the real entry moves and guard. All record-loop pointers
are initialized from the original ABI proof base, including an empty batch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCompactEntryState (state : MachineState) : MachineState :=
  nonceCompactGuardState (nonceCompactHeaderPrefix state 4)

theorem nonce_compact_entry_execute (state : MachineState) (pc : state.pc=4540)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (5+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactEntryState state) coins
          return result.charge 5 0) := by
  have guardPc : (nonceCompactHeaderPrefix state 4).pc=4556 := by
    rw [nonce_compact_header_pc state 4 (by decide), pc]
    rfl
  rw [show 5+fuel=4+(1+fuel) by omega,
    nonce_compact_header_execute state pc (1+fuel) coins,
    nonce_compact_guard_execute _ guardPc fuel coins]
  simp [Execution.charge, bind_assoc, ← Nat.add_assoc, nonceCompactEntryState]

theorem nonce_compact_entry_memory (state : MachineState) :
    (nonceCompactEntryState state).mem=state.mem := by
  rw [nonceCompactEntryState, nonce_compact_guard_memory, nonce_compact_header_memory]

theorem nonce_compact_entry_ready (base count : Nat) (state : MachineState)
    (pc : state.pc=4540) (small : count<2^64) (window : base+544*count ≤ MEMORY_BYTES)
    (aligned : base%8=0) (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count) :
    NonceCompactOuterReady base count count (nonceCompactEntryState state) := by
  have header:=nonce_compact_header_registers state
  have guardPc : (nonceCompactHeaderPrefix state 4).pc=4556 := by
    rw [nonce_compact_header_pc state 4 (by decide), pc]
    rfl
  have headerCounter : (nonceCompactHeaderPrefix state 4).getReg .x24=BitVec.ofNat 64 count :=
    header.2.2.2.trans counter
  refine ⟨by omega,small,window,aligned,?_,?_,?_,?_⟩
  · exact nonce_compact_guard_pc _ guardPc count small headerCounter
  · change (nonceCompactGuardState (nonceCompactHeaderPrefix state 4)).getReg .x23=_
    rw [nonce_compact_guard_register, header.2.1, proofBase]
    simp
  · change (nonceCompactGuardState (nonceCompactHeaderPrefix state 4)).getReg .x25=_
    rw [nonce_compact_guard_register, header.2.2.1, proofBase]
    simp
  · change (nonceCompactGuardState (nonceCompactHeaderPrefix state 4)).getReg .x24=_
    rw [nonce_compact_guard_register]
    exact headerCounter

end CommitGolfCandidate
