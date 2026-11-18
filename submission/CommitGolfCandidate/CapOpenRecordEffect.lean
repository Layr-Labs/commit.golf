import CommitGolfCandidate.CapOpenRecordTail

/-! Effect of the record tail (call, group stub, latch) from the salt-field exit.
The cursor advances by 128 (salt field and three cell digests), x20 becomes the
group's heap node, x28 the fourteen-level path counter; memory changes only in
the record's digest field `[cursor + 32, cursor + 128)`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

theorem cap_open_record_tail_facts (state : MachineState) (position rootBase cursor : Nat)
    (pc : state.pc = 4256) (index : state.getReg .x20 = BitVec.ofNat 64 position)
    (positionBound : position < 2^24) (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (groups : state.getReg .x19 = BitVec.ofNat 64 4194304)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (separate : rootBase + 2^31 ≤ cursor) (bound : cursor + 160 ≤ 2^64) :
    (capOpenRecordTailState state).pc = 4280 ∧
    (capOpenRecordTailState state).getReg .x20 = BitVec.ofNat 64 (4194304 + position/4) ∧
    (capOpenRecordTailState state).getReg .x25 = BitVec.ofNat 64 (cursor + 128) ∧
    (capOpenRecordTailState state).getReg .x28 = 14 ∧
    (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x23 → reg ≠ .x30 → reg ≠ .x20 →
      reg ≠ .x25 → reg ≠ .x28 → (capOpenRecordTailState state).getReg reg = state.getReg reg) ∧
    (∀ k < 3, ∀ w < 4,
      (capOpenRecordTailState state).getMem (BitVec.ofNat 64 (cursor + 32 + 32*k + 8*w)) =
        state.getMem (BitVec.ofNat 64 (rootBase + 268435784 + 368*(position/4) +
          32*capStubPlace (position%4) k + 8*w))) ∧
    (∀ a < 2^64, (a < cursor + 32 ∨ cursor + 128 ≤ a) →
      (capOpenRecordTailState state).getMem (BitVec.ofNat 64 a) = state.getMem (BitVec.ofNat 64 a)) := by
  have call := cap_open_record_call_facts state pc
  have callPointer : (capOpenRecordCallState state).getReg .x25 = BitVec.ofNat 64 (cursor + 32) := by
    rw [call.2.2.1, pointer, show (32 : Word) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
  have callMem : (capOpenRecordCallState state).getMem = state.getMem := by
    funext query
    simp only [MachineState.getMem, call.2.2.2.1]
  have stub := cap_open_stub_facts (capOpenRecordCallState state) position rootBase (cursor+32)
    call.2.1 ((call.2.2.2.2 .x20 (by decide) (by decide)).trans index) positionBound
    ((call.2.2.2.2 .x9 (by decide) (by decide)).trans roots)
    ((call.2.2.2.2 .x19 (by decide) (by decide)).trans groups) callPointer (by omega) (by omega)
  have latchMem : (capOpenRecordTailState state).getMem =
      (capOpenStubState (capOpenRecordCallState state)).getMem := by
    funext query
    simp only [MachineState.getMem, capOpenRecordTailState, cap_open_record_latch_memory]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [capOpenRecordTailState, cap_open_record_latch_pc _ 4 (by decide), stub.1]
    rfl
  · rw [capOpenRecordTailState, cap_open_record_latch_register _ .x20 (by decide), stub.2.1,
      Nat.add_comm]
  · rw [capOpenRecordTailState, cap_open_record_latch_register _ .x25 (by decide), stub.2.2.1,
      Nat.add_assoc]
  · exact cap_open_record_latch_count _
  · intro reg h1 h6 h7 h23 h30 h20 h25 h28
    rw [capOpenRecordTailState, cap_open_record_latch_register _ reg h28,
      stub.2.2.2.1 reg h6 h7 h23 h30 h20 h25, call.2.2.2.2 reg h1 h25]
  · intro k hk w hw
    rw [latchMem, show cursor + 32 + 32*k + 8*w = (cursor+32) + 32*k + 8*w by omega,
      stub.2.2.2.2.1 k hk w hw, callMem]
  · intro a ha outside
    rw [latchMem, stub.2.2.2.2.2 a ha (by omega), callMem]

end CommitGolfCandidate
