import CommitGolfCandidate.CapOpenRecordEffect
import CommitGolfCandidate.CapOpenPathLoop

/-! Checked record entry through its salt field, the group stub and lower-path
setup. The loaded position is related to the ABI separately. Every nonce,
cell and output access is admitted here, and the fourteen-step loop readiness
uses actual register projections. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- Facts at a record entry (pc 4212): register values, the loaded position, the
trapdoor below the output cursor and room for the record's 576 bytes. -/
structure CapOpenRecordAt (rootBase saltBase cursor limit position : Nat)
    (state : MachineState) : Prop where
  pc : state.pc = 4212
  roots : state.getReg .x9 = BitVec.ofNat 64 rootBase
  salts : state.getReg .x18 = BitVec.ofNat 64 saltBase
  pointer : state.getReg .x25 = BitVec.ofNat 64 cursor
  loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position
  indexValid : accessValid (state.getReg .x24) 8 = true
  positionBound : position < 16777216
  leaves : state.getReg .x19 = 4194304
  marks : state.getReg .x22 = 28672
  stride : state.getReg .x17 = 16
  rootAligned : rootBase % 8 = 0
  saltAligned : saltBase % 8 = 0
  cursorAligned : cursor % 8 = 0
  heapBelow : rootBase + 2^31 ≤ cursor
  saltBelow : saltBase + 16*position + 32 ≤ cursor
  high : 32800 ≤ cursor
  space : cursor + 576 ≤ limit
  limitBound : limit ≤ MEMORY_BYTES

def capOpenSaltedState (state : MachineState) : MachineState :=
  capNonceEightState (capOpenRecordPrefix state 3)

def capOpenRecordPathState (state : MachineState) : MachineState :=
  capOpenRecordTailState (capOpenSaltedState state)

theorem cap_open_record_at_small {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    cursor + 576 < 2^64 := by
  have := entry.space
  have := entry.limitBound
  simp only [MEMORY_BYTES] at *
  omega

theorem cap_open_record_salted_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x20 ∧ reg ≠ .x23) :
    (capOpenSaltedState state).getReg reg = state.getReg reg := by
  rw [capOpenSaltedState]
  exact (cap_nonce_eight_register _ reg outside.1).trans
    (cap_open_record_prepare_register state 3 (by decide) reg
      ⟨outside.2.1, outside.1, outside.2.2⟩)

theorem cap_open_record_salted_index (state : MachineState) (position : Nat)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position) :
    (capOpenSaltedState state).getReg .x20 = BitVec.ofNat 64 position := by
  rw [capOpenSaltedState, cap_nonce_eight_register _ .x20 (by decide), cap_open_record_index, loaded]

theorem cap_open_record_salted_pc (state : MachineState) (pc : state.pc = 4212) :
    (capOpenSaltedState state).pc = 4256 := by
  rw [capOpenSaltedState, cap_nonce_eight_pc, cap_open_record_prepare_pc state 3 (by decide), pc]
  rfl

theorem cap_open_record_salted_mem (state : MachineState) :
    (capOpenSaltedState state).getMem = (capNonceEightState (capOpenRecordPrefix state 3)).getMem := rfl

/-- Everything the record knows after its tail, relative to the salt-field exit. -/
theorem cap_open_record_path_facts {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordPathState state).pc = 4280 ∧
    (capOpenRecordPathState state).getReg .x20 = BitVec.ofNat 64 (4194304 + position/4) ∧
    (capOpenRecordPathState state).getReg .x25 = BitVec.ofNat 64 (cursor + 128) ∧
    (capOpenRecordPathState state).getReg .x28 = 14 ∧
    (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x23 → reg ≠ .x30 → reg ≠ .x20 →
      reg ≠ .x25 → reg ≠ .x28 → (capOpenRecordPathState state).getReg reg = state.getReg reg) ∧
    (∀ k < 3, ∀ w < 4,
      (capOpenRecordPathState state).getMem (BitVec.ofNat 64 (cursor + 32 + 32*k + 8*w)) =
        state.getMem (BitVec.ofNat 64 (rootBase + 268435784 + 368*(position/4) +
          32*capStubPlace (position%4) k + 8*w))) ∧
    (∀ a < 2^64, (a < cursor + 32 ∨ cursor + 128 ≤ a) →
      (capOpenRecordPathState state).getMem (BitVec.ofNat 64 a) =
        (capOpenSaltedState state).getMem (BitVec.ofNat 64 a)) := by
  have small := cap_open_record_at_small entry
  have tail := cap_open_record_tail_facts (capOpenSaltedState state) position rootBase cursor
    (cap_open_record_salted_pc state entry.pc) (cap_open_record_salted_index state position entry.loaded)
    (by have := entry.positionBound; omega)
    ((cap_open_record_salted_register state .x9 (by decide)).trans entry.roots)
    ((cap_open_record_salted_register state .x19 (by decide)).trans (by rw [entry.leaves]; rfl))
    ((cap_open_record_salted_register state .x25 (by decide)).trans entry.pointer)
    entry.heapBelow (by omega)
  have saltMem : ∀ address : Word, (capOpenSaltedState state).getMem address = state.getMem address →
      True := fun _ _ => trivial
  refine ⟨tail.1, tail.2.1, tail.2.2.1, tail.2.2.2.1, ?_, ?_, tail.2.2.2.2.2.2⟩
  · intro reg h1 h6 h7 h23 h30 h20 h25 h28
    rw [capOpenRecordPathState, tail.2.2.2.2.1 reg h1 h6 h7 h23 h30 h20 h25 h28]
    exact cap_open_record_salted_register state reg ⟨h6, h20, h23⟩
  · intro k hk w hw
    rw [capOpenRecordPathState, tail.2.2.2.2.2.1 k hk w hw]
    -- the cells lie below the cursor: the salt-field block and the prefix leave them unchanged
    have cellBound : rootBase + 268435784 + 368*(position/4) + 32*capStubPlace (position%4) k + 8*w <
        cursor := by
      have place : capStubPlace (position%4) k ≤ 3 := by unfold capStubPlace; split <;> omega
      have : 368*(position/4) ≤ 368*(2^22) := Nat.mul_le_mul_left _ (by have := entry.positionBound; omega)
      have := entry.heapBelow
      omega
    rw [capOpenSaltedState, cap_nonce_eight_memory_outside]
    · rfl
    · intro word equal
      rw [cap_open_record_prepare_register state 3 (by decide) .x25 (by decide), entry.pointer,
        ← BitVec.ofNat_add] at equal
      have := cap_stub_word_ne _ _ (by omega) (by have := word.isLt; omega)
        (by have := word.isLt; omega) equal
      exact this

theorem cap_open_record_path_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x30 ∧ reg ≠ .x20 ∧
      reg ≠ .x25 ∧ reg ≠ .x28)
    {rootBase saltBase cursor limit position : Nat}
    (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordPathState state).getReg reg = state.getReg reg :=
  (cap_open_record_path_facts entry).2.2.2.2.1 reg outside.1 outside.2.1 outside.2.2.1 outside.2.2.2.1
    outside.2.2.2.2.1 outside.2.2.2.2.2.1 outside.2.2.2.2.2.2.1 outside.2.2.2.2.2.2.2

theorem cap_open_record_path_ready {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    CapOpenPathReady rootBase limit 14 (capOpenRecordPathState state) := by
  have facts := cap_open_record_path_facts entry
  refine ⟨(cap_open_record_path_register state .x9 (by decide) entry).trans entry.roots, ?_,
    facts.1, by decide, ?_, ?_⟩
  · rw [facts.2.2.2.1]; rfl
  · exact ⟨4194304 + position/4, by have := entry.positionBound; omega, facts.2.1⟩
  · refine ⟨cursor+128, facts.2.2.1, by have := entry.cursorAligned; omega, ?_⟩
    have := entry.space
    omega

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

/-- Prepare, salt field, call, stub and latch: 62 instructions, 68 cycles. -/
theorem cap_open_record_start_execute {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (62+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordPathState state) allowCoins
          return result.charge 68 0) := by
  have small := cap_open_record_at_small entry
  have source := cap_open_record_salt_address state position saltBase entry.loaded entry.salts entry.stride
  have destination := (cap_open_record_prepare_register state 3 (by decide) .x25
    (by decide)).trans entry.pointer
  have saltBelow := entry.saltBelow
  have saltAligned := entry.saltAligned
  have cursorAligned := entry.cursorAligned
  have memory : MEMORY_BYTES ≤ 2^64 := by simp only [MEMORY_BYTES]; omega
  have limitBound := entry.limitBound
  have space := entry.space
  have sourceAccess : ∀ word : Fin 2,
      accessValid ((capOpenRecordPrefix state 3).getReg .x23 +
        BitVec.ofNat 64 (8*word.val)) 8 = true := by
    intro word
    rw [source, ← BitVec.ofNat_add]
    exact cap_stub_word_access _ (by omega) (by have := word.isLt; omega)
  have destinationAccess : ∀ word : Fin 3,
      accessValid ((capOpenRecordPrefix state 3).getReg .x25 +
        BitVec.ofNat 64 (8*word.val)) 8 = true := by
    intro word
    rw [destination, ← BitVec.ofNat_add]
    exact cap_stub_word_access _ (by omega) (by have := word.isLt; omega)
  have copyPC : (capOpenRecordPrefix state 3).pc = 4224 := by
    rw [cap_open_record_prepare_pc state 3 (by decide), entry.pc]
    rfl
  have tailRun := cap_open_record_tail_execute (capOpenSaltedState state) position rootBase cursor
    (cap_open_record_salted_pc state entry.pc) (cap_open_record_salted_index state position entry.loaded)
    (by have := entry.positionBound; omega)
    ((cap_open_record_salted_register state .x9 (by decide)).trans entry.roots)
    ((cap_open_record_salted_register state .x19 (by decide)).trans (by rw [entry.leaves]; rfl))
    ((cap_open_record_salted_register state .x25 (by decide)).trans entry.pointer)
    entry.rootAligned cursorAligned entry.heapBelow (by omega)
  rw [show 62+fuel = 3+(8+(51+fuel)) by omega,
    cap_open_record_prepare_execute state entry.pc entry.indexValid,
    cap_nonce_eight_execute _ cap_open_record_salt_copy_fetched
      (capOpenRecordPrefix state 3) copyPC sourceAccess destinationAccess,
    ← capOpenSaltedState, tailRun, ← capOpenRecordPathState]
  simp only [bind_assoc, pure_bind, charge_pair, Nat.reduceAdd]

end CommitGolfCandidate
