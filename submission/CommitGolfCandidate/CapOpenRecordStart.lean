import CommitGolfCandidate.CapOpenRecordEffect
import CommitGolfCandidate.CapOpenPathLoop

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenSaltedState (state : MachineState) : MachineState :=
  capNonceEightState (capOpenRecordPrefix state 3)

def capOpenRecordPathState (state : MachineState) : MachineState :=
  capOpenRecordTailPrefix (capOpenSaltedState state) 6

attribute [local irreducible] capOpenSaltedState capOpenRecordPathState

theorem cap_open_record_salted_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x20 ∧ reg ≠ .x23) :
    (capOpenSaltedState state).getReg reg = state.getReg reg := by
  rw [capOpenSaltedState]
  exact (cap_nonce_eight_register _ reg outside.1).trans
    (cap_open_record_prepare_register state 3 (by decide) reg
      ⟨outside.2.1, outside.1, outside.2.2⟩)

theorem cap_open_record_path_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧
      reg ≠ .x25 ∧ reg ≠ .x28) :
    (capOpenRecordPathState state).getReg reg = state.getReg reg := by
  rw [capOpenRecordPathState]
  exact (cap_open_record_tail_register _ reg
    ⟨outside.2.2.2.1, outside.2.1, outside.2.2.2.2⟩).trans
    (cap_open_record_salted_register state reg ⟨outside.1, outside.2.1, outside.2.2.1⟩)

theorem cap_open_record_path_cursor (state : MachineState) :
    (capOpenRecordPathState state).getReg .x25 = state.getReg .x25 + 32 := by
  rw [capOpenRecordPathState, cap_open_record_tail_cursor,
    cap_open_record_salted_register state .x25 (by decide)]

theorem cap_open_record_path_index (state : MachineState) (position : Nat)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216) :
    (capOpenRecordPathState state).getReg .x20 =
      BitVec.ofNat 64 (16777216+position) := by
  have salted : (capOpenSaltedState state).getReg .x20 = BitVec.ofNat 64 position := by
    rw [capOpenSaltedState, cap_nonce_eight_register _ .x20 (by decide),
      cap_open_record_index, loaded]
  rw [capOpenRecordPathState, cap_open_record_tail_index, salted,
    cap_open_record_salted_register state .x19 (by decide), leaves]
  change BitVec.ofNat 64 position + BitVec.ofNat 64 16777216 = _
  rw [← BitVec.ofNat_add, Nat.add_comm position 16777216]

theorem cap_open_record_path_pc (state : MachineState) (pc : state.pc = 4212) :
    (capOpenRecordPathState state).pc = 4280 := by
  rw [capOpenRecordPathState, cap_open_record_tail_pc _ 6 (by decide),
    capOpenSaltedState, cap_nonce_eight_pc _,
    cap_open_record_prepare_pc state 3 (by decide), pc]
  rfl

theorem cap_open_record_path_ready (rootBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (bounded : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216) :
    CapOpenPathReady rootBase limit 16 (capOpenRecordPathState state) := by
  refine ⟨(cap_open_record_path_register state .x9 (by decide)).trans roots, ?_,
    cap_open_record_path_pc state pc, by decide, ?_, ?_⟩
  · rw [capOpenRecordPathState]
    exact cap_open_record_tail_count _
  · exact ⟨16777216+position, by omega, cap_open_record_path_index state position loaded leaves⟩
  · refine ⟨cursor+32, ?_, by omega, by omega⟩
    rw [cap_open_record_path_cursor, pointer]
    exact (BitVec.ofNat_add cursor 32).symm

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_open_record_start_execute (state : MachineState)
    (position saltBase cursor : Nat) (pc : state.pc = 4212)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (salts : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (saltAligned : saltBase % 8 = 0) (saltBound : saltBase+24*position+32 ≤ MEMORY_BYTES)
    (cursorAligned : cursor % 8 = 0) (cursorBound : cursor+32 ≤ MEMORY_BYTES)
    (stride : state.getReg .x17 = 24)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (17+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordPathState state) allowCoins
          return result.charge 20 0) := by
  have source := cap_open_record_salt_address state position saltBase loaded salts stride
  have destination := (cap_open_record_prepare_register state 3 (by decide) .x25
    (by decide)).trans pointer
  have saltSmall : saltBase+24*position < 2^64 := by
    simp only [MEMORY_BYTES] at saltBound
    omega
  have cursorSmall : cursor < 2^64 := by
    simp only [MEMORY_BYTES] at cursorBound
    omega
  have sourceAccess : ∀ word : Fin 4,
      accessValid ((capOpenRecordPrefix state 3).getReg .x23 +
        BitVec.ofNat 64 (8*word.val)) 8 = true := by
    rw [source]
    apply opening_digest_access_valid
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt saltSmall] using saltBound
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt saltSmall]
      omega
  have destinationAccess : ∀ word : Fin 4,
      accessValid ((capOpenRecordPrefix state 3).getReg .x25 +
        BitVec.ofNat 64 (8*word.val)) 8 = true := by
    rw [destination]
    apply opening_digest_access_valid
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cursorSmall] using cursorBound
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cursorSmall] using cursorAligned
  have copyPC : (capOpenRecordPrefix state 3).pc = 4224 := by
    rw [cap_open_record_prepare_pc state 3 (by decide), pc]
    rfl
  have tailPC : (capOpenSaltedState state).pc = 4256 := by
    rw [capOpenSaltedState, cap_nonce_eight_pc _, copyPC]
    rfl
  have tailRun : execute ((capExperimental 24).image .opening) (6+fuel)
      (capNonceEightState (capOpenRecordPrefix state 3)) allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordPathState state) allowCoins
          return result.charge 6 0) := by
    rw [← capOpenSaltedState, capOpenRecordPathState]
    exact cap_open_record_tail_execute _ tailPC fuel allowCoins
  rw [show 17+fuel = 3+(8+(6+fuel)) by omega,
    cap_open_record_prepare_execute state pc indexValid,
    cap_nonce_eight_execute _ cap_open_record_salt_copy_fetched
      cap_open_record_nonce_nop_fetched (capOpenRecordPrefix state 3) copyPC
      (fun word => sourceAccess ⟨word.val, by have bound := word.isLt; omega⟩) destinationAccess,
    tailRun]
  simp only [bind_assoc, pure_bind, charge_pair, Nat.reduceAdd]

end CommitGolfCandidate
