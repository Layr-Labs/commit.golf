import CommitGolfCandidate.CapCheckGroupEffect

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_group_mark_access (state : MachineState) (group : Nat)
    (bounded : group < 256) (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (roots : state.getReg .x18 = 12288) :
    accessValid ((capCheckGroupStartPrefix state 5).getReg .x30) 8 = true := by
  have address := (cap_check_group_start_addresses state group bounded index leaves marks roots).2.1
  have unchanged : (capCheckGroupStartPrefix state 6).getReg .x30 =
      (capCheckGroupStartPrefix state 5).getReg .x30 := by
    simp only [capCheckGroupStartPrefix, capCheckGroupStartInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30)]
  rw [← unchanged, address]
  exact (cap_mark_address_valid 256 (256+group) (by decide) (by omega)).1

private theorem word_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address+8 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, bounded, aligned, decide_true, Bool.true_and]

theorem cap_check_group_root_access (group : Nat) (bounded : group < 256)
    (word : Fin 4) :
    accessValid (BitVec.ofNat 64 (12288+32*(256+group)) +
      signExtend12 (BitVec.ofNat 12 (8*word.val))) 8 = true := by
  have offset : signExtend12 (BitVec.ofNat 12 (8*word.val)) =
      BitVec.ofNat 64 (8*word.val) := by
    fin_cases word <;> decide
  rw [offset, ← BitVec.ofNat_add]
  apply word_access
  · omega
  · have inside := word.isLt
    simp only [MEMORY_BYTES]
    omega

theorem cap_check_group_scratch_access (word : Fin 4) :
    accessValid ((256 : Word) +
      signExtend12 (BitVec.ofNat 12 (8*word.val))) 8 = true := by
  fin_cases word <;> decide

end CommitGolfCandidate
