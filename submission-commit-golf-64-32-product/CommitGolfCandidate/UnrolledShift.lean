import CommitGolfCandidate.ContiguousPosition

/-! Unrolled leaves keep the live salt and heap pointers at the segment base and
fold each leaf's position into instruction immediates. Relative to the reference
state of leaf `slot`, the live x18 and x23 lag by exactly `slot` leaves; every
other register, memory and the program counter agree. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def unrolledShift (slot : Nat) (state : MachineState) : MachineState :=
  (state.setReg .x18 (state.getReg .x18 - BitVec.ofNat 64 (24 * slot))).setReg .x23
    (state.getReg .x23 - BitVec.ofNat 64 (32 * slot))

theorem unrolled_shift_register (slot : Nat) (state : MachineState) (reg : Reg)
    (not18 : reg ≠ .x18) (not23 : reg ≠ .x23) :
    (unrolledShift slot state).getReg reg = state.getReg reg := by
  simp only [unrolledShift, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not18),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not23)]

theorem unrolled_shift_salt (slot : Nat) (state : MachineState) :
    (unrolledShift slot state).getReg .x18 = state.getReg .x18 - BitVec.ofNat 64 (24 * slot) := rfl

theorem unrolled_shift_heap (slot : Nat) (state : MachineState) :
    (unrolledShift slot state).getReg .x23 = state.getReg .x23 - BitVec.ofNat 64 (32 * slot) := rfl

theorem unrolled_shift_memory (slot : Nat) (state : MachineState) :
    (unrolledShift slot state).mem = state.mem := rfl

theorem unrolled_shift_pc (slot : Nat) (state : MachineState) :
    (unrolledShift slot state).pc = state.pc := rfl

theorem unrolled_shift_zero (state : MachineState) : unrolledShift 0 state = state := by
  cases state
  dsimp [unrolledShift, MachineState.getReg, MachineState.setReg]
  congr 1
  funext reg
  cases reg <;> simp

theorem unrolled_shift_set_pc (slot : Nat) (state : MachineState) (pc : Word) :
    unrolledShift slot (state.setPC pc) = (unrolledShift slot state).setPC pc := rfl

theorem unrolled_shift_set_mem (slot : Nat) (state : MachineState) (address value : Word) :
    unrolledShift slot (state.setMem address value) =
      (unrolledShift slot state).setMem address value := rfl

theorem unrolled_shift_set_reg (slot : Nat) (state : MachineState) (reg : Reg) (value : Word)
    (not18 : reg ≠ .x18) (not23 : reg ≠ .x23) :
    unrolledShift slot (state.setReg reg value) = (unrolledShift slot state).setReg reg value := by
  cases state
  cases reg <;> first
    | exact absurd rfl not18
    | exact absurd rfl not23
    | rfl
    | (dsimp only [unrolledShift, MachineState.getReg, MachineState.setReg]
       congr 1
       funext other
       cases other <;> rfl)

theorem unrolled_shift_set_byte (slot : Nat) (state : MachineState) (address : Word) (value : BitVec 8) :
    unrolledShift slot (state.setByte address value) =
      (unrolledShift slot state).setByte address value := rfl

theorem unrolled_shift_write_bits {bits : Nat} (slot : Nat) (state : MachineState) (address : Word)
    (answer : BitVec bits) :
    writeBits (unrolledShift slot state) address answer = unrolledShift slot (writeBits state address answer) := by
  unfold writeBits
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (unrolledShift slot current) =
      unrolledShift slot (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current) := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.foldl_cons]
      rw [← ih, unrolled_shift_set_byte]
  rw [fold]
  rfl

theorem unrolled_shift_read (slot : Nat) (state : MachineState) (address count : Nat) :
    readBuffer (unrolledShift slot state) address count = readBuffer state address count :=
  read_buffer_memory_congr _ _ rfl address count

theorem unrolled_shift_oracle_input (slot : Nat) (state : MachineState) :
    oracleInput (unrolledShift slot state) = oracleInput state := by
  unfold oracleInput
  rw [unrolled_shift_register slot state .x13 (by decide) (by decide),
    unrolled_shift_register slot state .x10 (by decide) (by decide),
    unrolled_shift_register slot state .x12 (by decide) (by decide),
    unrolled_shift_register slot state .x11 (by decide) (by decide)]
  simp only [unrolled_shift_read]

theorem unrolled_sign_extend (value : Nat) (small : value < 2048) :
    signExtend12 (BitVec.ofNat 12 value) = BitVec.ofNat 64 value := by
  apply BitVec.eq_of_toNat_eq
  rw [signExtend12, BitVec.toNat_signExtend]
  simp [BitVec.toNat_ofNat, BitVec.msb_eq_decide, Nat.mod_eq_of_lt (show value < 4096 by omega)]
  omega

end CommitGolfCandidate
