import CommitGolfCandidate.ChainedTailEmit

/-! Byte and register frames for guarded emission. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem tail_guard_byte (s : MachineState) (query : Word) : (tailGuard s).getByte query = s.getByte query := by
  simp only [MachineState.getByte,tail_guard_memory]

theorem tail_append_byte (s : MachineState) (query : Word) : (tailAppendPrefix s 3).getByte query = s.getByte query := by
  simp only [MachineState.getByte,tail_append_memory]

theorem tail_emit_frame (s : MachineState) (reg : Reg) (pointer : reg ≠ .x20)
    (value : reg ≠ .x23) (count : reg ≠ .x25) (scratch : reg ≠ .x28) :
    (tailEmitState s).getReg reg = s.getReg reg := by
  dsimp only [tailEmitState]
  split
  · rw [tail_guard_register,tail_append_frame s reg value count scratch]
  · rw [tail_flush_frame _ reg pointer value count,tail_guard_register,tail_append_frame s reg value count scratch]

theorem tail_emit_pointer (s : MachineState) : (tailEmitState s).getReg .x20 =
    if tailSkips (tailAppendPrefix s 3) then s.getReg .x20 else s.getReg .x20+1 := by
  dsimp only [tailEmitState]
  split <;> simp only [tail_flush_pointer,tail_guard_register,tail_append_frame s .x20 (by decide) (by decide) (by decide)]

theorem tail_emit_value (s : MachineState) : (tailEmitState s).getReg .x23 =
    if tailSkips (tailAppendPrefix s 3) then (tailAppendPrefix s 3).getReg .x23
    else (tailAppendPrefix s 3).getReg .x23 >>> 8 := by
  dsimp only [tailEmitState]
  split <;> simp only [tail_flush_value,tail_guard_register]

theorem tail_emit_count (s : MachineState) : (tailEmitState s).getReg .x25 =
    if tailSkips (tailAppendPrefix s 3) then (tailAppendPrefix s 3).getReg .x25
    else (tailAppendPrefix s 3).getReg .x25-8 := by
  dsimp only [tailEmitState]
  split <;> simp only [tail_flush_count,tail_guard_register]

theorem tail_emit_byte (s : MachineState) (query : Word) : (tailEmitState s).getByte query =
    if tailSkips (tailAppendPrefix s 3) then s.getByte query
    else if query = s.getReg .x20 then ((tailAppendPrefix s 3).getReg .x23).setWidth 8 else s.getByte query := by
  dsimp only [tailEmitState]
  split
  · rw [tail_guard_byte,tail_append_byte]
  · rw [tail_flush_byte,tail_guard_register,tail_guard_register,
      tail_append_frame s .x20 (by decide) (by decide) (by decide),tail_guard_byte,tail_append_byte]

theorem tail_skips_count (s : MachineState) (count : Nat) (small : count ≤ 13)
    (counter : s.getReg .x25 = BitVec.ofNat 64 count) (eight : s.getReg .x27 = 8) :
    tailSkips s = decide (count < 8) := by
  have fit : count < 2^64 := by omega
  have reduced : count % 18446744073709551616 = count := Nat.mod_eq_of_lt fit
  simp [tailSkips,BitVec.ult,counter,eight,BitVec.toNat_ofNat,reduced]

theorem tail_shift_right_nat (value : Nat) (fit : value < 2^64) :
    BitVec.ofNat 64 value >>> 8 = BitVec.ofNat 64 (value/256) := by
  apply BitVec.eq_of_toNat_eq
  have quotient : value/256 < 2^64 := lt_of_le_of_lt (Nat.div_le_self _ _) fit
  have reduced : value % 18446744073709551616 = value := Nat.mod_eq_of_lt fit
  have quotientReduced : value/256 % 18446744073709551616 = value/256 := Nat.mod_eq_of_lt quotient
  simp [BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,reduced,quotientReduced]

theorem tail_remainder_small (value count : Nat) (full : value < 2^count)
    (ready : 8 ≤ count) : value/256 < 2^(count-8) := by
  have power : 2^count = 2^(count-8)*256 := by
    calc
      2^count = 2^((count-8)+8) := congrArg (fun n : Nat => 2^n) (by omega)
      _ = _ := by rw [Nat.pow_add]
  apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
  rwa [←power]

end CommitGolfCandidate.Chained.Native
