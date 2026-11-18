import CommitGolfCandidate.CapCheckPathBlock

/-! Supported lower-path replies preserve the caller registers (the latch's
call into the truncation code overwrites x1) and implement the natural
node/counter progress only when their stated bounds hold. These projections
avoid identifying relocated path states with any old checker PC. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_path_block_projection (state : MachineState) (answer : BitVec 256) :
    (capCheckPathBlockState state answer).getReg .x25 = state.getReg .x25 + 32 ∧
    (capCheckPathBlockState state answer).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (capCheckPathBlockState state answer).getReg .x29 = state.getReg .x29 - 1 := by
  have preserved (reg : Reg) (outside : reg ∈ [.x25, .x20, .x29]) :
      (capCheckCompressionState (capCheckPathPreparedState state) answer).getReg reg =
        state.getReg reg := by
    rcases List.mem_cons.mp outside with rfl | rest
    · exact (cap_check_compression_register _ answer .x25 (by decide)).trans
        (cap_check_path_prepared_register state .x25 (by decide))
    rcases List.mem_cons.mp rest with rfl | rest
    · exact (cap_check_compression_register _ answer .x20 (by decide)).trans
        (cap_check_path_prepared_register state .x20 (by decide))
    have equal : reg = .x29 := by simpa using rest
    subst reg
    exact (cap_check_compression_register _ answer .x29 (by decide)).trans
      (cap_check_path_prepared_register state .x29 (by decide))
  have pointers := cap_check_path_tail_pointers
    (capCheckCompressionState (capCheckPathPreparedState state) answer)
  simpa only [capCheckPathBlockState, preserved .x25 (by simp),
    preserved .x20 (by simp), preserved .x29 (by simp)] using
    pointers

theorem cap_check_path_block_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ∉ [.x6,.x7,.x5,.x10,.x11,.x12,.x13,.x25,.x20,.x29,.x1]) :
    (capCheckPathBlockState state answer).getReg reg = state.getReg reg := by
  rw [capCheckPathBlockState, cap_check_path_tail_register _ reg (by simp_all),
    cap_check_compression_register _ answer reg (by simp_all),
    cap_check_path_prepared_register state reg (by simp_all)]

theorem cap_check_path_block_node (state : MachineState) (answer : BitVec 256) (node : Nat)
    (small : node < 2^64) (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capCheckPathBlockState state answer).getReg .x20 = BitVec.ofNat 64 (node/2) := by
  rw [(cap_check_path_block_projection state answer).2.1, index]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  change node % 2^64 / 2 = node/2 % 2^64
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega : node/2 < 2^64)]

theorem cap_check_path_block_counter (state : MachineState) (answer : BitVec 256)
    (remaining : Nat) (positive : 0 < remaining)
    (counter : state.getReg .x29 = BitVec.ofNat 64 remaining) :
    (capCheckPathBlockState state answer).getReg .x29 = BitVec.ofNat 64 (remaining-1) := by
  rw [(cap_check_path_block_projection state answer).2.2, counter]
  exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by omega)

theorem cap_check_path_block_exit (state : MachineState) (answer : BitVec 256)
    (remaining : Nat) (positive : 0 < remaining) (bounded : remaining ≤ 17)
    (counter : state.getReg .x29 = BitVec.ofNat 64 remaining) :
    (capCheckPathBlockState state answer).pc = if remaining = 1 then 4420 else 4272 := by
  have count := (cap_check_compression_register (capCheckPathPreparedState state)
    answer .x29 (by decide)).trans
    ((cap_check_path_prepared_register state .x29 (by decide)).trans counter)
  have zero : (BitVec.ofNat 64 remaining - 1 = 0) ↔ remaining = 1 := by
    change (BitVec.ofNat 64 remaining - BitVec.ofNat 64 1 = (0 : Word)) ↔ remaining = 1
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) remaining 1 (by decide) (by omega)]
    constructor
    · intro equal
      have value := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : remaining-1 < 2^64)] at value
      change remaining-1 = 0 at value
      omega
    · intro one
      subst remaining
      rfl
  have replyPC : (capCheckCompressionState (capCheckPathPreparedState state) answer).pc = 4404 := by
    rw [cap_check_compression_pc, cap_check_path_prepared_pc]
    rfl
  rw [capCheckPathBlockState, cap_check_path_tail_pc _ replyPC, count]
  simp only [zero]

end CommitGolfCandidate
