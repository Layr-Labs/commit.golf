import CommitGolfCandidate.CapCheckPathBlock

/-! Supported lower-path replies preserve the caller registers and implement
the natural node/counter progress only when their stated bounds hold. These
projections avoid identifying relocated path states with any old checker PC. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem tail_node (state : MachineState) :
    (capCheckPathTailPrefix state 4).getReg .x20 = state.getReg .x20 >>> 1 := by
  have branch (current : MachineState) (offset : BitVec 13) :
      (execInstrBr current (.BNE .x29 .x0 offset)).getReg .x20 =
        current.getReg .x20 := by
    simp only [execInstrBr]
    split <;> exact MachineState.getReg_setPC
  rw [cap_check_path_tail_succ state 3 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 3) (.BNE .x29 .x0 8048)).getReg .x20 = _
  rw [branch]
  simp (disch := decide) only [capCheckPathTailPrefix, capCheckPathTailInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    show (1 : BitVec 6).toNat = 1 by decide]

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
  have node := tail_node (capCheckCompressionState (capCheckPathPreparedState state) answer)
  have combined := And.intro pointers.1 (And.intro node pointers.2)
  simpa only [capCheckPathBlockState, preserved .x25 (by simp),
    preserved .x20 (by simp), preserved .x29 (by simp)] using
    combined

theorem cap_check_path_block_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ∉ [.x6,.x7,.x5,.x10,.x11,.x12,.x13,.x25,.x20,.x29]) :
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
  rw [capCheckPathBlockState, cap_check_path_tail_pc, count,
    cap_check_compression_pc, cap_check_path_prepared_pc]
  simp only [zero]
  rfl

end CommitGolfCandidate
