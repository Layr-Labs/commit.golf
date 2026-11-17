import CommitGolfCandidate.CapOpenPathStep
import CommitGolfCandidate.CapCopyFrame
import CommitGolfCandidate.CapMarkAlgebra

/-! Register and memory projections for actual lower-path iterations. Natural
counter/index bounds are supplied separately from modular instruction effects.
The copied digest and outside-byte frame use explicit source/output separation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x28 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x28 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem cap_open_path_tail_memory (state : MachineState) :
    (capOpenPathTailPrefix state 4).mem = state.mem := by
  rw [cap_open_path_tail_succ state 3 (by decide)]
  change (execInstrBr (capOpenPathTailPrefix state 3) (.BNE .x28 .x0 8136)).mem = state.mem
  rw [branch_memory]
  rfl

theorem cap_open_path_tail_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28) :
    (capOpenPathTailPrefix state 4).getReg reg = state.getReg reg := by
  rw [cap_open_path_tail_succ state 3 (by decide)]
  change (execInstrBr (capOpenPathTailPrefix state 3) (.BNE .x28 .x0 8136)).getReg reg = _
  rw [branch_register]
  simp only [capOpenPathTailPrefix, capOpenPathTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

private theorem tail_projection (state : MachineState) :
    (capOpenPathTailPrefix state 4).getReg .x25 = state.getReg .x25 + 32 ∧
    (capOpenPathTailPrefix state 4).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (capOpenPathTailPrefix state 4).getReg .x28 = state.getReg .x28 - 1 := by
  have last (reg : Reg) : (capOpenPathTailPrefix state 4).getReg reg =
      (capOpenPathTailPrefix state 3).getReg reg := by
    rw [cap_open_path_tail_succ state 3 (by decide)]
    exact branch_register _ _ reg
  rw [last .x25, last .x20, last .x28]
  simp (disch := decide) only [capOpenPathTailPrefix,
    capOpenPathTailInstructions, List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,
    show (1 : BitVec 6).toNat = 1 by decide]
  constructor
  · rfl
  · constructor
    · trivial
    · rw [BitVec.sub_eq_add_neg]
      rfl

theorem cap_open_path_projection (state : MachineState) :
    (capOpenPathState state).getReg .x25 = state.getReg .x25 + 32 ∧
    (capOpenPathState state).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (capOpenPathState state).getReg .x28 = state.getReg .x28 - 1 := by
  have copied : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x23 →
      (capOpenPathCopied state).getReg reg = state.getReg reg := by
    intro reg ne6 ne7 ne23
    exact (cap_copy_prefix_register false _ 8 (by decide) reg ne6).trans
      (cap_open_path_prepare_register state 3 (by decide) reg ⟨ne7, ne23⟩)
  simpa (disch := decide) only [capOpenPathState, copied .x25, copied .x20, copied .x28]
    using tail_projection (capOpenPathCopied state)

theorem cap_open_path_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28) :
    (capOpenPathState state).getReg reg = state.getReg reg := by
  exact (cap_open_path_tail_register _ reg
    ⟨outside.2.2.2.1, outside.2.2.2.2.1, outside.2.2.2.2.2⟩).trans
    ((cap_copy_prefix_register false _ 8 (by decide) reg outside.1).trans
      (cap_open_path_prepare_register state 3 (by decide) reg
        ⟨outside.2.1, outside.2.2.1⟩))

theorem cap_open_path_index (state : MachineState) (node : Nat)
    (small : node < 2^64) (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capOpenPathState state).getReg .x20 = BitVec.ofNat 64 (node/2) := by
  rw [(cap_open_path_projection state).2.1, index]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  change node % 2^64 / 2 = node/2 % 2^64
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (by omega : node/2 < 2^64)]

theorem cap_open_path_counter (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining) (bounded : remaining ≤ 17)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (capOpenPathState state).getReg .x28 = BitVec.ofNat 64 (remaining-1) := by
  rw [(cap_open_path_projection state).2.2, counter]
  exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by omega)

theorem cap_open_path_exit (state : MachineState) (remaining : Nat)
    (pc : state.pc = 4280) (positive : 0 < remaining) (bounded : remaining ≤ 17)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (capOpenPathState state).pc = if remaining = 1 then 4340 else 4280 := by
  have copiedPC : (capOpenPathCopied state).pc = 4324 := by
    rw [capOpenPathCopied, cap_copy_prefix_pc false _ 8 (by decide),
      cap_open_path_prepare_pc state 3 (by decide), pc]
    rfl
  have copiedCount : (capOpenPathCopied state).getReg .x28 =
      BitVec.ofNat 64 remaining :=
    (cap_copy_prefix_register false _ 8 (by decide) .x28 (by decide)).trans
      ((cap_open_path_prepare_register state 3 (by decide) .x28 (by decide)).trans counter)
  have decrement : BitVec.ofNat 64 remaining + BitVec.signExtend 64 (4095 : BitVec 12) =
      BitVec.ofNat 64 (remaining-1) := by
    exact cap_mark_decrement remaining positive
  have zero : (BitVec.ofNat 64 (remaining-1) = 0) ↔ remaining = 1 := by
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
  have earlyPC : (capOpenPathTailPrefix (capOpenPathCopied state) 3).pc = 4336 := by
    rw [cap_open_path_tail_pc _ 3 (by decide), copiedPC]
    rfl
  have earlyCount : (capOpenPathTailPrefix (capOpenPathCopied state) 3).getReg .x28 =
      BitVec.ofNat 64 (remaining-1) := by
    simp (disch := decide) only [capOpenPathTailPrefix, capOpenPathTailInstructions,
      List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, copiedCount, decrement]
  change (capOpenPathTailPrefix (capOpenPathCopied state) 4).pc = _
  rw [cap_open_path_tail_succ _ 3 (by decide)]
  change (execInstrBr (capOpenPathTailPrefix (capOpenPathCopied state) 3)
    (.BNE .x28 .x0 8136)).pc = _
  simp only [execInstrBr, earlyCount, earlyPC,
    show (capOpenPathTailPrefix (capOpenPathCopied state) 3).getReg .x0 = 0 from rfl]
  by_cases last : remaining = 1
  · subst remaining
    simp only [Nat.sub_self, show BitVec.ofNat 64 0 = (0 : Word) by rfl,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, MachineState.setPC]
    rfl
  · have nonzero : BitVec.ofNat 64 (remaining-1) ≠ 0 :=
      fun equal => last (zero.mp equal)
    rw [ite_eq_left (bne_iff_ne.mpr nonzero)]
    simp only [MachineState.setPC, last, ite_false]
    decide

theorem cap_open_path_digest (state : MachineState) (node rootBase cursor : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (base : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (rootAligned : rootBase % 8 = 0) (cursorAligned : cursor % 8 = 0)
    (sourceBefore : rootBase + 32*(node ^^^ 1) + 32 ≤ cursor)
    (cursorBound : cursor+32 ≤ 2^64) :
    readBuffer (capOpenPathState state) cursor 32 =
      readBuffer state (rootBase + 32*(node ^^^ 1)) 32 := by
  have source := cap_open_path_address state node rootBase index base
  have destination := (cap_open_path_prepare_register state 3 (by decide) .x25
    (by decide)).trans pointer
  have copied := cap_copy_digest false (capOpenPathPrefix state 3)
    (rootBase + 32*(node ^^^ 1)) cursor source destination (by omega) cursorAligned
    (by omega) cursorBound (Or.inl sourceBefore)
  have tailSame := read_buffer_memory_congr (capOpenPathState state)
    (capOpenPathCopied state) (cap_open_path_tail_memory _) cursor 32
  exact tailSame.trans (copied.trans (read_buffer_memory_congr _ _
    (cap_open_path_prepare_memory state 3 (by decide)) _ 32))

end CommitGolfCandidate
