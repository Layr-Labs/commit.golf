import CommitGolfCandidate.CapOpenPathLoop

/-! The unrolled opening path uses one fixed output register. The reference path
continues to supply the record semantics, with its cursor and PC restored on return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

private def fastPathInstructions (level : Nat) : List Instr :=
  [.XORI .x7 .x20 1, .SLLI .x7 .x7 5, .ADD .x23 .x9 .x7,
   .LD .x6 .x23 0, .SD .x25 .x6 (BitVec.ofNat 12 (32*level)),
   .LD .x6 .x23 8, .SD .x25 .x6 (BitVec.ofNat 12 (32*level+8)),
   .LD .x6 .x23 16, .SD .x25 .x6 (BitVec.ofNat 12 (32*level+16)),
   .LD .x6 .x23 24, .SD .x25 .x6 (BitVec.ofNat 12 (32*level+24)),
   .SRLI .x20 .x20 1]

private def fastPathPrefix (state : MachineState) (level count : Nat) : MachineState :=
  ((fastPathInstructions level).take count).foldl execInstrBr state

private def fastFrame (state : MachineState) (base counter pc : Word) : MachineState :=
  ((state.setReg .x25 base).setReg .x28 counter).setPC pc

private theorem reg_mem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl

@[simp] private theorem pc_set (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl
@[simp] private theorem pc_overwrite (s : MachineState) (a b : Word) :
    (s.setPC a).setPC b=s.setPC b := rfl

private theorem frame_after_pc (s : MachineState) (p base counter pc : Word) :
    fastFrame (s.setPC p) base counter pc = fastFrame s base counter pc := by
  cases s
  rfl

private theorem frame_branch (s : MachineState) (base counter pc : Word) :
    fastFrame (execInstrBr s (.BNE .x28 .x0 8136)) base counter pc =
      fastFrame s base counter pc := by
  simp only [execInstrBr]
  split <;> apply frame_after_pc

private theorem word_ofNat_zero : BitVec.ofNat 64 0 = (0#64) := rfl

private theorem word_add_zero (x : Word) : x + (0 : Word) = x := BitVec.add_zero x

private theorem word_zero_add (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

private theorem immediate_offset (level word : Nat) (bound : level<16) (inside : word<4) :
    signExtend12 (BitVec.ofNat 12 (32*level+8*word))=
      BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 (8*word) := by
  interval_cases level <;> interval_cases word <;> rfl

private theorem pc_after_register (s : MachineState) (p v : Word) (r : Reg) :
    (s.setPC p).setReg r v = (s.setReg r v).setPC p := by cases r <;> rfl

private theorem pc_after_memory (s : MachineState) (p a v : Word) :
    (s.setPC p).setMem a v = (s.setMem a v).setPC p := rfl

private theorem get_mem_after_pc (s : MachineState) (p a : Word) :
    (s.setPC p).getMem a = s.getMem a := rfl

private theorem get_mem_after_register (s : MachineState) (a v : Word) (r : Reg) :
    (s.setReg r v).getMem a = s.getMem a := by cases r <;> rfl

private theorem x25_after_memory (s : MachineState) (x a v : Word) :
    (s.setReg .x25 x).setMem a v = (s.setMem a v).setReg .x25 x := rfl

private theorem x28_after_memory (s : MachineState) (x a v : Word) :
    (s.setReg .x28 x).setMem a v = (s.setMem a v).setReg .x28 x := rfl

private theorem register_overwrite (s : MachineState) (r : Reg) (a b : Word) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  cases s
  cases r <;> simp [MachineState.setReg]
  all_goals funext current; cases current <;> rfl

private theorem x25_after_register (s : MachineState) (x v : Word) (r : Reg)
    (different : r ≠ .x25 ∧ r ≠ .x28) :
    (s.setReg .x25 x).setReg r v = (s.setReg r v).setReg .x25 x := by
  cases s
  cases r <;> simp_all [MachineState.setReg]
  all_goals funext current; cases current <;> rfl

private theorem x28_after_register (s : MachineState) (x v : Word) (r : Reg)
    (different : r ≠ .x28) :
    (s.setReg .x28 x).setReg r v = (s.setReg r v).setReg .x28 x := by
  cases s
  cases r <;> simp_all [MachineState.setReg]
  all_goals funext current; cases current <;> rfl

private theorem fast_path_prefix_next (s : MachineState) (level i : Nat) (inside : i < 12) :
    fastPathPrefix s level (i+1) =
      execInstrBr (fastPathPrefix s level i)
        ((fastPathInstructions level)[i]?.getD .EBREAK) := by
  have bound : i < (fastPathInstructions level).length := by
    simpa only [fastPathInstructions, List.length_cons, List.length_nil, Nat.reduceAdd] using inside
  rw [fastPathPrefix, List.take_succ_eq_append_getElem bound, List.foldl_append]
  simp only [fastPathPrefix, List.foldl_cons, List.foldl_nil,
    getElem?_pos (fastPathInstructions level) i bound, Option.getD_some]

private theorem fast_path_step_cursor (s : MachineState) (level i : Nat) (inside : i < 12) :
    (execInstrBr s ((fastPathInstructions level)[i]?.getD .EBREAK)).getReg .x25 =
      s.getReg .x25 := by
  interval_cases i <;>
    simp (disch := decide) only [fastPathInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr, MachineState.getReg_setPC,
      reg_mem, MachineState.getReg_setReg_ne]

private theorem fast_path_prefix_cursor (s : MachineState) (level i : Nat) (bound : i ≤ 12) :
    (fastPathPrefix s level i).getReg .x25 = s.getReg .x25 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [fast_path_prefix_next s level i (by omega), fast_path_step_cursor _ level i (by omega)]
    exact ih (by omega)

private theorem fast_path_frame_step (s : MachineState) (level i : Nat)
    (levelBound : level < 16) (inside : i < 12) (base counter pc : Word)
    (cursor : s.getReg .x25 = base + BitVec.ofNat 64 (32*level)) :
    execInstrBr (fastFrame s base counter pc)
        ((fastPathInstructions level)[i]?.getD .EBREAK) =
      fastFrame (execInstrBr s ((fastPathInstructions 0)[i]?.getD .EBREAK))
        base counter (pc+4) := by
  have o0 := immediate_offset level 0 levelBound (by decide)
  have o1 := immediate_offset level 1 levelBound (by decide)
  have o2 := immediate_offset level 2 levelBound (by decide)
  have o3 := immediate_offset level 3 levelBound (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1 o2 o3
  interval_cases i <;>
    simp (disch := decide) only [fastPathInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, execInstrBr, fastFrame,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      cursor, o0, o1, o2, o3, BitVec.add_assoc, BitVec.add_zero, Nat.reduceMul, Nat.reduceAdd,
      pc_after_register, pc_after_memory, get_mem_after_pc, get_mem_after_register,
      x25_after_memory, x28_after_memory, x25_after_register, x28_after_register,
      pc_set, pc_overwrite,
      show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) by decide,
      show signExtend12 (BitVec.ofNat 12 8) = (8 : Word) by decide,
      show signExtend12 (BitVec.ofNat 12 16) = (16 : Word) by decide,
      show signExtend12 (BitVec.ofNat 12 24) = (24 : Word) by decide] <;>
    (try simp only [word_ofNat_zero, word_add_zero, BitVec.add_zero,
      show (8 : Word) = 8#64 by rfl,
      show (16 : Word) = 16#64 by rfl,
      show (24 : Word) = 24#64 by rfl]) <;> rfl

private theorem fast_path_prefix_refine (s : MachineState) (level i : Nat)
    (levelBound : level < 16) (inside : i ≤ 12) (base counter pc : Word)
    (cursor : s.getReg .x25 = base + BitVec.ofNat 64 (32*level)) :
    fastPathPrefix (fastFrame s base counter pc) level i =
      fastFrame (fastPathPrefix s 0 i) base counter (pc+BitVec.ofNat 64 (4*i)) := by
  induction i with
  | zero => simp [fastPathPrefix, fastFrame]
  | succ i ih =>
    have inStep : i < 12 := by omega
    have stable := (fast_path_prefix_cursor s 0 i (by omega)).trans cursor
    rw [fast_path_prefix_next _ level i inStep, ih (by omega),
      fast_path_frame_step _ level i levelBound inStep _ _ _ stable,
      fast_path_prefix_next s 0 i inStep]
    rw [BitVec.add_assoc]
    change _ = fastFrame _ _ _ _
    have nextPC : BitVec.ofNat 64 (4*i) + (4 : Word) = BitVec.ofNat 64 (4*(i+1)) := by
      change BitVec.ofNat 64 (4*i) + BitVec.ofNat 64 4 = _
      rw [← BitVec.ofNat_add]
      congr 1 <;> omega
    rw [nextPC]

private theorem fast_reference_prefix (s : MachineState) :
    fastPathPrefix s 0 12 =
      execInstrBr (capOpenPathCopied s) (.SRLI .x20 .x20 1) := by
  have code : fastPathInstructions 0 =
      (capOpenPathInstructions ++ capDigestCopyInstructions false) ++ [.SRLI .x20 .x20 1] :=
    rfl
  have length : (fastPathInstructions 0).length ≤ 12 := by decide
  rw [fastPathPrefix, List.take_of_length_le length, code,
    List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, capOpenPathCopied, capDigestCopyPrefix,
    capOpenPathPrefix,
    show capOpenPathInstructions.take 3 = capOpenPathInstructions by rfl,
    show (capDigestCopyInstructions false).take 8 = capDigestCopyInstructions false by rfl]

private theorem frame_after_cursor (state : MachineState) (v base counter pc : Word) :
    fastFrame (state.setReg .x25 v) base counter pc = fastFrame state base counter pc := by
  simp only [fastFrame, register_overwrite]

private theorem frame_after_counter (state : MachineState) (v base counter pc : Word) :
    fastFrame (state.setReg .x28 v) base counter pc = fastFrame state base counter pc := by
  rw [fastFrame, x28_after_register state v base .x25 (by decide), register_overwrite]
  rfl

private theorem frame_drop_counter_add (state : MachineState) (imm : BitVec 12)
    (base counter pc : Word) :
    fastFrame (execInstrBr state (.ADDI .x28 .x28 imm)) base counter pc =
      fastFrame state base counter pc := by
  simp only [execInstrBr, frame_after_pc, frame_after_counter]

private theorem frame_shift_after_cursor_add (state : MachineState) (imm : BitVec 12)
    (base counter pc : Word) :
    fastFrame (execInstrBr (execInstrBr state (.ADDI .x25 .x25 imm)) (.SRLI .x20 .x20 1))
        base counter pc =
      fastFrame (execInstrBr state (.SRLI .x20 .x20 1)) base counter pc := by
  simp (disch := decide) only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne, frame_after_pc, pc_after_register,
    x25_after_register, frame_after_cursor]

private theorem fast_reference_tail (s : MachineState) (base counter pc : Word) :
    fastFrame (capOpenPathTailPrefix s 4) base counter pc =
      fastFrame (execInstrBr s (.SRLI .x20 .x20 1)) base counter pc := by
  have branch : (capOpenPathTailInstructions[3]?.getD .EBREAK) = .BNE .x28 .x0 8136 := by
    simp only [capOpenPathTailInstructions,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have stage : capOpenPathTailPrefix s 3 =
      execInstrBr (execInstrBr (execInstrBr s (.ADDI .x25 .x25 32)) (.SRLI .x20 .x20 1))
        (.ADDI .x28 .x28 4095) := by
    simp only [capOpenPathTailPrefix, capOpenPathTailInstructions, List.take, List.foldl]
  rw [cap_open_path_tail_succ _ 3 (by decide), branch, frame_branch, stage,
    frame_drop_counter_add, frame_shift_after_cursor_add]

private theorem fast_path_refine (s : MachineState) (level : Nat) (bound : level < 16)
    (base counter pc : Word) (cursor : s.getReg .x25 = base + BitVec.ofNat 64 (32*level)) :
    fastPathPrefix (fastFrame s base counter pc) level 12 =
      fastFrame (capOpenPathState s) base counter (pc+48) := by
  rw [fast_path_prefix_refine s level 12 bound (by decide) base counter pc cursor,
    fast_reference_prefix, capOpenPathState, fast_reference_tail] <;> rfl

private abbrev fastImage : Image := (capExperimental 24).image .opening

-- Normalize the assembled image once before proving the individual fetches.
private def fastImageWords : List (BitVec 32) :=
  [0x00060493, 0x00068c13, 0x00078c93, 0x00080d93, 0x00000993, 0x00b99993, 0x00498993, 0x00b99993,
   0x00098993, 0x00b99993, 0x00098993, 0x00000313, 0x00b31313, 0x10030313, 0x00b31313, 0x00030313,
   0x00b31313, 0x00030313, 0x00648933, 0x00000b13, 0x00bb1b13, 0x00eb0b13, 0x00bb1b13, 0x000b0b13,
   0x10000e93, 0x01800893, 0x00000013, 0x00100f93, 0x120d8e63, 0x000c3a03, 0x031a0333, 0x00690bb3,
   0x000bb303, 0x006cb023, 0x008bb303, 0x006cb423, 0x010bb303, 0x006cb823, 0x000cbc23, 0x00000013,
   0x020c8c93, 0x013a0a33, 0x00000e13, 0x00be1e13, 0x010e0e13, 0x040e0063, 0x1980006f, 0x00539393,
   0x00748bb3, 0x000bb303, 0x006cb023, 0x008bb303, 0x006cb423, 0x010bb303, 0x006cb823, 0x018bb303,
   0x006cbc23, 0x020c8c93, 0x001a5a13, 0xfffe0e13, 0xfc0e14e3, 0x003a1393, 0x007b0bb3, 0x01fbb023,
   0x008c0c13, 0xfffd8d93, 0xf60d96e3, 0xfffe8a13, 0x020a0663, 0x004a1f13, 0x01eb0f33, 0x000f3303,
   0x008f3383, 0x00736333, 0x003a1b93, 0x017b0bb3, 0x006bb023, 0xfffa0a13, 0xfc0a1ee3, 0x00100a13,
   0x00100f93, 0x003a1393, 0x007b0bb3, 0x000bb303, 0x00030a63, 0x03da7e63, 0x001a1a13, 0xfe9ff06f,
   0x00000013, 0x005a1393, 0x00748bb3, 0x000bb303, 0x006cb023, 0x008bb303, 0x006cb423, 0x010bb303,
   0x006cb823, 0x018bb303, 0x006cbc23, 0x020c8c93, 0x01fa0e63, 0x001a7393, 0x00038663, 0x001a5a13,
   0xff1ff06f, 0x001a0a13, 0xf9dff06f, 0x40fc85b3, 0x00100293, 0x00000513, 0x00000073, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x006cb023, 0x008bb303, 0x006cb423, 0x010bb303, 0x006cb823, 0x018bb303, 0x006cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x026cb023, 0x008bb303, 0x026cb423, 0x010bb303,
   0x026cb823, 0x018bb303, 0x026cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x046cb023, 0x008bb303, 0x046cb423, 0x010bb303, 0x046cb823, 0x018bb303, 0x046cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x066cb023, 0x008bb303, 0x066cb423, 0x010bb303,
   0x066cb823, 0x018bb303, 0x066cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x086cb023, 0x008bb303, 0x086cb423, 0x010bb303, 0x086cb823, 0x018bb303, 0x086cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x0a6cb023, 0x008bb303, 0x0a6cb423, 0x010bb303,
   0x0a6cb823, 0x018bb303, 0x0a6cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x0c6cb023, 0x008bb303, 0x0c6cb423, 0x010bb303, 0x0c6cb823, 0x018bb303, 0x0c6cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x0e6cb023, 0x008bb303, 0x0e6cb423, 0x010bb303,
   0x0e6cb823, 0x018bb303, 0x0e6cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x106cb023, 0x008bb303, 0x106cb423, 0x010bb303, 0x106cb823, 0x018bb303, 0x106cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x126cb023, 0x008bb303, 0x126cb423, 0x010bb303,
   0x126cb823, 0x018bb303, 0x126cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x146cb023, 0x008bb303, 0x146cb423, 0x010bb303, 0x146cb823, 0x018bb303, 0x146cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x166cb023, 0x008bb303, 0x166cb423, 0x010bb303,
   0x166cb823, 0x018bb303, 0x166cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x186cb023, 0x008bb303, 0x186cb423, 0x010bb303, 0x186cb823, 0x018bb303, 0x186cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x1a6cb023, 0x008bb303, 0x1a6cb423, 0x010bb303,
   0x1a6cb823, 0x018bb303, 0x1a6cbc23, 0x001a5a13, 0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303,
   0x1c6cb023, 0x008bb303, 0x1c6cb423, 0x010bb303, 0x1c6cb823, 0x018bb303, 0x1c6cbc23, 0x001a5a13,
   0x001a4393, 0x00539393, 0x00748bb3, 0x000bb303, 0x1e6cb023, 0x008bb303, 0x1e6cb423, 0x010bb303,
   0x1e6cb823, 0x018bb303, 0x1e6cbc23, 0x001a5a13, 0x200c8c93, 0x00000e13, 0xb9dff06f]

private theorem fast_image_words : fastImage.code = fastImageWords := rfl

private theorem fast_path_fetched (level i : Nat) (bound : level<16) (inside : i<12)
    (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4688+48*level+4*i)) :
    fetch fastImage s=some (.base (((fastPathInstructions level)[i]?).getD .EBREAK)) := by
  apply cap_image_fetch _ _ (148+12*level+i) _ (by omega)
  · rw [pc]
    congr 1 <;> omega
  · rw [fast_image_words]
    interval_cases level <;> interval_cases i <;> rfl

private theorem fast_path_step_pc (state : MachineState) (level i : Nat) (inside : i < 12) :
    (execInstrBr state ((fastPathInstructions level)[i]?.getD .EBREAK)).pc = state.pc + 4 := by
  interval_cases i <;>
    simp only [fastPathInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, execInstrBr, pc_set]

private theorem fast_path_pc (state : MachineState) (level i : Nat) (inside : i ≤ 12) :
    (fastPathPrefix state level i).pc = state.pc + BitVec.ofNat 64 (4*i) := by
  induction i with
  | zero => simp [fastPathPrefix]
  | succ i ih =>
    rw [fast_path_prefix_next state level i (by omega), fast_path_step_pc _ _ _ (by omega),
      ih (by omega), BitVec.add_assoc]
    change state.pc+(BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 4) = _
    rw [← BitVec.ofNat_add]
    congr 1

private theorem fast_path_source (state : MachineState) (level i : Nat)
    (low : 3 ≤ i) (high : i ≤ 12) :
    (fastPathPrefix state level i).getReg .x23 =
      state.getReg .x9+((state.getReg .x20 ^^^ 1)<<<5) := by
  have step (s : MachineState) (j : Nat) (lo : 3 ≤ j) (hi : j < 12) :
      (execInstrBr s ((fastPathInstructions level)[j]?.getD .EBREAK)).getReg .x23 =
        s.getReg .x23 := by
    interval_cases j <;>
      simp (disch := decide) only [fastPathInstructions,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some,execInstrBr,MachineState.getReg_setPC,
        reg_mem,MachineState.getReg_setReg_ne]
  have stable (count : Nat) (bound : 3+count ≤ 12) :
      (fastPathPrefix state level (3+count)).getReg .x23 =
        (fastPathPrefix state level 3).getReg .x23 := by
    induction count with
    | zero => rfl
    | succ count ih =>
      rw [show 3+(count+1) = (3+count)+1 by omega,
        fast_path_prefix_next state level (3+count) (by omega),
        step _ _ (by omega) (by omega)]
      exact ih (by omega)
  rw [show i = 3+(i-3) by omega, stable (i-3) (by omega)]
  simp (disch := decide) only [fastPathPrefix,fastPathInstructions,List.take,List.foldl,
    execInstrBr,signExtend12,MachineState.getReg_setPC,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, show (5 : BitVec 6).toNat = 5 by decide] <;> rfl

private theorem fast_access_valid (level i : Nat) (bound : level<16) (hi : i < 12)
    (s : MachineState)
    (sourceValid : ∀ word : Fin 4,accessValid
      (s.getReg .x9+((s.getReg .x20 ^^^ 1)<<<5)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (s.getReg .x25+BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 (8*word.val)) 8=true)
    : memoryArgumentsValid (fastPathPrefix s level i)
        (((fastPathInstructions level)[i]?).getD .EBREAK) = true := by
  have destination (j : Nat) (hj : j≤11) :=
    fast_path_prefix_cursor s level j (by omega)
  have source (j : Nat) (hj : 3≤j ∧ j≤11) :=
    fast_path_source s level j hj.1 (by omega)
  have s0 := sourceValid ⟨0,by decide⟩
  have s1 := sourceValid ⟨1,by decide⟩
  have s2 := sourceValid ⟨2,by decide⟩
  have s3 := sourceValid ⟨3,by decide⟩
  have d0 := destinationValid ⟨0,by decide⟩
  have d1 := destinationValid ⟨1,by decide⟩
  have d2 := destinationValid ⟨2,by decide⟩
  have d3 := destinationValid ⟨3,by decide⟩
  have off0 := immediate_offset level 0 bound (by decide)
  have off1 := immediate_offset level 1 bound (by decide)
  have off2 := immediate_offset level 2 bound (by decide)
  have off3 := immediate_offset level 3 bound (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at off0 off1 off2 off3
  interval_cases i <;>
    simp only [fastPathInstructions,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,memoryArgumentsValid,memAccess,
      source 3 (by decide),source 5 (by decide),source 7 (by decide),source 9 (by decide),
      destination 4 (by decide),destination 6 (by decide),
      destination 8 (by decide),destination 10 (by decide),
      off0,off1,off2,off3,
      show signExtend12 0=(0#64) by decide,
      show signExtend12 8=(8#64) by decide,
      show signExtend12 16=(16#64) by decide,
      show signExtend12 24=(24#64) by decide,
      word_ofNat_zero,word_add_zero,BitVec.add_zero,BitVec.add_assoc]
  case «3» => simpa only [Fin.val_mk,Nat.mul_zero,word_ofNat_zero,BitVec.add_zero] using s0
  case «4» => simpa only [Fin.val_mk,Nat.mul_zero,word_ofNat_zero,BitVec.add_zero] using d0
  case «5» => simpa only [BitVec.add_assoc] using s1
  case «6» => simpa only [BitVec.add_assoc] using d1
  case «7» => simpa only [BitVec.add_assoc] using s2
  case «8» => simpa only [BitVec.add_assoc] using d2
  case «9» => simpa only [BitVec.add_assoc] using s3
  case «10» => simpa only [BitVec.add_assoc] using d3

private theorem fast_step_execute (level : Nat) (bound : level<16) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4688+48*level))
    (sourceValid : ∀ word : Fin 4,accessValid
      (s.getReg .x9+((s.getReg .x20 ^^^ 1)<<<5)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid
      (s.getReg .x25+BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (12+fuel) s coins=
      (do let result ← execute fastImage fuel (fastPathPrefix s level 12) coins
          return result.charge 12 0) := by
  apply execute_unit_steps (states := fastPathPrefix s level)
  intro i hi
  refine ⟨.base (((fastPathInstructions level)[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fast_path_fetched level i bound hi
    rw [fast_path_pc s level i (by omega),pc,←BitVec.ofNat_add]
  · have valid := fast_access_valid level i bound hi s sourceValid destinationValid
    rw [fast_path_prefix_next s level i hi]
    interval_cases i <;>
      simp only [fastPathInstructions,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep,valid,↓reduceIte]
  · interval_cases i <;> rfl

private theorem frame_first (state : MachineState) :
    fastFrame state (state.getReg .x25) (state.getReg .x28) 4688 = state.setPC 4688 := by
  cases state
  simp [fastFrame, MachineState.setReg, MachineState.getReg, MachineState.setPC]
  funext reg
  cases reg <;> rfl

private theorem frame_register (state : MachineState) (base counter pc : Word) (reg : Reg)
    (h25 : reg ≠ .x25) (h28 : reg ≠ .x28) :
    (fastFrame state base counter pc).getReg reg = state.getReg reg := by
  simp only [fastFrame, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h25)]

private theorem frame_output (state : MachineState) (base counter pc : Word) :
    (fastFrame state base counter pc).getReg .x25 = base := by
  simp (disch := decide) only [fastFrame, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

@[simp] private theorem set_reg_zero (state : MachineState) (value : Word) :
    state.setReg .x0 value = state := rfl

@[simp] private theorem get_reg_zero (state : MachineState) : state.getReg .x0 = 0 := rfl

private theorem fast_enter (state : MachineState) (pc : state.pc = 4280)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (1+fuel) state coins =
      (do let result ← execute fastImage fuel (state.setPC 4688) coins
          return result.charge 1 0) := by
  have checked : fetch fastImage state = some (.base (.JAL .x0 408)) := by
    apply cap_image_fetch _ state 46 _ (by decide) pc
    rw [fast_image_words] <;> rfl
  have action : ordinaryStep state (.base (.JAL .x0 408)) = some (state.setPC 4688) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ↓reduceIte, execInstrBr,
      set_reg_zero, pc] <;> rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ checked action] <;> rfl

private def fastExitInstructions : List Instr :=
  [.ADDI .x25 .x25 512, .ADDI .x28 .x0 0, .JAL .x0 (BitVec.ofInt 21 (-1124))]

private def fastExitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (fastExitInstructions.take count).foldl execInstrBr state

private theorem fast_exit (state : MachineState) (base counter : Word)
    (cursor : state.getReg .x25 = base+512) (counterZero : state.getReg .x28 = 0)
    (pc : state.pc = 4340) (fuel : Nat) (coins : Bool) :
    execute fastImage (3+fuel) (fastFrame state base counter 5456) coins =
      (do let result ← execute fastImage fuel state coins
          return result.charge 3 0) := by
  let initial := fastFrame state base counter 5456
  have final : fastExitPrefix initial 3 = state := by
    have output : initial.getReg .x25 = base := frame_output state base counter 5456
    simp only [fastExitPrefix, fastExitInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, set_reg_zero, get_reg_zero, BitVec.zero_add, word_zero_add, output, pc_set,
      show initial.pc = 5456 by rfl,
      show signExtend12 (512 : BitVec 12) = (512 : Word) by decide,
      show signExtend12 (0 : BitVec 12) = (0 : Word) by decide,
      show signExtend21 (BitVec.ofInt 21 (-1124)) = (BitVec.ofInt 64 (-1124)) by decide,
      show (5456 : Word)+4+4+BitVec.ofInt 64 (-1124) = 4340 by decide]
    rw [← cursor, ← counterZero]
    cases state
    simp [initial, fastFrame, MachineState.setReg, MachineState.getReg,
      MachineState.setPC] at *
    constructor
    · funext reg
      cases reg <;> rfl
    · exact pc.symm
  have run : execute fastImage (3+fuel) initial coins =
      (do let result ← execute fastImage fuel (fastExitPrefix initial 3) coins
          return result.charge 3 0) := by
    apply execute_unit_steps (states := fastExitPrefix initial)
    intro i hi
    refine ⟨.base ((fastExitInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply cap_image_fetch _ _ (340+i) _ (by omega)
      · interval_cases i <;> rfl
      · rw [fast_image_words]
        interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  rw [final] at run
  exact run

private theorem fast_frame_pc (state : MachineState) (base counter pc : Word) :
    (fastFrame state base counter pc).pc = pc := rfl

attribute [local irreducible] fastFrame fastPathPrefix capOpenPathState capCountedRun

private theorem fast_path_run (rootBase limit : Nat)
    (rootBound : rootBase + 1073741824 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0) (limitBound : limit ≤ MEMORY_BYTES)
    (remaining level : Nat) (state : MachineState) (base counter : Word)
    (span : level+remaining = 16) (ready : CapOpenPathReady rootBase limit remaining state)
    (cursor : state.getReg .x25 = base+BitVec.ofNat 64 (32*level))
    (fuel : Nat) (coins : Bool) :
    execute fastImage (12*remaining+fuel)
        (fastFrame state base counter (BitVec.ofNat 64 (4688+48*level))) coins =
      (do let result ← execute fastImage fuel
            (fastFrame (capCountedRun capOpenPathState remaining state) base counter 5456) coins
          return result.charge (12*remaining) 0) := by
  induction remaining generalizing level state with
  | zero =>
    have : level = 16 := by omega
    subst level
    simp [capCountedRun.eq_1, Execution.charge]
  | succ remaining ih =>
    obtain ⟨node, nodeBound, index⟩ := ready.node
    obtain ⟨output, pointer, outputAligned, space⟩ := ready.cursor
    have sibling : node ^^^ 1 < 33554432 :=
      Nat.xor_lt_two_pow (n := 25) nodeBound (by decide)
    have accessed := cap_open_path_copy_access state node rootBase output index ready.roots pointer
      (by omega) rootAligned (by omega) outputAligned
    have sourceAddress : (capOpenPathPrefix state 3).getReg .x23 =
        state.getReg .x9 + ((state.getReg .x20 ^^^ 1) <<< 5) := by
      simp (disch := decide) only [capOpenPathPrefix,capOpenPathInstructions,List.take,List.foldl,
        execInstrBr,signExtend12,MachineState.getReg_setPC,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,
        show (5 : BitVec 6).toNat = 5 by decide] <;> rfl
    have destAddress := cap_open_path_prepare_register state 3 (by decide) .x25 (by decide)
    let pc := BitVec.ofNat 64 (4688+48*level)
    have run := fast_step_execute level (by omega) (fastFrame state base counter pc)
      (fast_frame_pc state base counter pc)
      (by
        intro word
        rw [frame_register _ _ _ _ .x9 (by decide) (by decide),
          frame_register _ _ _ _ .x20 (by decide) (by decide), ← sourceAddress]
        exact accessed.1 word)
      (by
        intro word
        rw [frame_output, ← cursor, ← destAddress]
        exact accessed.2 word)
      (12*remaining+fuel) coins
    have nextCursor : (capOpenPathState state).getReg .x25 =
        base+BitVec.ofNat 64 (32*(level+1)) := by
      rw [(cap_open_path_projection state).1, cursor, BitVec.add_assoc]
      change base+(BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 32) = _
      rw [← BitVec.ofNat_add]
      congr 1 <;> omega
    have nextPC : pc+48 = BitVec.ofNat 64 (4688+48*(level+1)) := by
      change BitVec.ofNat 64 (4688+48*level)+BitVec.ofNat 64 48 = _
      rw [← BitVec.ofNat_add]
      congr 1 <;> omega
    rw [fast_path_refine state level (by omega) base counter pc cursor, nextPC] at run
    rw [show 12*(remaining+1)+fuel = 12+(12*remaining+fuel) by omega, run,
      ih (level+1) _ (by omega) (cap_open_path_ready_next rootBase limit remaining state
        limitBound ready) nextCursor]
    simp [capCountedRun.eq_2, Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add]

theorem cap_fast_path_execute (rootBase limit : Nat)
    (rootBound : rootBase + 1073741824 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0) (limitBound : limit ≤ MEMORY_BYTES)
    (state : MachineState) (ready : CapOpenPathReady rootBase limit 16 state)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (196+fuel) state coins =
      (do let result ← execute fastImage fuel
            (capCountedRun capOpenPathState 16 state) coins
          return result.charge 196 0) := by
  have run := fast_path_run rootBase limit rootBound rootAligned limitBound 16 0
    state (state.getReg .x25) (state.getReg .x28) (by decide) ready
    (by simp) (3+fuel) coins
  rw [show BitVec.ofNat 64 (4688 + 48 * 0) = 4688 by rfl, frame_first] at run
  let final := capCountedRun capOpenPathState 16 state
  have finished := cap_open_path_loop_finished rootBase limit limitBound 16 state ready
  have cursor : final.getReg .x25 = state.getReg .x25+512 :=
    cap_open_path_loop_cursor 16 state
  have exit := fast_exit final (state.getReg .x25) (state.getReg .x28) cursor
    finished.2 finished.1 fuel coins
  rw [show 196+fuel = 1+(12*16+(3+fuel)) by omega,
    fast_enter state (by simpa using ready.pc), run]
  rw [show capCountedRun capOpenPathState 16 state = final by rfl, exit]
  simp [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end CommitGolfCandidate
