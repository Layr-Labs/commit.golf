import CommitGolfCandidate.PairCheckRecordLeafEvenSpec

/-! # Pair-heads checker: the even leaf path (words 494–542), proof of `EvenPathFacts`

The path splits into the head (words 494–496), the first call (497), the middle (498–540: three setup
instructions, 19 two-instruction moves, two argument instructions), the second call (541) and the jump (542).
The moves are handled by induction on the move count (`evenMoves`). -/

namespace TwoPermutationPrototype.PairCk.Packed.RecordLeaf
open TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.PairCk.Packed.Checker (pairImage fetch_wide Hop Hop.thenDo)
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! ## Instruction semantics -/

private theorem even_exec_addi (s : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    execInstrBr s (.ADDI rd rs imm) = (s.setReg rd (s.getReg rs + signExtend12 imm)).setPC (s.pc + 4) := rfl

private theorem even_exec_ld (s : MachineState) (rd rs : Reg) (off : BitVec 12) :
    execInstrBr s (.LD rd rs off) = (s.setReg rd (s.getMem (s.getReg rs + signExtend12 off))).setPC (s.pc + 4) := rfl

private theorem even_exec_sd (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) :
    execInstrBr s (.SD rs1 rs2 off) = (s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4) :=
  rfl

private theorem even_exec_lui (s : MachineState) (rd : Reg) (imm : BitVec 20) :
    execInstrBr s (.LUI rd imm) =
      (s.setReg rd (((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)).setPC (s.pc + 4) := rfl

private theorem even_exec_jal (s : MachineState) (rd : Reg) (off : BitVec 21) :
    execInstrBr s (.JAL rd off) = (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 off) := rfl

private theorem even_get_reg (s : MachineState) (rd rs : Reg) (value : Word) :
    (s.setReg rd value).getReg rs = if rd = rs ∧ rd ≠ .x0 then value else s.getReg rs :=
  Opening.getReg_setReg s rd rs value

private theorem even_view_set_pc (s : MachineState) (v : Word) : memoryView (s.setPC v) = memoryView s := rfl

private theorem even_view_set_reg (s : MachineState) (r : Reg) (v : Word) :
    memoryView (s.setReg r v) = memoryView s := by
  funext w
  cases r <;> rfl

private theorem even_mem_set_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

private theorem even_sext_zero : signExtend12 0#12 = 0#64 := by decide

private theorem even_add_word (a b : Nat) : wordAddress a + BitVec.ofNat 64 (8*b) = wordAddress (a+b) :=
  (wordAddress_add a b).symm

private theorem even_pc_step (n k : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 k = BitVec.ofNat 64 (n+k) :=
  (BitVec.ofNat_add n k).symm

private theorem even_pc_four (n : Nat) : BitVec.ofNat 64 n + 4 = BitVec.ofNat 64 (n+4) :=
  even_pc_step n 4

/-- One ordinary instruction at word `k` as a `Hop`. -/
private theorem even_step (s : MachineState) (k : Nat) (instr : Instr) (bounded : k < 543)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*k))
    (decoded : (pairImage.code[k]?).bind decodeInstruction = some (.base instr))
    (stepped : ordinaryStep s (.base instr) = some (execInstrBr s instr))
    (cost : instructionCycles (.base instr) = 1) :
    Hop s (execInstrBr s instr) 1 1 := by
  intro fuel
  rw [Nat.add_comm, execute_ordinary_step pairImage (.base instr) s _ fuel false
    (fetch_wide s k instr bounded pc decoded) stepped, cost]

private theorem even_step_ld (s : MachineState) (rd rs : Reg) (off : BitVec 12)
    (valid : accessValid (s.getReg rs + signExtend12 off) 8 = true) :
    ordinaryStep s (.base (.LD rd rs off)) = some (execInstrBr s (.LD rd rs off)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]

private theorem even_step_sd (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12)
    (valid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    ordinaryStep s (.base (.SD rs1 rs2 off)) = some (execInstrBr s (.SD rs1 rs2 off)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, valid]

/-! ## Head (words 494–496) -/

private theorem even_lui_value :
    ((((256 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 : Word) = wordAddress 131072 := by
  decide

private theorem even_head_unfold (state : MachineState) :
    evenHead state =
      let s1 := (state.setReg .x30 (wordAddress 131072)).setPC (state.pc + 4)
      let s2 := (s1.setReg .x10 (s1.getReg .x10 + signExtend12 96)).setPC (s1.pc + 4)
      (s2.setReg .x12 (s2.getReg .x30 + signExtend12 3944)).setPC (s2.pc + 4) := by
  simp only [evenHead, evenHeadCode, List.foldl, even_exec_lui, even_exec_addi, even_lui_value]

theorem even_head_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x30) :
    (evenHead state).getReg reg = state.getReg reg := by
  rw [even_head_unfold]
  simp [even_get_reg, Ne.symm a, Ne.symm b, Ne.symm c]

theorem even_head_view (state : MachineState) : memoryView (evenHead state) = memoryView state := by
  rw [even_head_unfold]
  simp only [even_view_set_pc, even_view_set_reg]

theorem even_head_base (state : MachineState) : (evenHead state).getReg .x30 = wordAddress 131072 := by
  rw [even_head_unfold]
  simp [even_get_reg]

theorem even_head_output (state : MachineState) : (evenHead state).getReg .x12 = wordAddress 131053 := by
  rw [even_head_unfold]
  simp [even_get_reg]
  decide

theorem even_head_input (state : MachineState) :
    (evenHead state).getReg .x10 = state.getReg .x10 + BitVec.ofNat 64 (8*12) := by
  rw [even_head_unfold]
  simp [even_get_reg]
  decide

theorem even_head_pc (state : MachineState) : (evenHead state).pc = state.pc + 4 + 4 + 4 := by
  rw [even_head_unfold]
  rfl


/-! ## Middle (words 498–540): setup, 19 moves, arguments -/

private def evenPre (u : MachineState) : MachineState :=
  [Instr.ADDI .x10 .x10 4000, .ADDI .x31 .x28 4088, .SD .x30 .x31 0].foldl execInstrBr u

private def evenMoves (u : MachineState) (j : Nat) : MachineState :=
  ((List.range j).flatMap evenMoveCode).foldl execInstrBr (evenPre u)

private def evenPost (m : MachineState) : MachineState :=
  [Instr.ADDI .x10 .x30 0, .ADDI .x12 .x23 0].foldl execInstrBr m

private theorem even_middle_split (u : MachineState) : evenMiddle u = evenPost (evenMoves u 19) := by
  simp only [evenMiddle, evenMiddleCode, evenPost, evenMoves, evenPre, List.foldl_append]

private theorem even_moves_succ (u : MachineState) (j : Nat) :
    evenMoves u (j+1) = (evenMoveCode j).foldl execInstrBr (evenMoves u j) := by
  simp only [evenMoves, List.range_succ, List.flatMap_append, List.foldl_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The word that move `j` reads. -/
private def evenMoveSource (src nonce j : Nat) : Nat := if j < 17 then src+5+j else nonce+(j-17)

private theorem even_imm_load (j : Nat) (small : j < 17) :
    signExtend12 (BitVec.ofNat 12 (40+8*j)) = BitVec.ofNat 64 (8*(5+j)) := by
  interval_cases j <;> decide

private theorem even_imm_salt (j : Nat) (small : j < 2) :
    signExtend12 (BitVec.ofNat 12 (8*j)) = BitVec.ofNat 64 (8*j) := by
  interval_cases j <;> decide

private theorem even_store_address (j : Nat) (small : j < 19) :
    wordAddress 131072 + signExtend12 (BitVec.ofNat 12 (48+8*j)) = wordAddress (131078+j) := by
  interval_cases j <;> decide

private theorem even_view_sd (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) (a : Nat) (small : a < 2^61)
    (address : s.getReg rs1 + signExtend12 off = wordAddress a) (word : Nat) (bounded : word < 2^61) :
    memoryView (execInstrBr s (.SD rs1 rs2 off)) word = writeWord (memoryView s) a (s.getReg rs2) word := by
  rw [even_exec_sd, even_view_set_pc, address, memory_at_store small bounded]

private theorem even_view_ld (s : MachineState) (rd rs : Reg) (off : BitVec 12) :
    memoryView (execInstrBr s (.LD rd rs off)) = memoryView s := by
  rw [even_exec_ld, even_view_set_pc, even_view_set_reg]

private theorem even_ld_value (s : MachineState) (rs : Reg) (off : BitVec 12) (a : Nat)
    (address : s.getReg rs + signExtend12 off = wordAddress a) :
    (execInstrBr s (.LD .x31 rs off)).getReg .x31 = memoryView s a := by
  rw [even_exec_ld, MachineState.getReg_setPC, even_get_reg, address]
  rfl

private theorem even_ld_register (s : MachineState) (rd rs reg : Reg) (off : BitVec 12) (other : rd ≠ reg) :
    (execInstrBr s (.LD rd rs off)).getReg reg = s.getReg reg := by
  rw [even_exec_ld, MachineState.getReg_setPC, even_get_reg, if_neg (fun h => other h.1)]

private theorem even_load_address (m : MachineState) (j src nonce : Nat) (small : j < 19)
    (source : m.getReg .x10 = wordAddress src) (proofPointer : m.getReg .x4 = wordAddress nonce) :
    (if j < 17 then m.getReg .x10 + signExtend12 (BitVec.ofNat 12 (40+8*j))
      else m.getReg .x4 + signExtend12 (BitVec.ofNat 12 (8*(j-17)))) = wordAddress (evenMoveSource src nonce j) := by
  unfold evenMoveSource
  by_cases low : j < 17
  · rw [if_pos low, if_pos low, source, even_imm_load j low, even_add_word, Nat.add_assoc]
  · rw [if_neg low, if_neg low, proofPointer, even_imm_salt (j-17) (by omega), even_add_word]

/-- Move `j` as two concrete instructions. -/
private theorem even_move_code (j : Nat) :
    evenMoveCode j =
      [.LD .x31 (if j < 17 then .x10 else .x4)
          (if j < 17 then BitVec.ofNat 12 (40+8*j) else BitVec.ofNat 12 (8*(j-17))),
       .SD .x30 .x31 (BitVec.ofNat 12 (48+8*j))] := by
  unfold evenMoveCode
  by_cases low : j < 17
  · simp only [if_pos low]
  · simp only [if_neg low]

private theorem even_move_view (m : MachineState) (j : Nat) (src nonce : Nat) (small : j < 19)
    (source : m.getReg .x10 = wordAddress src) (proofPointer : m.getReg .x4 = wordAddress nonce)
    (base : m.getReg .x30 = wordAddress 131072) (word : Nat) (bounded : word < 2^61) :
    memoryView ((evenMoveCode j).foldl execInstrBr m) word =
      writeWord (memoryView m) (131078+j) (memoryView m (evenMoveSource src nonce j)) word := by
  rw [even_move_code]
  simp only [List.foldl]
  have loadAt : (if j < 17 then m.getReg .x10 else m.getReg .x4) +
      signExtend12 (if j < 17 then BitVec.ofNat 12 (40+8*j) else BitVec.ofNat 12 (8*(j-17))) =
        wordAddress (evenMoveSource src nonce j) := by
    rw [← even_load_address m j src nonce small source proofPointer]
    by_cases low : j < 17
    · rw [if_pos low, if_pos low, if_pos low]
    · rw [if_neg low, if_neg low, if_neg low]
  have regAt : (if j < 17 then m.getReg .x10 else m.getReg .x4) = m.getReg (if j < 17 then .x10 else .x4) := by
    by_cases low : j < 17
    · rw [if_pos low, if_pos low]
    · rw [if_neg low, if_neg low]
  rw [regAt] at loadAt
  rw [even_view_sd _ _ _ _ (131078+j) (by omega) _ word bounded, even_view_ld,
    even_ld_value _ _ _ _ loadAt]
  rw [even_ld_register _ _ _ _ _ (by decide), base, even_store_address j small]

private theorem even_move_register (m : MachineState) (j : Nat) (reg : Reg) (other : reg ≠ .x31) :
    ((evenMoveCode j).foldl execInstrBr m).getReg reg = m.getReg reg := by
  by_cases low : j < 17
  · rw [evenMoveCode, if_pos low]
    simp [List.foldl, even_exec_ld, even_exec_sd, even_get_reg, Opening.getReg_setMem, Ne.symm other]
  · rw [evenMoveCode, if_neg low]
    simp [List.foldl, even_exec_ld, even_exec_sd, even_get_reg, Opening.getReg_setMem, Ne.symm other]

private theorem even_move_pc (m : MachineState) (j : Nat) :
    ((evenMoveCode j).foldl execInstrBr m).pc = m.pc + 4 + 4 := by
  by_cases low : j < 17
  · rw [evenMoveCode, if_pos low]
    rfl
  · rw [evenMoveCode, if_neg low]
    rfl

private theorem even_moves_register (u : MachineState) (j : Nat) (reg : Reg) (other : reg ≠ .x31) :
    (evenMoves u j).getReg reg = (evenPre u).getReg reg := by
  induction j with
  | zero => rfl
  | succ j ih => rw [even_moves_succ, even_move_register _ _ _ other, ih]

private theorem even_moves_pc (u : MachineState) (n : Nat) (pc : (evenPre u).pc = BitVec.ofNat 64 n) (j : Nat) :
    (evenMoves u j).pc = BitVec.ofNat 64 (n+8*j) := by
  induction j with
  | zero => exact pc
  | succ j ih =>
    rw [even_moves_succ, even_move_pc, ih, even_pc_four, even_pc_four]
    congr 1

private theorem even_pre_unfold (u : MachineState) :
    evenPre u =
      let s1 := (u.setReg .x10 (u.getReg .x10 + signExtend12 4000)).setPC (u.pc + 4)
      let s2 := (s1.setReg .x31 (s1.getReg .x28 + signExtend12 4088)).setPC (s1.pc + 4)
      (s2.setMem (s2.getReg .x30 + signExtend12 0) (s2.getReg .x31)).setPC (s2.pc + 4) := rfl

private theorem even_pre_register (u : MachineState) (reg : Reg) (a : reg ≠ .x10) (b : reg ≠ .x31) :
    (evenPre u).getReg reg = u.getReg reg := by
  rw [even_pre_unfold]
  simp [even_get_reg, Opening.getReg_setMem, Ne.symm a, Ne.symm b]

private theorem even_pre_source (u : MachineState) :
    (evenPre u).getReg .x10 = u.getReg .x10 + signExtend12 4000 := by
  rw [even_pre_unfold]
  simp [even_get_reg, Opening.getReg_setMem]

private theorem even_pre_pc (u : MachineState) : (evenPre u).pc = u.pc + 4 + 4 + 4 := rfl

private theorem even_pre_view (u : MachineState) (base : u.getReg .x30 = wordAddress 131072) (word : Nat)
    (bounded : word < 2^61) :
    memoryView (evenPre u) word = writeWord (memoryView u) 131072 (u.getReg .x28 + signExtend12 4088) word := by
  let s1 := execInstrBr u (.ADDI .x10 .x10 4000)
  let s2 := execInstrBr s1 (.ADDI .x31 .x28 4088)
  have address : s2.getReg .x30 + signExtend12 0 = wordAddress 131072 := by
    simp [s1, s2, even_exec_addi, even_get_reg, base, even_sext_zero]
  have value : s2.getReg .x31 = u.getReg .x28 + signExtend12 4088 := by
    simp [s1, s2, even_exec_addi, even_get_reg]
  have view : memoryView s2 = memoryView u := by
    simp only [s1, s2, even_exec_addi, even_view_set_pc, even_view_set_reg]
  change memoryView (execInstrBr s2 (.SD .x30 .x31 0)) word = _
  rw [even_view_sd s2 .x30 .x31 0 131072 (by decide) address word bounded, value, view]

private theorem even_post_register (m : MachineState) (reg : Reg) (a : reg ≠ .x10) (b : reg ≠ .x12) :
    (evenPost m).getReg reg = m.getReg reg := by
  simp [evenPost, List.foldl, even_exec_addi, even_get_reg, Ne.symm a, Ne.symm b]

private theorem even_post_args (m : MachineState) :
    (evenPost m).getReg .x10 = m.getReg .x30 ∧ (evenPost m).getReg .x12 = m.getReg .x23 := by
  simp [evenPost, List.foldl, even_exec_addi, even_get_reg, even_sext_zero]

private theorem even_post_view (m : MachineState) : memoryView (evenPost m) = memoryView m := by
  simp only [evenPost, List.foldl, even_exec_addi, even_view_set_pc, even_view_set_reg]

private theorem even_post_pc (m : MachineState) : (evenPost m).pc = m.pc + 4 + 4 := rfl

theorem even_middle_register (u : MachineState) (reg : Reg) (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x31) :
    (evenMiddle u).getReg reg = u.getReg reg := by
  rw [even_middle_split, even_post_register _ _ a b, even_moves_register _ _ _ c, even_pre_register _ _ a c]

theorem even_middle_args (u : MachineState) :
    (evenMiddle u).getReg .x10 = u.getReg .x30 ∧ (evenMiddle u).getReg .x12 = u.getReg .x23 := by
  rw [even_middle_split, (even_post_args _).1, (even_post_args _).2,
    even_moves_register _ _ _ (by decide), even_moves_register _ _ _ (by decide),
    even_pre_register _ _ (by decide) (by decide), even_pre_register _ _ (by decide) (by decide)]
  exact ⟨rfl, rfl⟩

theorem even_middle_pc (u : MachineState) (pc : u.pc = BitVec.ofNat 64 (4096+4*498)) :
    (evenMiddle u).pc = BitVec.ofNat 64 (4096+4*541) := by
  have pre : (evenPre u).pc = BitVec.ofNat 64 (4096+4*501) := by
    rw [even_pre_pc, pc]
    rfl
  rw [even_middle_split, even_post_pc, even_moves_pc u _ pre]
  rfl

/-! ## `register` and `pc` -/

private theorem even_write_pc {bits : Nat} (s : MachineState) (address : Word) (answer : BitVec bits) :
    (writeBits s address answer).pc = s.pc + 4 := rfl

theorem even_final_register (state : MachineState) (first second : Block) (reg : Reg)
    (a : reg ≠ .x10) (b : reg ≠ .x12) (c : reg ≠ .x30) (d : reg ≠ .x31) :
    (evenFinal state first second).getReg reg = state.getReg reg := by
  unfold evenFinal evenFirstState
  rw [evenJump, even_exec_jal, MachineState.getReg_setPC]
  change (writeBits (evenMiddle (writeBits (evenHead state) (wordAddress 131053) first)) (wordAddress 1536)
    second).getReg reg = _
  rw [writeBits_register, even_middle_register _ _ a b d, writeBits_register, even_head_register _ _ a b c]

theorem even_final_pc {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (first second : Block) :
    (evenFinal state first second).pc = 0x10e8 := by
  have start : (evenFirstState state first).pc = BitVec.ofNat 64 (4096+4*498) := by
    unfold evenFirstState
    rw [even_write_pc, even_head_pc, ready.pc]
    rfl
  change (writeBits (evenMiddle (evenFirstState state first)) (wordAddress 1536) second).pc +
    signExtend21 2095216 = 0x10e8
  rw [even_write_pc, even_middle_pc _ start]
  decide


/-! ## Memory of the middle -/

private theorem even_moves_view (u : MachineState) (src nonce : Nat)
    (source : (evenPre u).getReg .x10 = wordAddress src) (proofPointer : (evenPre u).getReg .x4 = wordAddress nonce)
    (base : (evenPre u).getReg .x30 = wordAddress 131072) (high : 131097 ≤ src) (room : src + 37 ≤ 2^33)
    (low : nonce + 2 ≤ 1536) (j : Nat) (small : j ≤ 19) (word : Nat) (bounded : word < 2^61) :
    memoryView (evenMoves u j) word =
      if 131078 ≤ word ∧ word < 131078+j then memoryView (evenPre u) (evenMoveSource src nonce (word-131078))
      else memoryView (evenPre u) word := by
  induction j generalizing word with
  | zero =>
    rw [if_neg (by omega)]
    rfl
  | succ j ih =>
    have regs (r : Reg) (other : r ≠ .x31) := even_moves_register u j r other
    rw [even_moves_succ, even_move_view _ j src nonce (by omega) ((regs _ (by decide)).trans source)
      ((regs _ (by decide)).trans proofPointer) ((regs _ (by decide)).trans base) word bounded]
    have sourceBound : evenMoveSource src nonce j < 2^61 := by
      unfold evenMoveSource; split <;> omega
    have sourceOut : ¬(131078 ≤ evenMoveSource src nonce j ∧ evenMoveSource src nonce j < 131078 + j) := by
      unfold evenMoveSource; split <;> omega
    rw [ih (by omega) _ sourceBound, if_neg sourceOut, writeWord]
    by_cases hit : word = 131078 + j
    · subst hit
      rw [if_pos rfl, if_pos (by omega), show 131078 + j - 131078 = j by omega]
    · rw [if_neg hit, ih (by omega) word bounded]
      by_cases inside : 131078 ≤ word ∧ word < 131078 + j
      · rw [if_pos inside, if_pos (by omega)]
      · rw [if_neg inside, if_neg (by omega)]

/-! ## Entry facts after the head and the first reply -/

private theorem even_first_register (state : MachineState) (a : Block) (reg : Reg) :
    (evenFirstState state a).getReg reg = (evenHead state).getReg reg :=
  writeBits_register _ _ _ _

private theorem even_first_view (state : MachineState) (a : Block) (word : Nat) (bounded : word < 2^33) :
    memoryView (evenFirstState state a) word = writeWindow (memoryView state) 131053 (replyWords a) word := by
  unfold evenFirstState
  change BitVec 1600 at a
  change memoryView (writeBits (evenHead state) (wordAddress 131053) a) word = _
  rw [permutation_write_memory _ 131053 word a (by decide) bounded, even_head_view]

private theorem even_first_pc {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (a : Block) :
    (evenFirstState state a).pc = BitVec.ofNat 64 (4096+4*498) := by
  unfold evenFirstState
  rw [even_write_pc, even_head_pc, ready.pc]
  rfl

private theorem even_first_keep {state : MachineState} (a : Block) (reg : Reg)
    (x : reg ≠ .x10) (y : reg ≠ .x12) (z : reg ≠ .x30) :
    (evenFirstState state a).getReg reg = state.getReg reg :=
  (even_first_register state a reg).trans (even_head_register state reg x y z)

private theorem even_first_base (state : MachineState) (a : Block) :
    (evenFirstState state a).getReg .x30 = wordAddress 131072 :=
  (even_first_register state a _).trans (even_head_base state)

private theorem even_pre_facts {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (a : Block) :
    let u := evenFirstState state a
    (evenPre u).getReg .x10 = wordAddress src ∧ (evenPre u).getReg .x4 = wordAddress nonce ∧
      (evenPre u).getReg .x30 = wordAddress 131072 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [even_pre_source, even_first_register, even_head_input, ready.source, BitVec.add_assoc,
      show BitVec.ofNat 64 (8*12) + signExtend12 4000 = 0#64 by decide, BitVec.add_zero]
  · rw [even_pre_register _ _ (by decide) (by decide), even_first_keep a _ (by decide) (by decide) (by decide),
      ready.proofPointer]
  · rw [even_pre_register _ _ (by decide) (by decide), even_first_base]

private theorem even_tag (index : Index) : firstTag index.val + signExtend12 4088 = evenPositionTag index := by
  have split : firstTag index.val = evenPositionTag index + BitVec.ofNat 64 8 := by
    unfold firstTag evenPositionTag
    rw [even_pc_step]
    congr 1
    omega
  rw [split, BitVec.add_assoc, show BitVec.ofNat 64 8 + signExtend12 4088 = 0#64 by decide, BitVec.add_zero]

private theorem even_first_input (state : MachineState) (src : Nat) :
    window (memoryView (evenHead state)) (src+12) = evenFirstInput (window (memoryView state) (src+5)) := by
  funext i
  rw [even_head_view]
  change memoryView state (src+12+i.val) = memoryView state (src+5+(i.val+7))
  congr 1
  omega

theorem even_second_input {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (a : Block) :
    window (memoryView (evenMiddle (evenFirstState state a))) 131072 =
      evenSecondInput index (checkerNonce state) (replyWords a) (window (memoryView state) (src+5)) := by
  funext i
  have bounded := i.isLt
  have high := ready.srcHigh
  have room := ready.endBound
  have low := ready.nonceRange
  obtain ⟨preSource, preNonce, preBase⟩ := even_pre_facts ready a
  let u := evenFirstState state a
  have uBase : u.getReg .x30 = wordAddress 131072 := even_first_base state a
  have uTag : u.getReg .x28 = firstTag index.val :=
    (even_first_keep a _ (by decide) (by decide) (by decide)).trans ready.tag
  change memoryView (evenMiddle u) (131072+i.val) = _
  rw [even_middle_split, even_post_view,
    even_moves_view u src nonce preSource preNonce preBase high room low 19 le_rfl _ (by omega)]
  unfold evenSecondInput
  by_cases moved : 131078 ≤ 131072 + i.val ∧ 131072 + i.val < 131078 + 19
  · rw [if_pos moved, if_neg (by omega : ¬i.val = 0), dif_neg (by omega : ¬i.val < 6)]
    unfold evenMoveSource
    by_cases value : i.val < 23
    · rw [dif_pos value, if_pos (by omega : 131072+i.val-131078 < 17),
        even_pre_view u uBase _ (by omega), writeWord, if_neg (by omega),
        even_first_view state a _ (by omega), writeWindow, dif_neg (by omega)]
      change _ = memoryView state (src+5+(i.val-6))
      rw [show 131072 + i.val - 131078 = i.val - 6 by omega]
    · rw [dif_neg value, if_neg (by omega : ¬131072+i.val-131078 < 17),
        even_pre_view u uBase _ (by omega), writeWord, if_neg (by omega),
        even_first_view state a _ (by omega), writeWindow, dif_neg (by omega),
        checker_nonce_words state nonce ready.proofPointer]
      change _ = memoryView state (nonce+(i.val-23))
      rw [show 131072 + i.val - 131078 - 17 = i.val - 23 by omega]
  · rw [if_neg moved, even_pre_view u uBase _ (by omega), writeWord]
    by_cases zero : i.val = 0
    · rw [if_pos (by omega), if_pos zero, uTag, even_tag]
    · rw [if_neg (by omega), if_neg zero, dif_pos (by omega : i.val < 6), even_first_view state a _ (by omega),
        writeWindow, dif_pos (by omega)]
      exact congrArg (replyWords a) (Fin.ext (by show 131072 + i.val - 131053 = i.val + 19; omega))

/-! ## `frame` -/

private theorem even_final_view (state : MachineState) (first second : Block) :
    memoryView (evenFinal state first second) =
      memoryView (writeBits (evenMiddle (evenFirstState state first)) (wordAddress 1536) second) := by
  unfold evenFinal
  rw [evenJump, even_exec_jal, even_view_set_pc]
  rfl

theorem even_final_frame {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (first second : Block) (word : Nat) (bounded : word < 2^33)
    (scratch : word < 1536 ∨ 1561 ≤ word) (outside : word < 131053 ∨ 131097 ≤ word) :
    memoryView (evenFinal state first second) word = memoryView state word := by
  have high := ready.srcHigh
  have room := ready.endBound
  have low := ready.nonceRange
  obtain ⟨preSource, preNonce, preBase⟩ := even_pre_facts ready first
  rw [even_final_view]
  change BitVec 1600 at second
  change memoryView (writeBits (evenMiddle (evenFirstState state first)) (wordAddress 1536) second) word = _
  rw [ permutation_write_memory _ 1536 word second (by decide) bounded, writeWindow,
    dif_neg (by omega), even_middle_split, even_post_view,
    even_moves_view _ src nonce preSource preNonce preBase high room low 19 le_rfl word (by omega),
    if_neg (by omega), even_pre_view _ (even_first_base state first) word (by omega), writeWord, if_neg (by omega),
    even_first_view state first word bounded, writeWindow, dif_neg (by omega)]

/-! ## Execution -/

private theorem even_head_hop (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*494)) :
    Hop state (evenHead state) 3 3 := by
  let s1 := execInstrBr state (.LUI .x30 256)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 96)
  have h1 := even_step state 494 (.LUI .x30 256) (by decide) pc (even_head_decode 0 (by decide)) rfl rfl
  have h2 := even_step s1 495 (.ADDI .x10 .x10 96) (by decide)
    (by change state.pc + 4 = _; rw [pc]; decide) (even_head_decode 1 (by decide)) rfl rfl
  have h3 := even_step s2 496 (.ADDI .x12 .x30 3944) (by decide)
    (by change state.pc + 4 + 4 = _; rw [pc]; decide) (even_head_decode 2 (by decide)) rfl rfl
  exact (h1.thenDo h2).thenDo h3

private theorem even_pre_hop (u : MachineState) (pc : u.pc = BitVec.ofNat 64 (4096+4*498))
    (base : u.getReg .x30 = wordAddress 131072) :
    Hop u (evenPre u) 3 3 := by
  let s1 := execInstrBr u (.ADDI .x10 .x10 4000)
  let s2 := execInstrBr s1 (.ADDI .x31 .x28 4088)
  have address : s2.getReg .x30 + signExtend12 0 = wordAddress 131072 := by
    simp [s1, s2, even_exec_addi, even_get_reg, base, even_sext_zero]
  have h1 := even_step u 498 (.ADDI .x10 .x10 4000) (by decide) pc (even_middle_decode 0 (by decide)) rfl rfl
  have h2 := even_step s1 499 (.ADDI .x31 .x28 4088) (by decide)
    (by change u.pc + 4 = _; rw [pc]; decide) (even_middle_decode 1 (by decide)) rfl rfl
  have h3 := even_step s2 500 (.SD .x30 .x31 0) (by decide)
    (by change u.pc + 4 + 4 = _; rw [pc]; decide) (even_middle_decode 2 (by decide))
    (even_step_sd _ _ _ _ (by rw [address]; exact aligned_access _ (by decide))) rfl
  exact (h1.thenDo h2).thenDo h3

private theorem even_move_code_at (j k : Nat) (hj : j < 19) (hk : k < 2) :
    evenMiddleCode[3+2*j+k]? = (evenMoveCode j)[k]? := by
  interval_cases j <;> interval_cases k <;> rfl

private theorem even_move_decode (j k : Nat) (hj : j < 19) (hk : k < 2) :
    (pairImage.code[501+2*j+k]?).bind decodeInstruction = some (.base ((evenMoveCode j)[k]?.getD .EBREAK)) := by
  rw [← even_move_code_at j k hj hk, show 501+2*j+k = 498+(3+2*j+k) by omega]
  exact even_middle_decode _ (by omega)

private theorem even_move_load_address (m : MachineState) (j src nonce : Nat) (small : j < 19)
    (source : m.getReg .x10 = wordAddress src) (proofPointer : m.getReg .x4 = wordAddress nonce) :
    m.getReg (if j < 17 then .x10 else .x4) +
      signExtend12 (if j < 17 then BitVec.ofNat 12 (40+8*j) else BitVec.ofNat 12 (8*(j-17))) =
        wordAddress (evenMoveSource src nonce j) := by
  rw [← even_load_address m j src nonce small source proofPointer]
  by_cases low : j < 17
  · rw [if_pos low, if_pos low, if_pos low]
  · rw [if_neg low, if_neg low, if_neg low]

private theorem even_move_hop (m : MachineState) (j src nonce : Nat) (small : j < 19)
    (pc : m.pc = BitVec.ofNat 64 (4096+4*(501+2*j)))
    (source : m.getReg .x10 = wordAddress src) (proofPointer : m.getReg .x4 = wordAddress nonce)
    (base : m.getReg .x30 = wordAddress 131072) (room : src + 37 ≤ 2^33) (low : nonce + 2 ≤ 1536) :
    Hop m ((evenMoveCode j).foldl execInstrBr m) 2 2 := by
  have d0 := even_move_decode j 0 small (by decide)
  have d1 := even_move_decode j 1 small (by decide)
  rw [even_move_code] at d0 d1
  rw [Nat.add_zero] at d0
  rw [even_move_code]
  have loadAt := even_move_load_address m j src nonce small source proofPointer
  have sourceBound : evenMoveSource src nonce j < 2^33 := by
    unfold evenMoveSource; split <;> omega
  let ld : Instr := .LD .x31 (if j < 17 then .x10 else .x4)
    (if j < 17 then BitVec.ofNat 12 (40+8*j) else BitVec.ofNat 12 (8*(j-17)))
  let sd : Instr := .SD .x30 .x31 (BitVec.ofNat 12 (48+8*j))
  have h1 := even_step m (501+2*j) ld (by omega) pc d0
    (even_step_ld _ _ _ _ (by rw [loadAt]; exact aligned_access _ sourceBound)) rfl
  have h2 := even_step (execInstrBr m ld) (501+2*j+1) sd (by omega)
    (by change m.pc + 4 = _; rw [pc, even_pc_four]; congr 1) d1
    (even_step_sd _ _ _ _ (by
      rw [even_ld_register _ _ _ _ _ (by decide), base, even_store_address j small]
      exact aligned_access _ (by omega))) rfl
  exact h1.thenDo h2

private theorem even_moves_hop (u : MachineState) (src nonce : Nat)
    (pc : (evenPre u).pc = BitVec.ofNat 64 (4096+4*501))
    (source : (evenPre u).getReg .x10 = wordAddress src) (proofPointer : (evenPre u).getReg .x4 = wordAddress nonce)
    (base : (evenPre u).getReg .x30 = wordAddress 131072) (room : src + 37 ≤ 2^33) (low : nonce + 2 ≤ 1536)
    (j : Nat) (small : j ≤ 19) :
    Hop (evenPre u) (evenMoves u j) (2*j) (2*j) := by
  induction j with
  | zero =>
    intro fuel
    exact execute_unit_steps pairImage 0 fuel (fun _ => evenPre u) false (by intro i h; omega)
  | succ j ih =>
    have regs (r : Reg) (other : r ≠ .x31) := even_moves_register u j r other
    have step := even_move_hop (evenMoves u j) j src nonce (by omega)
      (by rw [even_moves_pc u _ pc]; congr 1; omega) ((regs _ (by decide)).trans source)
      ((regs _ (by decide)).trans proofPointer) ((regs _ (by decide)).trans base) room low
    rw [even_moves_succ, show 2*(j+1) = 2*j+2 by omega]
    exact (ih (by omega)).thenDo step

private theorem even_post_hop (m : MachineState) (pc : m.pc = BitVec.ofNat 64 (4096+4*539)) :
    Hop m (evenPost m) 2 2 := by
  have h1 := even_step m 539 (.ADDI .x10 .x30 0) (by decide) pc (even_middle_decode 41 (by decide)) rfl rfl
  have h2 := even_step (execInstrBr m (.ADDI .x10 .x30 0)) 540 (.ADDI .x12 .x23 0) (by decide)
    (by change m.pc + 4 = _; rw [pc]; decide) (even_middle_decode 42 (by decide)) rfl rfl
  exact h1.thenDo h2

private theorem even_middle_hop {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (a : Block) :
    Hop (evenFirstState state a) (evenMiddle (evenFirstState state a)) 43 43 := by
  let u := evenFirstState state a
  have pc : u.pc = BitVec.ofNat 64 (4096+4*498) := even_first_pc ready a
  obtain ⟨preSource, preNonce, preBase⟩ := even_pre_facts ready a
  have prePc : (evenPre u).pc = BitVec.ofNat 64 (4096+4*501) := by
    rw [even_pre_pc, pc]
    decide
  have movesPc : (evenMoves u 19).pc = BitVec.ofNat 64 (4096+4*539) := even_moves_pc u _ prePc 19
  rw [even_middle_split]
  exact ((even_pre_hop u pc (even_first_base state a)).thenDo
    (even_moves_hop u src nonce prePc preSource preNonce preBase ready.endBound ready.nonceRange 19 le_rfl)).thenDo
    (even_post_hop _ movesPc)

attribute [local irreducible] execute readBuffer packBuffer

private theorem even_first_call {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (fuel : Nat) :
    execute pairImage (4+fuel) state false =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer (evenFirstInput (window (memoryView state) (src+5)))))))
          let r ← execute pairImage fuel (evenFirstState state a) false
          return r.charge 11 1) := by
  have room := ready.endBound
  have callPC : (evenHead state).pc = BitVec.ofNat 64 (4096+4*497) := by
    rw [even_head_pc, ready.pc]
    decide
  have input : (evenHead state).getReg .x10 = wordAddress (src+12) := by
    rw [even_head_input, ready.source, even_add_word]
  have keep (reg : Reg) (x : reg ≠ .x10) (y : reg ≠ .x12) (z : reg ≠ .x30) :=
    even_head_register state reg x y z
  have call := execute_permutation_call pairImage fuel (evenHead state) false (src+12) 131053
    (by omega) (by decide) input (even_head_output state)
    ((keep _ (by decide) (by decide) (by decide)).trans ready.selector)
    ((keep _ (by decide) (by decide) (by decide)).trans ready.size)
    ((keep _ (by decide) (by decide) (by decide)).trans ready.primitive)
    (fetch_wide _ 497 .ECALL (by decide) callPC even_calls_decode.1)
  rw [even_first_input] at call
  rw [show 4+fuel = 3+(fuel+1) by omega, even_head_hop state ready.pc (fuel+1), call]
  simp [evenFirstState, Execution.charge, ← Nat.add_assoc]

private theorem even_second_call (m : MachineState) (pc : m.pc = BitVec.ofNat 64 (4096+4*541))
    (input : m.getReg .x10 = wordAddress 131072) (output : m.getReg .x12 = wordAddress 1536)
    (selector : m.getReg .x5 = 0) (size : m.getReg .x11 = 200) (primitive : m.getReg .x13 = 1) (fuel : Nat) :
    execute pairImage (2+fuel) m false =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView m) 131072)))))
          let r ← execute pairImage fuel (execInstrBr (writeBits m (wordAddress 1536) b) evenJump) false
          return r.charge 9 1) := by
  have call := execute_permutation_call pairImage (fuel+1) m false 131072 1536 (by decide) (by decide)
    input output selector size primitive (fetch_wide m 541 .ECALL (by decide) pc even_calls_decode.2.1)
  rw [show 2+fuel = fuel+1+1 by omega, call]
  apply bind_congr_of_forall_mem_support
  intro b _
  change Block at b
  have jump := even_step (writeBits m (wordAddress 1536) b) 542 evenJump (by decide)
    (by rw [even_write_pc, pc]; decide) even_calls_decode.2.2 rfl rfl fuel
  rw [Nat.add_comm fuel 1, jump]
  simp [Execution.charge, ← Nat.add_assoc]

theorem even_path_run {state : MachineState} {src nonce : Nat} {index : Index}
    (ready : EvenReady state src nonce index) (fuel : Nat) :
    execute pairImage (49+fuel) state false =
      (do let intermediate ← evenQueries state src index
          let result ← execute pairImage fuel intermediate false
          return result.charge 63 2) := by
  rw [show 49+fuel = 4+(43+(2+fuel)) by omega, even_first_call ready]
  simp only [evenQueries, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change Block at a
  let u := evenFirstState state a
  have keep (reg : Reg) (x : reg ≠ .x10) (y : reg ≠ .x12) (z : reg ≠ .x31) (w : reg ≠ .x30) :
      (evenMiddle u).getReg reg = state.getReg reg :=
    (even_middle_register u reg x y z).trans (even_first_keep a reg x y w)
  have args := even_middle_args u
  have second := even_second_call (evenMiddle u) (even_middle_pc u (even_first_pc ready a))
    (args.1.trans (even_first_base state a))
    (args.2.trans ((even_first_keep a _ (by decide) (by decide) (by decide)).trans ready.destination))
    ((keep _ (by decide) (by decide) (by decide) (by decide)).trans ready.selector)
    ((keep _ (by decide) (by decide) (by decide) (by decide)).trans ready.size)
    ((keep _ (by decide) (by decide) (by decide) (by decide)).trans ready.primitive) fuel
  rw [even_second_input ready a] at second
  rw [even_middle_hop ready a (2+fuel), bind_assoc, second]
  simp [evenFinal, Execution.charge, ← Nat.add_assoc]
  rfl

/-! ## The target -/

theorem even_path_facts : EvenPathFacts where
  run := even_path_run
  pc := even_final_pc
  register := fun state first second reg a b c d => even_final_register state first second reg a b c d
  frame := even_final_frame

end TwoPermutationPrototype.PairCk.Packed.RecordLeaf
