import CommitGolfCandidate.GroupOpenImage
import CommitGolfCandidate.GroupOpenPathLayout

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

@[local simp] private theorem mem_set_register (state : MachineState) (reg : Reg) (word : Word) :
    (state.setReg reg word).mem = state.mem := by cases reg <;> rfl

@[local simp] private theorem mem_set_pc (state : MachineState) (pc : Word) :
    (state.setPC pc).mem = state.mem := rfl

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

@[local simp] private theorem pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

/-! ### Straight-line writer rows

A run of rows `(word, instruction)` of unit-cost ordinary instructions, each at its word, where every
row's successor word is the next word or its `jal` target. -/

def rowsState (state : MachineState) (rows : List (Nat × Instr)) (count : Nat) : MachineState :=
  (rows.take count).foldl (fun t r => execInstrBr t r.2) state

/-- The pc after row `r`: the next word, or the `jal` target. -/
def rowNext (r : Nat × Instr) : Word :=
  match r.2 with
  | .JAL _ offset => BitVec.ofNat 64 (4096+4*r.1) + signExtend21 offset
  | _ => BitVec.ofNat 64 (4096+4*(r.1+1))

/-- The instructions a row may hold. -/
def rowInstr : Instr → Bool
  | .LHU .. | .SH .. | .LD .. | .SD .. | .ADDI .. | .SLLI .. | .SRLI .. | .OR .. | .XORI .. | .ADD .. => true
  | .JAL .x0 _ => true
  | _ => false

theorem row_pc (state : MachineState) (r : Nat × Instr) (kind : rowInstr r.2 = true)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*r.1)) :
    (execInstrBr state r.2).pc = rowNext r := by
  obtain ⟨w, i⟩ := r
  simp only at kind pc ⊢
  have four : BitVec.ofNat 64 (4096+4*w) + 4#64 = BitVec.ofNat 64 (4096+4*(w+1)) := by
    rw [show (4#64 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1 <;> omega
  cases i <;> first
    | (simp [rowInstr] at kind; done)
    | simp [rowNext, execInstrBr, pc, four, MachineState.setHalfword, MachineState.setByte,
        MachineState.setWord32]

theorem row_ordinary (state : MachineState) (i : Instr) (kind : rowInstr i = true)
    (valid : memoryArgumentsValid state i = true) :
    ordinaryStep state (.base i) = some (execInstrBr state i) := by
  cases i <;> first
    | (simp [rowInstr] at kind; done)
    | simp_all [ordinaryStep]

theorem row_cycles (i : Instr) (kind : rowInstr i = true) : instructionCycles (.base i) = 1 := by
  cases i <;> first
    | (simp [rowInstr] at kind; done)
    | rfl

theorem rows_state_succ (state : MachineState) (rows : List (Nat × Instr)) (i : Nat) (inside : i < rows.length) :
    rowsState state rows (i+1) = execInstrBr (rowsState state rows i) rows[i].2 := by
  unfold rowsState
  rw [List.take_succ_eq_append_getElem inside, List.foldl_append]
  rfl

/-- The rows are well formed: decoded at their words, of an allowed kind, and chained. -/
def RowsCode (rows : List (Nat × Instr)) : Prop :=
  (∀ r ∈ rows, r.1 < 896 ∧ (openingImage.code[r.1]?).bind Opening.decodeBase = some r.2 ∧ rowInstr r.2 = true) ∧
  ∀ i (inside : i < rows.length-1), rowNext rows[i] = BitVec.ofNat 64 (4096+4*rows[i+1].1)

instance (rows : List (Nat × Instr)) : Decidable (RowsCode rows) := by unfold RowsCode; infer_instance

theorem rows_pc (state : MachineState) (rows : List (Nat × Instr)) (code : RowsCode rows)
    (start : ∀ inside : 0 < rows.length, state.pc = BitVec.ofNat 64 (4096+4*rows[0].1)) :
    ∀ i (inside : i < rows.length), (rowsState state rows i).pc = BitVec.ofNat 64 (4096+4*rows[i].1) := by
  intro i inside
  induction i with
  | zero => exact start inside
  | succ i ih =>
    rw [rows_state_succ _ _ _ (by omega), row_pc _ _ (code.1 _ (List.getElem_mem _)).2.2 (ih (by omega))]
    exact code.2 i (by omega)

theorem rows_after_pc (state : MachineState) (rows : List (Nat × Instr)) (code : RowsCode rows)
    (start : ∀ inside : 0 < rows.length, state.pc = BitVec.ofNat 64 (4096+4*rows[0].1))
    (n : Nat) (last : n+1 = rows.length) :
    (rowsState state rows (n+1)).pc = rowNext rows[n] := by
  rw [rows_state_succ _ _ _ (by omega)]
  exact row_pc _ _ (code.1 _ (List.getElem_mem _)).2.2 (rows_pc state rows code start n (by omega))

theorem execute_rows (state : MachineState) (rows : List (Nat × Instr)) (code : RowsCode rows)
    (start : ∀ inside : 0 < rows.length, state.pc = BitVec.ofNat 64 (4096+4*rows[0].1))
    (valid : ∀ i (inside : i < rows.length), memoryArgumentsValid (rowsState state rows i) rows[i].2 = true)
    (fuel : Nat) (coins : Bool) :
    execute openingImage (rows.length+fuel) state coins =
      (do let result ← execute openingImage fuel (rowsState state rows rows.length) coins
          return result.charge rows.length 0) := by
  apply execute_unit_steps (states := rowsState state rows)
  intro i inside
  have member := code.1 _ (List.getElem_mem inside)
  refine ⟨.base rows[i].2, ?_, ?_, row_cycles _ member.2.2⟩
  · exact packed_fetch_base _ _ _ member.1 (rows_pc state rows code start i inside) member.2.1
  · rw [rows_state_succ _ _ _ inside]
    exact row_ordinary _ _ member.2.2 (valid i inside)

/-! ### Upper path levels -/

def siblingSite (level : Fin 14) : CopySite :=
  if h : level.val = 0 then .firstSibling else .sibling ⟨level.val-1, by omega⟩

@[simp] theorem sibling_source_reg (level : Fin 14) : (siblingSite level).source = .x7 := by
  unfold siblingSite
  split <;> rfl

@[simp] theorem sibling_dest_offset (level : Fin 14) : (siblingSite level).destOffset = 0 := by
  unfold siblingSite
  split <;> rfl

def siblingStart (level : Fin 14) : Nat := if level.val=0 then 148 else (siblingSite level).start-3
def siblingEnd (level : Fin 14) : Nat :=
  if level.val = 13 then 638 else if level.val = 1 then 220 else (siblingSite level).start+2*(siblingSite level).halfwords

/-- The generic straight-line copy moves the whole width except at the dedicated level-1 site. -/
theorem sibling_width_exact :
    ∀ level : Fin 14, level.val < 13 →
      2*(siblingSite level).halfwords = if level.val = 1 then 0 else siblingWidth level.val := by
  decide

theorem sibling_copy_start : ∀ level : Fin 14, level.val≠0 → siblingStart level+3 = (siblingSite level).start := by
  decide

theorem sibling_next_all : ∀ level : Fin 13,
    siblingEnd ⟨level.val, by omega⟩+2 = siblingStart ⟨level.val+1, by omega⟩ := by
  decide

theorem sibling_next (level : Fin 14) (later : level.val+1 < 14) :
    siblingEnd level+2 = siblingStart ⟨level.val+1, later⟩ :=
  sibling_next_all ⟨level.val, by omega⟩

theorem first_sibling_start : siblingStart 0 = 148 := rfl
theorem last_sibling_start : siblingStart 13 = 607 := rfl
theorem last_sibling_end : siblingEnd 13 = 638 := rfl
theorem a1_sibling_end : siblingEnd 1 = 220 := rfl

def headCode : List Instr :=
  [.XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]

def tailCode (level : Fin 14) : List Instr :=
  [.ADDI .x21 .x21 (BitVec.ofNat 12 (siblingWidth level.val)), .SRLI .x6 .x6 1]

def headPrefix (state : MachineState) (count : Nat) : MachineState :=
  (headCode.take count).foldl execInstrBr state

def tailPrefix (state : MachineState) (level : Fin 14) (count : Nat) : MachineState :=
  ((tailCode level).take count).foldl execInstrBr state

set_option maxRecDepth 4096 in
private theorem head_decode :
    ∀ (level : Fin 14) (i : Fin 3), level.val ≠ 0 → level.val ≠ 2 →
      (openingImage.code[siblingStart level+i.val]?).bind Opening.decodeBase =
        some (headCode[i.val]?.getD .EBREAK) := by decide

/-- Levels with the plain two-word tail at `siblingEnd` (all but level 1, through A1, and level 13,
through the fold). -/
def PlainTail (level : Fin 14) : Prop := level.val ≠ 1 ∧ level.val ≠ 13

instance (level : Fin 14) : Decidable (PlainTail level) := by unfold PlainTail; infer_instance

set_option maxRecDepth 4096 in
private theorem tail_decode :
    ∀ (level : Fin 14) (i : Fin 2), PlainTail level →
      (openingImage.code[siblingEnd level+i.val]?).bind Opening.decodeBase =
        some ((tailCode level)[i.val]?.getD .EBREAK) := by decide

private theorem head_range : ∀ level : Fin 14, siblingStart level+3 ≤ 896 := by decide
private theorem tail_range : ∀ level : Fin 14, siblingEnd level+2 ≤ 896 := by decide

theorem execute_sibling_head (state : MachineState) (level : Fin 14) (nz : level.val ≠ 0) (old : level.val ≠ 2)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level)) (fuel : Nat) (coins : Bool) :
    execute openingImage (3+fuel) state coins =
      (do let result ← execute openingImage fuel (headPrefix state 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := headPrefix state)
  intro i inside
  refine ⟨.base (headCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (siblingStart level+i) _ (by have := head_range level; omega)
    · have offset : BitVec.ofNat 64 (4096+4*siblingStart level) + BitVec.ofNat 64 (4*i) =
          BitVec.ofNat 64 (4096+4*(siblingStart level+i)) := by rw [← BitVec.ofNat_add]; congr 1; omega
      rw [← offset]
      interval_cases i <;> simp [headPrefix, headCode, execInstrBr, pc, BitVec.add_assoc]
    · exact head_decode level ⟨i,inside⟩ nz old
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_sibling_tail (state : MachineState) (level : Fin 14) (plain : PlainTail level)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*siblingEnd level)) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) state coins =
      (do let result ← execute openingImage fuel (tailPrefix state level 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := tailPrefix state level)
  intro i inside
  refine ⟨.base ((tailCode level)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (siblingEnd level+i) _ (by have := tail_range level; omega)
    · have offset : BitVec.ofNat 64 (4096+4*siblingEnd level) + BitVec.ofNat 64 (4*i) =
          BitVec.ofNat 64 (4096+4*(siblingEnd level+i)) := by rw [← BitVec.ofNat_add]; congr 1; omega
      rw [← offset]
      interval_cases i <;> simp [tailPrefix, tailCode, execInstrBr, pc, BitVec.add_assoc]
    · exact tail_decode level ⟨i,inside⟩ plain
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem sibling_head_post (state : MachineState) :
    let next := headPrefix state 3
    next.pc = state.pc+12#64 ∧ next.mem = state.mem ∧
      next.getReg .x7 = state.getReg .x9+((state.getReg .x6 ^^^ 1#64) <<< 5) ∧
      ∀ reg, reg ≠ .x7 → next.getReg reg = state.getReg reg := by
  simp [headPrefix, headCode, execInstrBr, signExtend12, BitVec.add_assoc]
  intro reg distinct
  simp [Ne.symm distinct]

theorem sibling_tail_post (state : MachineState) (level : Fin 14) :
    let next := tailPrefix state level 2
    next.pc = state.pc+8#64 ∧ next.mem = state.mem ∧
      next.getReg .x21 = state.getReg .x21 + BitVec.ofNat 64 (siblingWidth level.val) ∧
      next.getReg .x6 = state.getReg .x6 >>> 1 ∧
      ∀ reg, reg ≠ .x21 → reg ≠ .x6 → next.getReg reg = state.getReg reg := by
  have small : siblingWidth level.val < 2048 := by have := sibling_width_le level.val; omega
  have sign : signExtend12 (BitVec.ofNat 12 (siblingWidth level.val)) = BitVec.ofNat 64 (siblingWidth level.val) := by
    have cases : siblingWidth level.val = 32 ∨ siblingWidth level.val = 30 ∨ siblingWidth level.val = 28 := by
      unfold siblingWidth; split <;> (try split) <;> simp
    rcases cases with h | h | h <;> rw [h] <;> rfl
  simp [tailPrefix, tailCode, execInstrBr, sign, BitVec.add_assoc]
  intro reg a b
  simp [Ne.symm a, Ne.symm b]

/-! ### Level 0 through the prefix's pointer word -/

/-- Level 0's head loads the sibling pointer from the biased quartet base and jumps to the wide copy. -/
def zeroRows : List (Nat × Instr) :=
  [(148, .LD .x7 .x7 128), (149, .JAL .x0 16)]

theorem zero_code : RowsCode zeroRows := by decide +kernel

theorem zero_final_pc : rowNext zeroRows[1] = BitVec.ofNat 64 (4096+4*153) := by decide +kernel

/-! ### Level 1 through A1 -/

/-- Level 1 advances the cursor and node after copying the whole sibling. -/
def a1Rows : List (Nat × Instr) :=
  [(220, .ADDI .x21 .x21 32), (221, .SRLI .x6 .x6 1)]

theorem a1_code : RowsCode a1Rows := by decide +kernel

theorem a1_final_pc : rowNext a1Rows[1] = BitVec.ofNat 64 (4096+4*222) := by decide +kernel

end TwoPermutationPrototype.GroupedOpening
