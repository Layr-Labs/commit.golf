import CommitGolfCandidate.ChainedWidthInit

/-! Width-table construction preserves even bytes and every byte outside its odd slots. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option Elab.async false

def widthTableOps (widths : List (Fin 7)) : List Instr := widths.flatMap widthInitOps
def widthTableWords (widths : List (Fin 7)) : List (BitVec 32) := widths.flatMap widthInitWords

@[irreducible] def widthTableState : List (Fin 7) → MachineState → MachineState
  | [],s => s
  | width::widths,s => widthTableState widths (widthInitPrefix width s 3)

theorem width_table_zero (s : MachineState) : widthTableState [] s=s := by
  rw [widthTableState]
theorem width_table_cons (width : Fin 7) (widths : List (Fin 7)) (s : MachineState) :
    widthTableState (width::widths) s=widthTableState widths (widthInitPrefix width s 3) := by
  rw [widthTableState]

theorem width_table_ops_length (widths : List (Fin 7)) : (widthTableOps widths).length=3*widths.length := by
  induction widths with
  | nil => rfl
  | cons width widths ih =>
    change (widthInitOps width++widthTableOps widths).length=_
    rw [List.length_append,ih]
    simp only [widthInitOps,List.length_cons,List.length_nil]
    omega

theorem width_slot_shift (base : Word) (index : Nat) :
    (base+2)+BitVec.ofNat 64 (2*index+1)=base+BitVec.ofNat 64 (2*(index+1)+1) := by
  change (base+BitVec.ofNat 64 2)+BitVec.ofNat 64 (2*index+1)=_
  rw [byte_offset_add]
  congr 2
  omega

theorem width_table_register (widths : List (Fin 7)) (s : MachineState) (reg : Reg)
    (pointer : reg≠.x7) (temporary : reg≠.x10) :
    (widthTableState widths s).getReg reg=s.getReg reg := by
  induction widths generalizing s with
  | nil => rw [width_table_zero]
  | cons width widths ih =>
    rw [width_table_cons,ih,width_init_register width s reg pointer temporary]

theorem width_table_pointer (widths : List (Fin 7)) (s : MachineState) :
    (widthTableState widths s).getReg .x7=s.getReg .x7+BitVec.ofNat 64 (2*widths.length) := by
  induction widths generalizing s with
  | nil => rw [width_table_zero]; simp
  | cons width widths ih =>
    rw [width_table_cons,ih,width_init_pointer]
    change (s.getReg .x7+BitVec.ofNat 64 2)+BitVec.ofNat 64 (2*widths.length)=_
    rw [byte_offset_add]
    congr 2
    simp only [List.length_cons]
    omega

theorem width_table_pc (widths : List (Fin 7)) (s : MachineState) :
    (widthTableState widths s).pc=s.pc+BitVec.ofNat 64 (12*widths.length) := by
  induction widths generalizing s with
  | nil => rw [width_table_zero]; simp
  | cons width widths ih =>
    rw [width_table_cons,ih,width_init_pc width s 3 (by decide)]
    rw [byte_offset_add]
    congr 2
    simp only [List.length_cons]
    omega

theorem width_table_byte_frame (widths : List (Fin 7)) (s : MachineState) (query : Word)
    (away : ∀ index, index<widths.length → query≠s.getReg .x7+BitVec.ofNat 64 (2*index+1)) :
    (widthTableState widths s).getByte query=s.getByte query := by
  induction widths generalizing s with
  | nil => rw [width_table_zero]
  | cons width widths ih =>
    rw [width_table_cons,ih]
    · rw [width_init_byte,ite_eq_right (by simpa using away 0 (by simp))]
    · intro index inside
      rw [width_init_pointer,width_slot_shift]
      exact away (index+1) (by simpa using inside)

theorem width_table_memory (widths : List (Fin 7)) (s : MachineState)
    (fit : 2*widths.length<2^64) :
    ParseWidthsAt (widthTableState widths s) (s.getReg .x7) (widths.map Fin.val) := by
  induction widths generalizing s with
  | nil => intro index inside; simp at inside
  | cons width widths ih =>
    intro index inside
    simp only [List.length_map,List.length_cons] at inside fit
    cases index with
    | zero =>
      change (widthTableState (width::widths) s).getByte (s.getReg .x7+1)=BitVec.ofNat 8 width.val
      rw [width_table_cons,width_table_byte_frame,width_init_byte,ite_eq_left rfl]
      intro index bounded same
      rw [width_init_pointer,width_slot_shift] at same
      change s.getReg .x7+BitVec.ofNat 64 1=s.getReg .x7+BitVec.ofNat 64 (2*(index+1)+1) at same
      have impossible := byte_offset_inj (s.getReg .x7) 1 (2*(index+1)+1)
        (by decide) (by omega) same
      omega
    | succ index =>
      have rest := ih (widthInitPrefix width s 3) (by omega) index (by simpa using inside)
      rw [width_init_pointer,width_slot_shift] at rest
      rw [width_table_cons]
      exact rest

theorem width_table_even_frame (widths : List (Fin 7)) (s : MachineState)
    (fit : 2*widths.length<2^64) (index : Nat) (inside : index<widths.length) :
    (widthTableState widths s).getByte (s.getReg .x7+BitVec.ofNat 64 (2*index))=
      s.getByte (s.getReg .x7+BitVec.ofNat 64 (2*index)) := by
  apply width_table_byte_frame
  intro other bounded same
  have impossible := byte_offset_inj (s.getReg .x7) (2*index) (2*other+1)
    (by omega) (by omega) same
  omega

end CommitGolfCandidate.Chained.Native
