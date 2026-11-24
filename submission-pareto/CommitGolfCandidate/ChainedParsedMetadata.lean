import CommitGolfCandidate.ChainedInversePrefix

/-! Parsed scratch values and untouched widths form the exact descriptor table. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem parsed_byte_offset (base : Word) (index : Nat) :
    (base+2)+BitVec.ofNat 64 (2*index)=base+BitVec.ofNat 64 (2*(index+1)) := by
  change (base+BitVec.ofNat 64 2)+BitVec.ofNat 64 (2*index)=_
  rw [byte_offset_add]
  congr 2
  omega

theorem write_parsed_rows_preserves (rows : List (List Bool)) (memory : Word → BitVec 8) (base query : Word)
    (apart : ∀ index, index<rows.length → query≠base+BitVec.ofNat 64 (2*index)) :
    writeParsedRows memory base rows query=memory query := by
  induction rows generalizing memory base with
  | nil => rfl
  | cons row rows ih =>
    rw [writeParsedRows,ih]
    · unfold storeByteFn
      rw [ite_eq_right (by simpa using apart 0 (by simp))]
    · intro index inside
      rw [parsed_byte_offset]
      exact apart (index+1) (by simpa using inside)

theorem write_parsed_rows_read (rows : List (List Bool)) (memory : Word → BitVec 8) (base : Word)
    (fit : 2*rows.length<2^64) (index : Nat) (inside : index<rows.length) :
    writeParsedRows memory base rows (base+BitVec.ofNat 64 (2*index))=
      tailBitsWord 8 (rows.getD index []) := by
  induction rows generalizing memory base index with
  | nil => simp at inside
  | cons row rows ih =>
    cases index with
    | zero =>
      simp only [Nat.mul_zero,BitVec.add_zero,List.getD_cons_zero,writeParsedRows]
      rw [write_parsed_rows_preserves]
      · simp [storeByteFn]
      · intro index bounded same
        rw [parsed_byte_offset] at same
        have impossible := byte_offset_inj base 0 (2*(index+1)) (by decide)
          (by simp only [List.length_cons] at fit; omega) (by simpa using same)
        omega
    | succ index =>
      rw [writeParsedRows,←parsed_byte_offset]
      exact ih _ _ (by simp only [List.length_cons] at fit; omega) index (by simpa using inside)

theorem mapped_row_width (rows : List (List Bool)) (index : Nat) :
    (rows.map List.length).getD index 0=(rows.getD index []).length := by
  induction rows generalizing index with
  | nil => simp
  | cons row rows ih => cases index <;> simp_all

theorem write_parsed_rows_descriptor (rows : List (List Bool)) (memory : Word → BitVec 8) (base : Word)
    (widths : ∀ index, index<rows.length →
      memory (base+BitVec.ofNat 64 (2*index+1))=BitVec.ofNat 8 (rows.getD index []).length)
    (fit : 2*rows.length<2^64) (index : Nat) (inside : index<(descriptorBytes rows).length) :
    writeParsedRows memory base rows (base+BitVec.ofNat 64 index)=(descriptorBytes rows).getD index 0 := by
  have bound : index<2*rows.length := by simpa only [descriptor_bytes_length] using inside
  have row : index/2<rows.length := by omega
  by_cases even : index%2=0
  · rw [show index=2*(index/2) by omega,write_parsed_rows_read rows memory base fit _ row]
    exact (descriptor_value rows _ row).symm
  · rw [show index=2*(index/2)+1 by omega,write_parsed_rows_preserves]
    · rw [widths _ row]
      exact (descriptor_width rows _ row).symm
    · intro written before same
      have impossible := byte_offset_inj base (2*(index/2)+1) (2*written) (by omega) (by omega) same
      omega

theorem parsed_rows_descriptor_at (s after : MachineState) (base : Word) (rows : List (List Bool))
    (table : ParseWidthsAt s base (rows.map List.length)) (fit : 2*rows.length<2^64)
    (memory : ∀ query, after.getByte query=writeParsedRows s.getByte base rows query) :
    BytesAt after base (descriptorBytes rows) := by
  intro index inside
  rw [memory]
  apply write_parsed_rows_descriptor rows s.getByte base ?_ fit index inside
  intro index inside
  have width := table index (by simpa using inside)
  rwa [mapped_row_width] at width

theorem parsed_fields_register (n : Nat) (s : MachineState) (reg : Reg)
    (input : reg≠.x20) (pointer : reg≠.x21) (counter : reg≠.x22) (buffer : reg≠.x23)
    (value : reg≠.x24) (count : reg≠.x25) (width : reg≠.x26) (mask : reg≠.x28) :
    (tailValidatePrefix (tailParsedFieldsState n s) 3).getReg reg=s.getReg reg := by
  rw [tail_validate_frame _ reg value mask]
  induction n generalizing s with
  | zero => rw [tail_parsed_fields_zero]
  | succ n ih =>
    rw [tail_parsed_fields_succ,ih,tail_parse_step_frame s reg input pointer counter buffer value count width mask]

end CommitGolfCandidate.Chained.Native
