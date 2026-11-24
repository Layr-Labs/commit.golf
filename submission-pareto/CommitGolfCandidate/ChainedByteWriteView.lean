import CommitGolfCandidate.ChainedTailMemory

/-! Readback and untouched-byte frames for a bounded native byte-write sequence. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem byte_offset_inj (base : Word) (left right : Nat) (leftFit : left<2^64) (rightFit : right<2^64)
    (same : base+BitVec.ofNat 64 left=base+BitVec.ofNat 64 right) : left=right := by
  have words := (BitVec.add_right_inj base).mp same
  have numbers := congrArg BitVec.toNat words
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt leftFit,Nat.mod_eq_of_lt rightFit] using numbers

theorem write_byte_list_preserves (memory : Word → BitVec 8) (base : Word) (bytes : Proof) (query : Word)
    (away : ∀ index, index<bytes.length → query≠base+BitVec.ofNat 64 index) :
    writeByteList memory base bytes query=memory query := by
  induction bytes generalizing memory base with
  | nil => rfl
  | cons byte bytes ih =>
    have first : query≠base := by simpa using away 0 (by simp)
    have rest : ∀ index, index<bytes.length → query≠(base+1)+BitVec.ofNat 64 index := by
      intro index inside
      have shifted : (base+1)+BitVec.ofNat 64 index=base+BitVec.ofNat 64 (index+1) := by
        change (base+BitVec.ofNat 64 1)+BitVec.ofNat 64 index=_
        rw [byte_offset_add,Nat.add_comm 1]
      rw [shifted]
      exact away (index+1) (by simpa using inside)
    rw [writeByteList,ih _ _ rest]
    simp [storeByteFn,first]

theorem write_byte_list_read (memory : Word → BitVec 8) (base : Word) (bytes : Proof)
    (fit : bytes.length<2^64) (index : Nat) (inside : index<bytes.length) :
    writeByteList memory base bytes (base+BitVec.ofNat 64 index)=bytes.getD index 0 := by
  induction bytes generalizing memory base index with
  | nil => simp at inside
  | cons byte bytes ih =>
    cases index with
    | zero =>
      have away : ∀ offset, offset<bytes.length → base≠(base+1)+BitVec.ofNat 64 offset := by
        intro offset bounded same
        have location : (base+1)+BitVec.ofNat 64 offset=base+BitVec.ofNat 64 (offset+1) := by
          change (base+BitVec.ofNat 64 1)+BitVec.ofNat 64 offset=_
          rw [byte_offset_add,Nat.add_comm 1]
        rw [location] at same
        have equal : base+BitVec.ofNat 64 0=base+BitVec.ofNat 64 (offset+1) := by simpa using same
        have impossible := byte_offset_inj base 0 (offset+1) (by decide) (by simp only [List.length_cons] at fit; omega) equal
        omega
      have result := write_byte_list_preserves (storeByteFn memory base byte) (base+1) bytes base away
      simpa [writeByteList,storeByteFn] using result
    | succ index =>
      have location : base+BitVec.ofNat 64 (index+1)=(base+1)+BitVec.ofNat 64 index := by
        change _=(base+BitVec.ofNat 64 1)+BitVec.ofNat 64 index
        rw [byte_offset_add,Nat.add_comm 1]
      rw [location,writeByteList,List.getD_cons_succ]
      exact ih _ _ (by simp only [List.length_cons] at fit; omega) index (by simpa using inside)

theorem native_tail_bytes_at (rows : List (List Bool)) (front : List Bool) (s : MachineState)
    (buffer : TailBuffer s front) (small : ∀ row ∈ rows, row.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes rows))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) rows)
    (fit : (packedBits (front++rows.flatten)).length<2^64) :
    BytesAt (tailFinishState (tailFieldsState rows.length s)) (s.getReg .x20) (packedBits (front++rows.flatten)) := by
  intro index inside
  rw [native_tail_memory rows front s buffer small memory apart]
  exact write_byte_list_read _ _ _ fit index inside

end CommitGolfCandidate.Chained.Native
