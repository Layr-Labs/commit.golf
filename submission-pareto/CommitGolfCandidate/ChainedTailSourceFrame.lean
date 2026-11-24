import CommitGolfCandidate.ChainedDescriptorMemory

/-! Immutable descriptor-table refinement through native output-byte writes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def TailApart (source destination : Word) (rows : List (List Bool)) : Prop :=
  ∀ index, index<2*rows.length → ∀ offset, offset≤rows.length →
    source+BitVec.ofNat 64 index≠destination+BitVec.ofNat 64 offset

theorem tail_apart_shift (source destination : Word) (back : List Bool) (rows : List (List Bool))
    (apart : TailApart source destination (back::rows)) (step : Nat) (small : step≤1) :
    TailApart (source+BitVec.ofNat 64 2) (destination+BitVec.ofNat 64 step) rows := by
  intro index inside offset bounded
  rw [byte_offset_add,byte_offset_add]
  exact apart (2+index) (by simp only [List.length_cons]; omega)
    (step+offset) (by simp only [List.length_cons]; omega)

theorem tail_step_source_memory (s : MachineState) (front back : List Bool) (rows : List (List Bool))
    (buffer : TailBuffer s front) (small : back.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (back::rows)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (back::rows)) :
    BytesAt (tailStepState s) ((tailStepState s).getReg .x21) (descriptorBytes rows) := by
  have data := descriptor_memory_slot s (s.getReg .x21) (back::rows) memory 0 (by simp) (by simp)
  rw [tail_step_source]
  intro index inside
  have location : (s.getReg .x21+2)+BitVec.ofNat 64 index=s.getReg .x21+BitVec.ofNat 64 (index+2) := by
    change (s.getReg .x21+BitVec.ofNat 64 2)+BitVec.ofNat 64 index=_
    rw [byte_offset_add,Nat.add_comm 2 index]
  have different : (s.getReg .x21+2)+BitVec.ofNat 64 index≠s.getReg .x20 := by
    rw [location]
    have difference := apart (index+2) (by rw [descriptor_bytes_length] at inside; simp only [List.length_cons]; omega) 0 (by omega)
    simpa using difference
  have original := memory (index+2) (by
    rw [descriptor_bytes_length] at inside ⊢
    simp only [List.length_cons]
    omega)
  have same : (descriptorBytes (back::rows)).getD (index+2) 0=(descriptorBytes rows).getD index 0 := by
    simp only [descriptorBytes,List.getD_cons_succ]
  rw [same] at original
  rw [tail_step_bits_byte s front back buffer.value buffer.count buffer.eight data.1 data.2 buffer.pending small]
  by_cases fits : (front++back).length<8
  · rw [ite_eq_left fits,location]
    exact original
  · rw [ite_eq_right fits,ite_eq_right different,location]
    exact original

theorem tail_step_apart (s : MachineState) (front back : List Bool) (rows : List (List Bool))
    (buffer : TailBuffer s front) (small : back.length≤6)
    (memory : BytesAt s (s.getReg .x21) (descriptorBytes (back::rows)))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (back::rows)) :
    TailApart ((tailStepState s).getReg .x21) ((tailStepState s).getReg .x20) rows := by
  have data := descriptor_memory_slot s (s.getReg .x21) (back::rows) memory 0 (by simp) (by simp)
  rw [tail_step_source,tail_step_bits_pointer s front back buffer data.1 data.2 small]
  by_cases fits : (front++back).length<8
  · rw [ite_eq_left fits]
    simpa using tail_apart_shift (s.getReg .x21) (s.getReg .x20) back rows apart 0 (by decide)
  · rw [ite_eq_right fits]
    exact tail_apart_shift (s.getReg .x21) (s.getReg .x20) back rows apart 1 (by decide)

end CommitGolfCandidate.Chained.Native
