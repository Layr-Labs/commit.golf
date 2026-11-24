import CommitGolfCandidate.ChainedFieldBuild

/-! Complete field write plans and preservation of earlier output and unread input. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem field_build_frame (n : Nat) (s : MachineState) (reg : Reg)
    (source : reg≠.x5) (destination : reg≠.x6) (descriptor : reg≠.x7)
    (temporary : reg≠.x11) : (fieldBuildState n s).getReg reg=s.getReg reg := by
  rw [fieldBuildState,field_descriptor_frame _ reg source descriptor temporary,
    low_copy_frame _ _ reg source destination temporary]

theorem field_build_pc (n : Nat) (s : MachineState) :
    (fieldBuildState n s).pc=s.pc+BitVec.ofNat 64 (4*(4*n+5)) := by
  rw [fieldBuildState,field_descriptor_pc _ 5 (by decide),low_copy_pc]
  change (s.pc+BitVec.ofNat 64 (16*n))+BitVec.ofNat 64 20=_
  rw [byte_offset_add]
  congr 2
  omega

theorem native_field_write_plan (low : Proof) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length) (query : Word) :
    (fieldBuildState low.length s).getByte query=
      if query=s.getReg .x7+1 then (s.getReg .x10).setWidth 8 else
        if query=s.getReg .x7 then s.getByte (s.getReg .x5+BitVec.ofNat 64 low.length) else
          writeByteList s.getByte (s.getReg .x6) low query := by
  have last : (lowCopyState low.length s).getByte ((lowCopyState low.length s).getReg .x5)=
      s.getByte (s.getReg .x5+BitVec.ofNat 64 low.length) := by
    rw [low_copy_source,native_low_copy_plan low s body ahead,write_byte_list_preserves]
    intro index inside
    exact ahead low.length (by omega) index inside
  rw [fieldBuildState,field_descriptor_byte,last,
    low_copy_frame _ _ .x7 (by decide) (by decide) (by decide),
    low_copy_frame _ _ .x10 (by decide) (by decide) (by decide),
    native_low_copy_plan low s body ahead]

theorem native_field_preserves_byte (low : Proof) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length) (query : Word)
    (value : query≠s.getReg .x7) (width : query≠s.getReg .x7+1)
    (apart : ∀ index, index<low.length → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (fieldBuildState low.length s).getByte query=s.getByte query := by
  rw [native_field_write_plan low s body ahead,ite_eq_right width,ite_eq_right value]
  exact write_byte_list_preserves _ _ _ _ apart

theorem native_field_preserves_bytes (low bytes : Proof) (s : MachineState) (base : Word)
    (body : BytesAt s (s.getReg .x5) low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length) (memory : BytesAt s base bytes)
    (scratch : ∀ index, index<bytes.length →
      base+BitVec.ofNat 64 index≠s.getReg .x7 ∧ base+BitVec.ofNat 64 index≠s.getReg .x7+1)
    (apart : ∀ index, index<bytes.length → ∀ written, written<low.length →
      base+BitVec.ofNat 64 index≠s.getReg .x6+BitVec.ofNat 64 written) :
    BytesAt (fieldBuildState low.length s) base bytes := by
  intro index inside
  rw [native_field_preserves_byte low s body ahead _ (scratch index inside).1
    (scratch index inside).2 (apart index inside)]
  exact memory index inside

end CommitGolfCandidate.Chained.Native
