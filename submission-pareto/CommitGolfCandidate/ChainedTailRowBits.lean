import CommitGolfCandidate.ChainedTailEmitBits

/-! Connect scratch-row loads and complete row byte effects to field bit lists. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem tail_load_field_bits (s : MachineState) (bits : List Bool) (small : bits.length≤6)
    (value : s.getByte (s.getReg .x21) = tailBitsWord 8 bits)
    (width : s.getByte (s.getReg .x21+1) = BitVec.ofNat 8 bits.length) :
    (tailLoadPrefix s 3).getReg .x24 = tailBitsWord 64 bits ∧
    (tailLoadPrefix s 3).getReg .x26 = BitVec.ofNat 64 bits.length := by
  constructor
  · rw [tail_load_value]
    erw [BitVec.add_zero]
    rw [value]
    change (tailBitsWord 8 bits).setWidth 64 = _
    exact tail_bits_word_setWidth 8 64 bits (by omega)
  · rw [tail_load_width,width]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth_of_le (by decide)]
    simp only [BitVec.toNat_ofNat]
    omega

private theorem tail_decrease_byte (s : MachineState) (query : Word) :
    (tailDecrease s).getByte query = s.getByte query := rfl

private theorem tail_back_byte (s : MachineState) (query : Word) :
    (tailBackEdge s).getByte query = s.getByte query := by
  simp only [MachineState.getByte,tail_back_memory]

private theorem tail_load_byte (s : MachineState) (query : Word) :
    (tailLoadPrefix s 3).getByte query = s.getByte query := by
  simp only [MachineState.getByte,tail_load_memory]

theorem tail_step_bits_byte (s : MachineState) (front back : List Bool)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length) (eight : s.getReg .x27 = 8)
    (value : s.getByte (s.getReg .x21) = tailBitsWord 8 back)
    (width : s.getByte (s.getReg .x21+1) = BitVec.ofNat 8 back.length)
    (pending : front.length<8) (small : back.length≤6) (query : Word) :
    (tailStepState s).getByte query = if (front++back).length<8 then s.getByte query
      else if query=s.getReg .x20 then tailBitsWord 8 (front++back) else s.getByte query := by
  have loaded := tail_load_field_bits s back small value width
  have bufferLoaded : (tailLoadPrefix s 3).getReg .x23 = tailBitsWord 64 front := by
    rw [tail_load_frame s .x23 (by decide) (by decide) (by decide)]
    exact buffer
  have countLoaded : (tailLoadPrefix s 3).getReg .x25 = BitVec.ofNat 64 front.length := by
    rw [tail_load_frame s .x25 (by decide) (by decide) (by decide)]
    exact count
  have eightLoaded : (tailLoadPrefix s 3).getReg .x27 = 8 := by
    rw [tail_load_frame s .x27 (by decide) (by decide) (by decide)]
    exact eight
  rw [tailStepState,tail_back_byte,tailStepDecreased,tail_decrease_byte,tailStepEmitted,
    tail_emit_bits_byte _ front back bufferLoaded loaded.1 countLoaded loaded.2 eightLoaded pending
      (by simp only [List.length_append]; omega),tail_load_byte,
    tail_load_frame s .x20 (by decide) (by decide) (by decide)]

end CommitGolfCandidate.Chained.Native
