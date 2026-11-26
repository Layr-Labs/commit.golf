import CommitGolfCandidate.ChainedTailParseEntry
import CommitGolfCandidate.ChainedTailReadBits
import CommitGolfCandidate.WriteMemory

/-! Byte-exact inverse-row stores and parsed field bits, without changing source memory. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] tailReadState
attribute [local irreducible] tailParseRead tailParseStored tailParseDecreased tailParseBack tailParseStepState

theorem tail_width_bits (s : MachineState) (width : Nat) (small : width≤6)
    (memory : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 width) :
    (tailWidthState s).getReg .x26=BitVec.ofNat 64 width := by
  change (s.getByte (s.getReg .x21+1)).zeroExtend 64=_
  rw [memory]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth_of_le (by decide)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem tail_parse_read_field (s : MachineState) (front byte : List Bool) (width : Nat)
    (buffer : s.getReg .x23=tailBitsWord 64 front)
    (count : s.getReg .x25=BitVec.ofNat 64 front.length)
    (field : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 width)
    (input : s.getByte (s.getReg .x20)=tailBitsWord 8 byte)
    (byteBound : byte.length≤8) (pending : front.length<8) (small : width≤6) :
    (tailParseRead s).getReg .x24=
      tailBitsWord 64 ((if front.length<width then front++byte else front).take width) := by
  rw [tailParseRead]
  apply tail_read_bits (tailWidthState s) front byte width
  · rw [tail_width_register s .x23 (by decide)]
    exact buffer
  · rw [tail_width_register s .x25 (by decide)]
    exact count
  · exact tail_width_bits s width small field
  · exact input
  · exact byteBound
  · exact pending
  · exact small

theorem tail_parse_store_byte (s : MachineState) (query : Word) :
    (tailParseStored s).getByte query=
      if query=s.getReg .x21 then ((tailParseRead s).getReg .x24).setWidth 8 else s.getByte query := by
  have pointer : (tailParseRead s).getReg .x21=s.getReg .x21 := by
    rw [tailParseRead,tail_read_frame _ .x21 (by decide) (by decide) (by decide) (by decide) (by decide),
      tail_width_register s .x21 (by decide)]
  rw [tailParseStored]
  change ((tailParseRead s).setByte ((tailParseRead s).getReg .x21+0#64)
    (((tailParseRead s).getReg .x24).truncate 8)).getByte query=_
  rw [BitVec.add_zero,CommitGolfCandidate.set_byte_read,pointer]
  have bytes : (tailParseRead s).getByte query=s.getByte query := by
    rw [tailParseRead,tail_read_byte]
    rfl
  rw [bytes]

private theorem parse_back_read (s : MachineState) (query : Word) :
    (tailParseBack s).getMem query=s.getMem query := by
  by_cases more : tailMore s
  · have same : tailParseBack s=s.setPC (s.pc+signExtend13 8128) := by
      rw [tailParseBack]
      exact ite_eq_left more
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : tailParseBack s=s.setPC (s.pc+4) := by
      rw [tailParseBack]
      exact ite_eq_right more
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC

private theorem parse_decrease_read (s : MachineState) (query : Word) :
    (tailDecrease s).getMem query=s.getMem query := rfl

theorem tail_parse_step_memory (s : MachineState) (query : Word) :
    (tailParseStepState s).getMem query=(tailParseStored s).getMem query := by
  rw [tailParseStepState,parse_back_read,tailParseDecreased]
  exact parse_decrease_read (tailParseStored s) query

theorem tail_parse_step_byte (s : MachineState) (query : Word) :
    (tailParseStepState s).getByte query=
      if query=s.getReg .x21 then ((tailParseRead s).getReg .x24).setWidth 8 else s.getByte query := by
  have same : (tailParseStepState s).getByte query=(tailParseStored s).getByte query := by
    simp only [MachineState.getByte,tail_parse_step_memory]
  exact same.trans (tail_parse_store_byte s query)

theorem tail_parse_step_bits_byte (s : MachineState) (front byte : List Bool) (width : Nat)
    (buffer : s.getReg .x23=tailBitsWord 64 front)
    (count : s.getReg .x25=BitVec.ofNat 64 front.length)
    (field : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 width)
    (input : s.getByte (s.getReg .x20)=tailBitsWord 8 byte)
    (byteBound : byte.length≤8) (pending : front.length<8) (small : width≤6) (query : Word) :
    (tailParseStepState s).getByte query=if query=s.getReg .x21 then
      tailBitsWord 8 ((if front.length<width then front++byte else front).take width) else s.getByte query := by
  rw [tail_parse_step_byte,tail_parse_read_field s front byte width buffer count field input byteBound pending small,
    tail_bits_word_setWidth 64 8 _ (by simp only [List.length_take]; omega)]

end CommitGolfCandidate.Chained.Native
