import CommitGolfCandidate.ChainedTailParseBits

/-! Cursor, accumulator and register invariants for native inverse rows. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] tailReadState tailParseRead tailParseStored
  tailParseDecreased tailParseBack tailParseStepState

structure TailParseBuffer (s : MachineState) (bits : List Bool) : Prop where
  value : s.getReg .x23=tailBitsWord 64 bits
  count : s.getReg .x25=BitVec.ofNat 64 bits.length
  pending : bits.length<8

def nextParsedBits (front byte : List Bool) (width : Nat) : List Bool :=
  (if front.length<width then front++byte else front).drop width

theorem next_parsed_pending (front byte : List Bool) (width : Nat)
    (pending : front.length<8) (byteSize : byte.length=8) :
    (nextParsedBits front byte width).length<8 := by
  unfold nextParsedBits
  split <;> simp only [List.length_drop,List.length_append] <;> omega

theorem tail_parse_back_register (s : MachineState) (reg : Reg) :
    (tailParseBack s).getReg reg=s.getReg reg := by
  by_cases more : tailMore s
  · have same : tailParseBack s=s.setPC (s.pc+signExtend13 8128) := by
      rw [tailParseBack]
      exact ite_eq_left more
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailParseBack s=s.setPC (s.pc+4) := by
      rw [tailParseBack]
      exact ite_eq_right more
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC

theorem tail_parsed_store_register (s : MachineState) (reg : Reg) (pointer : reg≠.x21) :
    (tailParsedStorePrefix s 2).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem tail_parsed_store_pointer (s : MachineState) :
    (tailParsedStorePrefix s 2).getReg .x21=s.getReg .x21+2 := rfl

theorem tail_parse_step_read_register (s : MachineState) (reg : Reg)
    (pointer : reg≠.x21) (counter : reg≠.x22) :
    (tailParseStepState s).getReg reg=(tailParseRead s).getReg reg := by
  rw [tailParseStepState,tail_parse_back_register,tailParseDecreased,
    tail_decrease_frame _ reg counter,tailParseStored,tail_parsed_store_register _ reg pointer]

theorem tail_read_pointer (s : MachineState) :
    (tailReadState s).getReg .x20=if tailNeedsByte s then s.getReg .x20+1 else s.getReg .x20 := by
  rw [tailReadState,tail_extract_frame _ .x20 (by decide) (by decide) (by decide) (by decide)]
  by_cases needs : tailNeedsByte s
  · rw [tailReadLoaded,ite_eq_left needs,tail_refill_pointer,tail_read_guard_register,ite_eq_left needs]
  · rw [tailReadLoaded,ite_eq_right needs,tail_read_guard_register,ite_eq_right needs]

theorem tail_parse_step_source (s : MachineState) :
    (tailParseStepState s).getReg .x21=s.getReg .x21+2 := by
  rw [tailParseStepState,tail_parse_back_register,tailParseDecreased,
    tail_decrease_frame _ .x21 (by decide),tailParseStored,tail_parsed_store_pointer,
    tailParseRead,tail_read_frame _ .x21 (by decide) (by decide) (by decide) (by decide) (by decide),
    tail_width_register _ .x21 (by decide)]

theorem tail_parse_step_counter (s : MachineState) :
    (tailParseStepState s).getReg .x22=s.getReg .x22-1 := by
  rw [tailParseStepState,tail_parse_back_register,tailParseDecreased,tail_decrease_count,
    tailParseStored,tail_parsed_store_register _ .x22 (by decide),tailParseRead,
    tail_read_frame _ .x22 (by decide) (by decide) (by decide) (by decide) (by decide),
    tail_width_register _ .x22 (by decide)]

theorem tail_width_parse_buffer (s : MachineState) (front : List Bool) (buffer : TailParseBuffer s front) :
    TailParseBuffer (tailWidthState s) front := by
  constructor
  · rw [tail_width_register s .x23 (by decide)]
    exact buffer.value
  · rw [tail_width_register s .x25 (by decide)]
    exact buffer.count
  · exact buffer.pending

theorem tail_parse_step_buffer (s : MachineState) (front byte : List Bool) (width : Nat)
    (buffer : TailParseBuffer s front)
    (field : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 width)
    (input : s.getByte (s.getReg .x20)=tailBitsWord 8 byte)
    (byteSize : byte.length=8) (small : width≤6) :
    TailParseBuffer (tailParseStepState s) (nextParsedBits front byte width) := by
  have loaded := tail_width_parse_buffer s front buffer
  have fieldReg := tail_width_bits s width small field
  have inputByte : (tailWidthState s).getByte ((tailWidthState s).getReg .x20)=tailBitsWord 8 byte := input
  constructor
  · rw [tail_parse_step_read_register s .x23 (by decide) (by decide),tailParseRead]
    exact tail_read_bits_buffer _ front byte width loaded.value loaded.count fieldReg inputByte
      (by omega) loaded.pending small
  · rw [tail_parse_step_read_register s .x25 (by decide) (by decide),tailParseRead]
    exact tail_read_bits_count _ front byte width loaded.count fieldReg byteSize loaded.pending small
  · exact next_parsed_pending front byte width buffer.pending byteSize

theorem tail_parse_step_input (s : MachineState) (front : List Bool) (width : Nat)
    (buffer : TailParseBuffer s front)
    (field : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 width) (small : width≤6) :
    (tailParseStepState s).getReg .x20=
      if front.length<width then s.getReg .x20+1 else s.getReg .x20 := by
  have loaded := tail_width_parse_buffer s front buffer
  have needs := tail_needs_bits (tailWidthState s) front width loaded.count
    (tail_width_bits s width small field) loaded.pending small
  rw [tail_parse_step_read_register s .x20 (by decide) (by decide),tailParseRead,tail_read_pointer,needs,
    tail_width_register _ .x20 (by decide)]
  by_cases more : front.length<width <;> simp [more]

theorem tail_parse_step_frame (s : MachineState) (reg : Reg)
    (input : reg≠.x20) (pointer : reg≠.x21) (counter : reg≠.x22) (buffer : reg≠.x23)
    (value : reg≠.x24) (count : reg≠.x25) (width : reg≠.x26) (mask : reg≠.x28) :
    (tailParseStepState s).getReg reg=s.getReg reg := by
  rw [tail_parse_step_read_register s reg pointer counter,tailParseRead,
    tail_read_frame _ reg input buffer value count mask,tail_width_register _ reg width]

end CommitGolfCandidate.Chained.Native
