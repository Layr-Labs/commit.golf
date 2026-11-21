import CommitGolfCandidate.ChainedTailEmitBits

/-! Bit-list interpretation of the inverse reader's low-field mask. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem tail_bits_mask (width : Nat) (small : width≤6) :
    (1#64 <<< width)-1 = (BitVec.allOnes width).setWidth 64 := by
  interval_cases width <;> rfl

theorem tail_bits_word_take (bits : List Bool) (width : Nat) (small : width≤6) :
    tailBitsWord 64 bits &&& ((1#64 <<< width)-1) = tailBitsWord 64 (bits.take width) := by
  rw [tail_bits_mask width small]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [BitVec.getLsbD_and,tail_bits_word_bit 64 bits bit inside,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes,tail_bits_word_bit 64 _ bit inside]
  by_cases present : bit<width
  · have index : (bits.take width).getD bit false = bits.getD bit false := by
      simp [List.getD_eq_getElem?_getD,present]
    rw [index]
    simp [inside,present]
  · rw [List.getD_eq_default (bits.take width) false (by simp only [List.length_take]; omega)]
    simp [inside,present]

theorem tail_extract_bits (s : MachineState) (bits : List Bool) (width : Nat)
    (buffer : s.getReg .x23 = tailBitsWord 64 bits)
    (field : s.getReg .x26 = BitVec.ofNat 64 width) (small : width≤6) :
    (tailExtractPrefix s 6).getReg .x24 = tailBitsWord 64 (bits.take width) := by
  rw [tail_extract_value,buffer,field]
  have shift : (BitVec.ofNat 64 width).toNat%64 = width := by
    change (width%18446744073709551616)%64 = width
    omega
  rw [shift]
  exact tail_bits_word_take bits width small

theorem tail_extract_bits_buffer (s : MachineState) (bits : List Bool) (width : Nat)
    (buffer : s.getReg .x23 = tailBitsWord 64 bits) (bound : bits.length≤64)
    (field : s.getReg .x26 = BitVec.ofNat 64 width) (small : width≤6) :
    (tailExtractPrefix s 6).getReg .x23 = tailBitsWord 64 (bits.drop width) := by
  rw [tail_extract_buffer,buffer,field]
  have shift : (BitVec.ofNat 64 width).toNat%64 = width := by
    change (width%18446744073709551616)%64 = width
    omega
  rw [shift]
  exact tail_bits_word_drop 64 bits width bound

theorem tail_needs_bits (s : MachineState) (front : List Bool) (width : Nat)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (field : s.getReg .x26 = BitVec.ofNat 64 width) (pending : front.length<8) (small : width≤6) :
    tailNeedsByte s = decide (front.length<width) := by
  have reduced : front.length%18446744073709551616 = front.length := Nat.mod_eq_of_lt (by omega)
  have widthReduced : width%18446744073709551616 = width := Nat.mod_eq_of_lt (by omega)
  simp [tailNeedsByte,BitVec.ult,count,field,BitVec.toNat_ofNat,reduced,widthReduced]

theorem tail_read_loaded_bits (s : MachineState) (front byte : List Bool) (width : Nat)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (field : s.getReg .x26 = BitVec.ofNat 64 width)
    (input : s.getByte (s.getReg .x20) = tailBitsWord 8 byte)
    (byteBound : byte.length≤8) (pending : front.length<8) (small : width≤6) :
    (tailReadLoaded s).getReg .x23 =
      tailBitsWord 64 (if front.length<width then front++byte else front) := by
  have guardByte (query : Word) : (tailReadGuard s).getByte query = s.getByte query := by
    simp only [MachineState.getByte,tail_read_guard_memory]
  have wide : (tailBitsWord 8 byte).zeroExtend 64 = tailBitsWord 64 byte := by
    change (tailBitsWord 8 byte).setWidth 64 = _
    exact tail_bits_word_setWidth 8 64 byte byteBound
  have shift : (BitVec.ofNat 64 front.length).toNat%64 = front.length := by
    change (front.length%18446744073709551616)%64 = front.length
    omega
  have needs := tail_needs_bits s front width count field pending small
  by_cases more : front.length<width
  · have loads : tailNeedsByte s := by simp [needs,more]
    rw [tailReadLoaded,ite_eq_left loads,tail_refill_value]
    simp only [tail_read_guard_register,guardByte]
    erw [BitVec.add_zero]
    rw [input,wide,buffer,count,shift,ite_eq_left more]
    exact tail_bits_word_append front byte
  · have enough : ¬tailNeedsByte s := by simp [needs,more]
    rw [tailReadLoaded,ite_eq_right enough,tail_read_guard_register,buffer,ite_eq_right more]

theorem tail_read_bits (s : MachineState) (front byte : List Bool) (width : Nat)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (field : s.getReg .x26 = BitVec.ofNat 64 width)
    (input : s.getByte (s.getReg .x20) = tailBitsWord 8 byte)
    (byteBound : byte.length≤8) (pending : front.length<8) (small : width≤6) :
    (tailReadState s).getReg .x24 =
      tailBitsWord 64 ((if front.length<width then front++byte else front).take width) := by
  rw [tailReadState]
  apply tail_extract_bits _ _ width
  · exact tail_read_loaded_bits s front byte width buffer count field input byteBound pending small
  · rw [tail_read_loaded_frame s .x26 (by decide) (by decide) (by decide) (by decide)]
    exact field
  · exact small

theorem tail_read_bits_buffer (s : MachineState) (front byte : List Bool) (width : Nat)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (field : s.getReg .x26 = BitVec.ofNat 64 width)
    (input : s.getByte (s.getReg .x20) = tailBitsWord 8 byte)
    (byteBound : byte.length≤8) (pending : front.length<8) (small : width≤6) :
    (tailReadState s).getReg .x23 =
      tailBitsWord 64 ((if front.length<width then front++byte else front).drop width) := by
  rw [tailReadState]
  apply tail_extract_bits_buffer _ _ width
  · exact tail_read_loaded_bits s front byte width buffer count field input byteBound pending small
  · split
    · rw [List.length_append]
      omega
    · omega
  · rw [tail_read_loaded_frame s .x26 (by decide) (by decide) (by decide) (by decide)]
    exact field
  · exact small

theorem tail_read_bits_count (s : MachineState) (front byte : List Bool) (width : Nat)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (field : s.getReg .x26 = BitVec.ofNat 64 width)
    (byteSize : byte.length=8) (pending : front.length<8) (small : width≤6) :
    (tailReadState s).getReg .x25 =
      BitVec.ofNat 64 ((if front.length<width then front++byte else front).drop width).length := by
  have needs := tail_needs_bits s front width count field pending small
  have loaded : (tailReadLoaded s).getReg .x25 =
      BitVec.ofNat 64 (if front.length<width then front.length+8 else front.length) := by
    by_cases more : front.length<width
    · have loads : tailNeedsByte s := by simp [needs,more]
      rw [tailReadLoaded,ite_eq_left loads,tail_refill_count,tail_read_guard_register,count,ite_eq_left more]
      change BitVec.ofNat 64 front.length+BitVec.ofNat 64 8 = _
      rw [BitVec.ofNat_add]
    · have enough : ¬tailNeedsByte s := by simp [needs,more]
      rw [tailReadLoaded,ite_eq_right enough,tail_read_guard_register,count,ite_eq_right more]
  have length : (if front.length<width then front++byte else front).length =
      if front.length<width then front.length+8 else front.length := by
    split <;> simp [byteSize]
  have enough : width ≤ (if front.length<width then front.length+8 else front.length) := by
    split <;> omega
  rw [tailReadState,tail_extract_count,loaded,
    tail_read_loaded_frame s .x26 (by decide) (by decide) (by decide) (by decide),field,List.length_drop,length]
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) enough

end CommitGolfCandidate.Chained.Native
