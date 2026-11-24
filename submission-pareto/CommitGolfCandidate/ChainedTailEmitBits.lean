import CommitGolfCandidate.ChainedTailBits

/-! Native accumulator and byte-store interpretation for one bounded tail field. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem tail_append_bits (s : MachineState) (front back : List Bool)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (value : s.getReg .x24 = tailBitsWord 64 back)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length) (small : front.length<8) :
    (tailAppendPrefix s 3).getReg .x23 = tailBitsWord 64 (front++back) := by
  rw [tail_append_value,buffer,value,count]
  have shift : (BitVec.ofNat 64 front.length).toNat%64 = front.length := by
    change (front.length%18446744073709551616)%64 = front.length
    omega
  rw [shift]
  exact tail_bits_word_append front back

theorem tail_append_bits_count (s : MachineState) (front back : List Bool)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (width : s.getReg .x26 = BitVec.ofNat 64 back.length) :
    (tailAppendPrefix s 3).getReg .x25 = BitVec.ofNat 64 (front++back).length := by
  rw [tail_append_count,count,width,List.length_append,BitVec.ofNat_add]

theorem tail_emit_bits_guard (s : MachineState) (front back : List Bool)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (width : s.getReg .x26 = BitVec.ofNat 64 back.length)
    (eight : s.getReg .x27 = 8) (small : (front++back).length≤13) :
    tailSkips (tailAppendPrefix s 3) = decide ((front++back).length<8) := by
  apply tail_skips_count _ _ small (tail_append_bits_count s front back count width)
  rw [tail_append_frame s .x27 (by decide) (by decide) (by decide)]
  exact eight

theorem tail_emit_bits_byte (s : MachineState) (front back : List Bool)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (value : s.getReg .x24 = tailBitsWord 64 back)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (width : s.getReg .x26 = BitVec.ofNat 64 back.length) (eight : s.getReg .x27 = 8)
    (pending : front.length<8) (small : (front++back).length≤13) (query : Word) :
    (tailEmitState s).getByte query = if (front++back).length<8 then s.getByte query
      else if query=s.getReg .x20 then tailBitsWord 8 (front++back) else s.getByte query := by
  rw [tail_emit_byte,tail_emit_bits_guard s front back count width eight small,
    tail_append_bits s front back buffer value count pending,
    tail_bits_word_setWidth 64 8 (front++back) (by omega)]
  simp

theorem tail_emit_bits_value (s : MachineState) (front back : List Bool)
    (buffer : s.getReg .x23 = tailBitsWord 64 front)
    (value : s.getReg .x24 = tailBitsWord 64 back)
    (count : s.getReg .x25 = BitVec.ofNat 64 front.length)
    (width : s.getReg .x26 = BitVec.ofNat 64 back.length) (eight : s.getReg .x27 = 8)
    (pending : front.length<8) (small : (front++back).length≤13) :
    (tailEmitState s).getReg .x23 = if (front++back).length<8 then tailBitsWord 64 (front++back)
      else tailBitsWord 64 ((front++back).drop 8) := by
  rw [tail_emit_value,tail_emit_bits_guard s front back count width eight small,
    tail_append_bits s front back buffer value count pending,
    tail_bits_word_drop 64 (front++back) 8 (by omega)]
  simp

theorem tail_empty_bits (s : MachineState) (bits : List Bool)
    (count : s.getReg .x25 = BitVec.ofNat 64 bits.length) (small : bits.length<8) :
    tailEmpty s = decide (bits.length=0) := by
  rw [tailEmpty,count]
  change (bits.length%18446744073709551616 == 0) = decide (bits.length=0)
  rw [Nat.mod_eq_of_lt (by omega)]
  cases bits <;> rfl

theorem tail_finish_bits_byte (s : MachineState) (bits : List Bool)
    (buffer : s.getReg .x23 = tailBitsWord 64 bits)
    (count : s.getReg .x25 = BitVec.ofNat 64 bits.length) (small : bits.length<8) (query : Word) :
    (tailFinishState s).getByte query = if bits.length=0 then s.getByte query
      else if query=s.getReg .x20 then tailBitsWord 8 bits else s.getByte query := by
  rw [tail_finish_byte,tail_empty_bits s bits count small,buffer,
    tail_bits_word_setWidth 64 8 bits (by omega)]
  simp

theorem tail_finish_bits_padding (s : MachineState) (bits : List Bool)
    (buffer : s.getReg .x23 = tailBitsWord 64 bits)
    (count : s.getReg .x25 = BitVec.ofNat 64 bits.length) (small : bits.length<8)
    (nonempty : bits.length≠0) (bit : Nat) (inside : bit<8) (padding : bits.length≤bit) :
    ((tailFinishState s).getByte (s.getReg .x20)).getLsbD bit = false := by
  rw [tail_finish_bits_byte s bits buffer count small]
  simp only [nonempty,↓reduceIte,tail_bits_word_bit 8 bits bit inside]
  exact List.getD_eq_default bits false padding

end CommitGolfCandidate.Chained.Native
