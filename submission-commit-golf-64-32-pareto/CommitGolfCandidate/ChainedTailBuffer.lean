import CommitGolfCandidate.ChainedTailRowBits

/-! Accumulator and cursor invariants preserved by a complete native row. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure TailBuffer (s : MachineState) (bits : List Bool) : Prop where
  value : s.getReg .x23=tailBitsWord 64 bits
  count : s.getReg .x25=BitVec.ofNat 64 bits.length
  eight : s.getReg .x27=8
  pending : bits.length<8

def nextTailBits (front back : List Bool) : List Bool :=
  if (front++back).length<8 then front++back else (front++back).drop 8

theorem next_tail_pending (front back : List Bool) (pending : front.length<8) (small : back.length≤6) :
    (nextTailBits front back).length<8 := by
  unfold nextTailBits
  split
  · assumption
  · simp only [List.length_drop,List.length_append]
    omega

theorem tail_emit_buffer (s : MachineState) (front back : List Bool) (buffer : TailBuffer s front)
    (value : s.getReg .x24=tailBitsWord 64 back) (width : s.getReg .x26=BitVec.ofNat 64 back.length)
    (small : back.length≤6) : TailBuffer (tailEmitState s) (nextTailBits front back) := by
  have bound : (front++back).length≤13 := by simp only [List.length_append]; have := buffer.pending; omega
  constructor
  · have result := tail_emit_bits_value s front back buffer.value value buffer.count width buffer.eight buffer.pending bound
    simpa only [nextTailBits,apply_ite] using result
  · rw [tail_emit_count,tail_emit_bits_guard s front back buffer.count width buffer.eight bound,
      tail_append_bits_count s front back buffer.count width]
    by_cases fits : (front++back).length<8
    · have sumFits : front.length+back.length<8 := by simpa using fits
      simp [nextTailBits,List.length_append,sumFits]
    · simp only [fits,decide_false,Bool.false_eq_true,↓reduceIte,nextTailBits,List.length_drop]
      exact BitVec.ofNat_sub_ofNat_of_le ((front++back).length) 8 (by decide) (by omega)
  · rw [tail_emit_frame s .x27 (by decide) (by decide) (by decide) (by decide)]
    exact buffer.eight
  · exact next_tail_pending front back buffer.pending small

theorem tail_step_emit_register (s : MachineState) (reg : Reg) (counter : reg≠.x22) :
    (tailStepState s).getReg reg=(tailEmitState (tailLoadPrefix s 3)).getReg reg := by
  rw [tailStepState,tail_back_register,tailStepDecreased,tail_decrease_frame _ reg counter]
  rfl

theorem tail_load_buffer (s : MachineState) (front : List Bool) (buffer : TailBuffer s front) :
    TailBuffer (tailLoadPrefix s 3) front := by
  constructor
  · rw [tail_load_frame s .x23 (by decide) (by decide) (by decide)]
    exact buffer.value
  · rw [tail_load_frame s .x25 (by decide) (by decide) (by decide)]
    exact buffer.count
  · rw [tail_load_frame s .x27 (by decide) (by decide) (by decide)]
    exact buffer.eight
  · exact buffer.pending

theorem tail_step_buffer (s : MachineState) (front back : List Bool) (buffer : TailBuffer s front)
    (value : s.getByte (s.getReg .x21)=tailBitsWord 8 back)
    (width : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 back.length)
    (small : back.length≤6) : TailBuffer (tailStepState s) (nextTailBits front back) := by
  have loaded := tail_load_field_bits s back small value width
  have result := tail_emit_buffer _ front back (tail_load_buffer s front buffer) loaded.1 loaded.2 small
  constructor
  · rw [tail_step_emit_register s .x23 (by decide)]
    exact result.value
  · rw [tail_step_emit_register s .x25 (by decide)]
    exact result.count
  · rw [tail_step_emit_register s .x27 (by decide)]
    exact result.eight
  · exact result.pending

theorem tail_step_bits_pointer (s : MachineState) (front back : List Bool) (buffer : TailBuffer s front)
    (value : s.getByte (s.getReg .x21)=tailBitsWord 8 back)
    (width : s.getByte (s.getReg .x21+1)=BitVec.ofNat 8 back.length)
    (small : back.length≤6) :
    (tailStepState s).getReg .x20=if (front++back).length<8 then s.getReg .x20 else s.getReg .x20+1 := by
  have loaded := tail_load_field_bits s back small value width
  have state := tail_load_buffer s front buffer
  rw [tail_step_emit_register s .x20 (by decide),tail_emit_pointer,
    tail_emit_bits_guard _ front back state.count loaded.2 state.eight (by
      simp only [List.length_append]; have := buffer.pending; omega),
    tail_load_frame s .x20 (by decide) (by decide) (by decide)]
  simp

end CommitGolfCandidate.Chained.Native
