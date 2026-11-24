import CommitGolfCandidate.ChainedTailParseMemory

/-! The native inverse flag enforces the exact consumed length and zero padding. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] tailParseStepState

theorem tail_parsed_fields_end_frame (n : Nat) (s : MachineState) :
    (tailParsedFieldsState n s).getReg .x19=s.getReg .x19 := by
  induction n generalizing s with
  | zero => rw [tail_parsed_fields_zero]
  | succ n ih =>
    rw [tail_parsed_fields_succ,ih (tailParseStepState s),
      tail_parse_step_frame s .x19 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]

theorem tail_bits_zero_iff (bits : List Bool) (fit : bits.length≤64) :
    tailBitsWord 64 bits=0#64 ↔ ∀ index, index<bits.length → bits.getD index false=false := by
  constructor
  · intro zero index inside
    have same := congrArg (fun word : BitVec 64 => word.getLsbD index) zero
    simpa only [tail_bits_word_bit 64 bits index (by omega),BitVec.getLsbD_zero] using same
  · intro zero
    apply BitVec.eq_of_getLsbD_eq
    intro index inside
    rw [tail_bits_word_bit 64 bits index inside,BitVec.getLsbD_zero]
    by_cases present : index<bits.length
    · exact zero index present
    · exact List.getD_eq_default bits false (by omega)

theorem native_tail_parse_result (widths : List Nat) (front : List Bool) (input : Nat → List Bool)
    (s : MachineState) (buffer : TailParseBuffer s front)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ width ∈ widths, width≤6)
    (table : ParseWidthsAt s (s.getReg .x21) widths)
    (memory : ParseInputAt s (s.getReg .x20) input widths.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (widths.map fun _ => []))
    (fit : 2*widths.length<2^64) (endBytes : Nat) (endFit : endBytes<2^64)
    (endPointer : s.getReg .x19=s.getReg .x20+BitVec.ofNat 64 endBytes) :
    let plan := tailParsePlan widths front input
    let after := tailValidatePrefix (tailParsedFieldsState widths.length s) 3
    after.getReg .x24=(if plan.read=endBytes ∧
        (∀ index, index<plan.carry.length → plan.carry.getD index false=false) then 1#64 else 0#64) ∧
    ∀ query, after.getByte query=writeParsedRows s.getByte (s.getReg .x21) plan.fields query := by
  obtain ⟨finalBuffer,finalMemory,finalPointer⟩ :=
    native_tail_parse_plan widths front input s buffer byteSize small table memory apart fit
  have consumed := tail_parse_plan_read_bound widths front input
  have endEq : s.getReg .x20+BitVec.ofNat 64 (tailParsePlan widths front input).read=s.getReg .x19 ↔
      (tailParsePlan widths front input).read=endBytes := by
    rw [endPointer]
    constructor
    · exact byte_offset_inj (s.getReg .x20) _ _ (by omega) endFit
    · intro same
      rw [same]
  constructor
  · rw [tail_validate_flag,finalPointer,tail_parsed_fields_end_frame,finalBuffer.value]
    simp only [endEq,tail_bits_zero_iff (tailParsePlan widths front input).carry
      (by have := finalBuffer.pending; omega)]
  · intro query
    have same : (tailValidatePrefix (tailParsedFieldsState widths.length s) 3).getByte query=
        (tailParsedFieldsState widths.length s).getByte query := by
      simp only [MachineState.getByte,tail_validate_memory]
    exact same.trans (finalMemory query)

example : (tailParsePlan [] [] (fun _ => List.replicate 8 false)).read=0 := rfl

example : (tailParsePlan [0,6,6,1] [] (fun _ => List.replicate 8 true)).read=2 := by decide +kernel

example : (tailParsePlan [1] [] (fun _ => List.replicate 8 true)).carry=List.replicate 7 true := by
  decide +kernel

example :
    let plan := tailParsePlan [1] [] (fun _ => List.replicate 8 false)
    decide (plan.read=1 ∧ tailBitsWord 64 plan.carry=0#64)=true := by decide +kernel

example :
    let plan := tailParsePlan [1] [] (fun _ => List.replicate 8 false)
    decide (plan.read=0 ∧ tailBitsWord 64 plan.carry=0#64)=false := by decide +kernel

example :
    let plan := tailParsePlan [1] [] (fun _ => List.replicate 8 false)
    decide (plan.read=2 ∧ tailBitsWord 64 plan.carry=0#64)=false := by decide +kernel

example :
    let plan := tailParsePlan [1] [] (fun _ => List.replicate 8 true)
    decide (plan.read=1 ∧ tailBitsWord 64 plan.carry=0#64)=false := by decide +kernel

end CommitGolfCandidate.Chained.Native
