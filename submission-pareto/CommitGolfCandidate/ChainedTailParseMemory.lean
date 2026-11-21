import CommitGolfCandidate.ChainedTailParseSource

/-! Complete inverse-row memory and cursor refinement to an independent stream plan. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] tailParseStepState

def writeParsedRows (memory : Word → BitVec 8) (base : Word) : List (List Bool) → Word → BitVec 8
  | [] => memory
  | bits::rows => writeParsedRows (storeByteFn memory base (tailBitsWord 8 bits)) (base+2) rows

theorem native_tail_parse_plan (widths : List Nat) (front : List Bool) (input : Nat → List Bool)
    (s : MachineState) (buffer : TailParseBuffer s front)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ width ∈ widths, width≤6)
    (table : ParseWidthsAt s (s.getReg .x21) widths)
    (memory : ParseInputAt s (s.getReg .x20) input widths.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (widths.map fun _ => []))
    (fit : 2*widths.length<2^64) :
    TailParseBuffer (tailParsedFieldsState widths.length s) (tailParsePlan widths front input).carry ∧
    (∀ query, (tailParsedFieldsState widths.length s).getByte query=
      writeParsedRows s.getByte (s.getReg .x21) (tailParsePlan widths front input).fields query) ∧
    (tailParsedFieldsState widths.length s).getReg .x20=
      s.getReg .x20+BitVec.ofNat 64 (tailParsePlan widths front input).read := by
  induction widths generalizing front input s with
  | nil =>
    simp only [List.length_nil,tail_parsed_fields_zero,tailParsePlan,writeParsedRows]
    exact ⟨buffer,by simp,by simp⟩
  | cons width widths ih =>
    let advance := if front.length<width then 1 else 0
    let shifted := fun i => input (advance+i)
    have stepBound : advance≤1 := by unfold advance; split <;> omega
    have bound := small width (by simp)
    have field := parse_width_head s width widths table
    have headInput : s.getByte (s.getReg .x20)=tailBitsWord 8 (input 0) := by
      simpa using memory 0 (by omega)
    have nextBuffer := tail_parse_step_buffer s front (input 0) width buffer field headInput (byteSize 0) bound
    have nextTable := tail_parse_step_width_memory s width widths table fit
    have pointer : (tailParseStepState s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 advance := by
      rw [tail_parse_step_input s front width buffer field bound]
      by_cases more : front.length<width <;> simp [advance,more]
    have nextMemory := tail_parse_step_input_memory s width widths input advance stepBound pointer memory apart
    have nextApart : TailApart ((tailParseStepState s).getReg .x21)
        ((tailParseStepState s).getReg .x20) (widths.map fun _ => []) := by
      rw [tail_parse_step_source,pointer]
      exact tail_apart_shift (s.getReg .x21) (s.getReg .x20) [] (widths.map fun _ => []) apart advance stepBound
    have restSmall : ∀ value ∈ widths, value≤6 := fun value member => small value (by simp [member])
    obtain ⟨finalBuffer,finalMemory,finalPointer⟩ :=
      ih (nextParsedBits front (input 0) width) shifted (tailParseStepState s) nextBuffer
        (fun i => byteSize _) restSmall nextTable nextMemory nextApart
        (by simp only [List.length_cons] at fit; omega)
    rw [List.length_cons,tail_parsed_fields_succ]
    refine ⟨finalBuffer,?_,?_⟩
    · have stepMemory : (tailParseStepState s).getByte=storeByteFn s.getByte (s.getReg .x21)
          (tailBitsWord 8 ((if front.length<width then front++input 0 else front).take width)) := by
        funext query
        exact tail_parse_step_bits_byte s front (input 0) width buffer.value buffer.count field headInput
          (le_of_eq (byteSize 0)) buffer.pending bound query
      intro query
      have observed := finalMemory query
      rw [stepMemory,tail_parse_step_source] at observed
      exact observed
    · rw [pointer,byte_offset_add] at finalPointer
      exact finalPointer

end CommitGolfCandidate.Chained.Native
