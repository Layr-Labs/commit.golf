import CommitGolfCandidate.ChainedTailParseResult
import CommitGolfCandidate.ChainedTailAccess

/-! Derive inverse-row access and loop-control premises from physical buffer ranges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] tailParseStepState tailParseRead

theorem tail_parsed_rows_access (widths : List Nat) (front : List Bool) (input : Nat → List Bool)
    (s : MachineState) (source destination : Nat) (buffer : TailParseBuffer s front)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ width ∈ widths, width≤6)
    (table : ParseWidthsAt s (s.getReg .x21) widths)
    (memory : ParseInputAt s (s.getReg .x20) input widths.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (widths.map fun _ => []))
    (sourcePointer : s.getReg .x21=BitVec.ofNat 64 source)
    (inputPointer : s.getReg .x20=BitVec.ofNat 64 destination)
    (count : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (sourceRoom : source+2*widths.length≤MEMORY_BYTES)
    (inputRoom : destination+widths.length+1≤MEMORY_BYTES) :
    TailParsedFieldsReady widths.length s := by
  induction widths generalizing front input s source destination with
  | nil => trivial
  | cons width widths ih =>
    have fit : 2*(width::widths).length<2^64 := by unfold MEMORY_BYTES at sourceRoom; omega
    have bound := small width (by simp)
    have field := parse_width_head s width widths table
    have headInput : s.getByte (s.getReg .x20)=tailBitsWord 8 (input 0) := by
      simpa using memory 0 (by omega)
    let advance := if front.length<width then 1 else 0
    have stepBound : advance≤1 := by unfold advance; split <;> omega
    have pointer : (tailParseStepState s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 advance := by
      rw [tail_parse_step_input s front width buffer field bound]
      by_cases more : front.length<width <;> simp [advance,more]
    have nextBuffer := tail_parse_step_buffer s front (input 0) width buffer field headInput (byteSize 0) bound
    have nextTable := tail_parse_step_width_memory s width widths table fit
    have nextMemory := tail_parse_step_input_memory s width widths input advance stepBound pointer memory apart
    have nextApart : TailApart ((tailParseStepState s).getReg .x21)
        ((tailParseStepState s).getReg .x20) (widths.map fun _ => []) := by
      rw [tail_parse_step_source,pointer]
      exact tail_apart_shift (s.getReg .x21) (s.getReg .x20) [] (widths.map fun _ => []) apart advance stepBound
    have nextSource : (tailParseStepState s).getReg .x21=BitVec.ofNat 64 (source+2) := by
      rw [tail_parse_step_source,sourcePointer,BitVec.ofNat_add]
      rfl
    have nextInput : (tailParseStepState s).getReg .x20=BitVec.ofNat 64 (destination+advance) := by
      rw [pointer,inputPointer,BitVec.ofNat_add]
    have nextCount : (tailParseStepState s).getReg .x22=BitVec.ofNat 64 widths.length := by
      rw [tail_parse_step_counter,count]
      have one : (1 : Word)=BitVec.ofNat 64 1 := by decide +kernel
      rw [one]
      have result := BitVec.ofNat_sub_ofNat_of_le (width::widths).length 1 (by decide : 1<2^64) (by simp)
      simpa only [List.length_cons,Nat.add_sub_cancel] using result
    have decreased : (tailParseDecreased s).getReg .x22=BitVec.ofNat 64 widths.length := by
      simpa only [tailParseStepState,tail_parse_back_register] using nextCount
    have more : tailMore (tailParseDecreased s)=decide (widths.length≠0) := by
      have bounded : widths.length<2^64 := by simp only [List.length_cons] at fit; omega
      rw [tailMore,decreased]
      change (!(widths.length%2^64 == 0))=decide (widths.length≠0)
      rw [Nat.mod_eq_of_lt bounded]
      cases widths <;> rfl
    have rest := ih (nextParsedBits front (input 0) width) (fun i => input (advance+i))
      (tailParseStepState s) (source+2) (destination+advance) nextBuffer (fun i => byteSize _)
      (fun value member => small value (by simp [member])) nextTable nextMemory nextApart
      nextSource nextInput nextCount
      (by simp only [List.length_cons] at sourceRoom; omega)
      (by simp only [List.length_cons] at inputRoom; omega)
    have numeric : (s.getReg .x21).toNat=source := by
      rw [sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at sourceRoom
      omega
    have inputNumeric : (s.getReg .x20).toNat=destination := by
      rw [inputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at inputRoom
      omega
    refine ⟨?_,?_,?_,more,rest⟩
    · exact byte_access_offset (s.getReg .x21) 1 (by rw [numeric]; simp only [List.length_cons] at sourceRoom; omega)
    · intro _
      rw [tail_width_register _ .x20 (by decide)]
      simpa using byte_access_offset (s.getReg .x20) 0 (by rw [inputNumeric]; omega)
    · rw [tailParseRead,
        tail_read_frame _ .x21 (by decide) (by decide) (by decide) (by decide) (by decide),
        tail_width_register _ .x21 (by decide)]
      simpa using byte_access_offset (s.getReg .x21) 0
        (by rw [numeric]; simp only [List.length_cons] at sourceRoom; omega)

end CommitGolfCandidate.Chained.Native
