import CommitGolfCandidate.ChainedTailParseAccess

/-! Couple inverse-row memory and strict-tail flags to actual instruction execution. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem native_parsed_rows (image : Image) (base : Word) (code : TailParseAt image base)
    (widths : List Nat) (front : List Bool) (input : Nat → List Bool)
    (s : MachineState) (source destination : Nat)
    (pc : s.pc=if widths.length=0 then base+72 else base+4)
    (buffer : TailParseBuffer s front)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ width ∈ widths, width≤6)
    (table : ParseWidthsAt s (s.getReg .x21) widths)
    (memory : ParseInputAt s (s.getReg .x20) input widths.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) (widths.map fun _ => []))
    (sourcePointer : s.getReg .x21=BitVec.ofNat 64 source)
    (inputPointer : s.getReg .x20=BitVec.ofNat 64 destination)
    (count : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (sourceRoom : source+2*widths.length≤MEMORY_BYTES)
    (inputRoom : destination+widths.length+1≤MEMORY_BYTES)
    (endBytes : Nat) (endFit : endBytes<2^64)
    (endPointer : s.getReg .x19=s.getReg .x20+BitVec.ofNat 64 endBytes) :
    let plan := tailParsePlan widths front input
    ∃ (after : MachineState) (cycles : Nat),
      after.pc=base+84 ∧ cycles≤17*widths.length+3 ∧
      (∀ fuel coins, execute image (cycles+fuel) s coins=
        (do let result ← execute image fuel after coins
            return result.charge cycles 0)) ∧
      after.getReg .x24=(if plan.read=endBytes ∧
        (∀ index, index<plan.carry.length → plan.carry.getD index false=false) then 1#64 else 0#64) ∧
      ∀ query, after.getByte query=writeParsedRows s.getByte (s.getReg .x21) plan.fields query := by
  have ready := tail_parsed_rows_access widths front input s source destination buffer byteSize small
    table memory apart sourcePointer inputPointer count sourceRoom inputRoom
  have fit : 2*widths.length<2^64 := by unfold MEMORY_BYTES at sourceRoom; omega
  have content := native_tail_parse_result widths front input s buffer byteSize small table memory apart fit
    endBytes endFit endPointer
  refine ⟨tailValidatePrefix (tailParsedFieldsState widths.length s) 3,
    tailParsedFieldsCycles widths.length s+3,?_,?_,?_,content.1,content.2⟩
  · exact tail_parsed_fields_validate_pc widths.length s base pc ready
  · have bound := tail_parsed_fields_bound widths.length s
    omega
  · intro fuel coins
    exact tail_parsed_fields_validate_execution image base code widths.length s pc ready fuel coins

end CommitGolfCandidate.Chained.Native
