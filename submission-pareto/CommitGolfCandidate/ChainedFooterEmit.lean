import CommitGolfCandidate.ChainedFooterFieldCode

/-! Actual footer field emission: width selection, low copy, descriptor and row counter. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def footerCountState (s : MachineState) : MachineState := execInstrBr s (.ADDI .x19 .x19 1)
def footerEmitState (s : MachineState) : MachineState := footerCountState (fieldBuildState 29 (footerHeaderState s))
def footerEmitCycles (s : MachineState) : Nat := footerHeaderCycles s+122

theorem footer_count_byte (s : MachineState) (query : Word) : (footerCountState s).getByte query=s.getByte query := rfl
theorem footer_count_register (s : MachineState) (reg : Reg) (different : reg≠.x19) :
    (footerCountState s).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem footer_count_value (s : MachineState) : (footerCountState s).getReg .x19=s.getReg .x19+1 := rfl
theorem footer_count_pc (s : MachineState) : (footerCountState s).pc=s.pc+4 := rfl
theorem footer_emit_pc (s : MachineState) (pc : s.pc=12436) : (footerEmitState s).pc=12940 := by
  rw [footerEmitState,footer_count_pc,field_build_pc,footer_header_pc,pc]
  rfl
theorem footer_emit_register (s : MachineState) (reg : Reg)
    (a : reg≠.x5) (b : reg≠.x6) (c : reg≠.x7) (d : reg≠.x9) (e : reg≠.x10) (f : reg≠.x11) (g : reg≠.x19) :
    (footerEmitState s).getReg reg=s.getReg reg := by
  rw [footerEmitState,footer_count_register _ reg g,field_build_frame _ _ reg a b c f,footer_header_register _ reg d e]
theorem footer_emit_counter (s : MachineState) : (footerEmitState s).getReg .x19=s.getReg .x19+1 := by
  rw [footerEmitState,footer_count_value,field_build_frame _ _ .x19 (by decide) (by decide) (by decide) (by decide),
    footer_header_register _ .x19 (by decide) (by decide)]

theorem footer_emit_memory (field : RawField) (rest : Proof) (s : MachineState) (source output metadata node : Nat)
    (lowSize : field.low.length=29) (padding : field.padding=[])
    (highSize : field.high.length=InteriorCodec.footerWidth node-232) (nodeFit : node<2^64)
    (nodeReg : s.getReg .x30=BitVec.ofNat 64 node) (limit : s.getReg .x29=256)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source) (outputReg : s.getReg .x6=BitVec.ofNat 64 output)
    (metaReg : s.getReg .x7=BitVec.ofNat 64 metadata)
    (memory : BytesAt s (BitVec.ofNat 64 source) (field.bytes++rest))
    (ordered : output≤source) (separate : source+30+rest.length≤metadata) (room : metadata+2<2^64) :
    BytesAt (footerEmitState s) (BitVec.ofNat 64 output) field.low ∧
    BytesAt (footerEmitState s) (BitVec.ofNat 64 metadata) (descriptorBytes [field.high]) ∧
    BytesAt (footerEmitState s) (BitVec.ofNat 64 (source+30)) rest ∧
    (footerEmitState s).getReg .x5=BitVec.ofNat 64 (source+30) ∧
    (footerEmitState s).getReg .x6=BitVec.ofNat 64 (output+29) ∧
    (footerEmitState s).getReg .x7=BitVec.ofNat 64 (metadata+2) := by
  have sourceHeader : (footerHeaderState s).getReg .x5=BitVec.ofNat 64 source := by
    rw [footer_header_register _ _ (by decide) (by decide),sourceReg]
  have outputHeader : (footerHeaderState s).getReg .x6=BitVec.ofNat 64 output := by
    rw [footer_header_register _ _ (by decide) (by decide),outputReg]
  have metaHeader : (footerHeaderState s).getReg .x7=BitVec.ofNat 64 metadata := by
    rw [footer_header_register _ _ (by decide) (by decide),metaReg]
  have input : BytesAt (footerHeaderState s) (BitVec.ofNat 64 source)
      (field.low++tailBitsWord 8 field.high::([]++rest)) := by
    intro index inside
    rw [footer_header_byte]
    have view : field.bytes++rest=field.low++tailBitsWord 8 field.high::([]++rest) := by
      simp only [RawField.bytes,padding,List.append_assoc,List.cons_append,List.nil_append]
    rw [←view] at inside ⊢
    exact memory index inside
  have width : (footerHeaderState s).getReg .x10=BitVec.ofNat 64 field.high.length := by
    rw [highSize]
    exact footer_header_width s node nodeFit nodeReg limit
  have result := native_raw_field field.low [] rest field.high (footerHeaderState s) source output metadata
    sourceHeader outputHeader metaHeader (footer_header_skip s) width input ordered
    (by simpa only [lowSize,List.length_nil,Nat.add_zero,Nat.add_assoc] using separate) room
  rw [lowSize] at result
  rcases result with ⟨body,rows,future,sourceNext,outputNext,metaNext⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro index inside
    rw [footerEmitState,footer_count_byte]
    exact body index inside
  · intro index inside
    rw [footerEmitState,footer_count_byte]
    exact rows index inside
  · intro index inside
    rw [footerEmitState,footer_count_byte]
    exact future index inside
  · rw [footerEmitState,footer_count_register _ _ (by decide)]
    exact sourceNext
  · rw [footerEmitState,footer_count_register _ _ (by decide)]
    exact outputNext
  · rw [footerEmitState,footer_count_register _ _ (by decide)]
    exact metaNext

theorem footer_emit_execution (s : MachineState) (pc : s.pc=12436)
    (source output metadata : Nat)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source) (outputReg : s.getReg .x6=BitVec.ofNat 64 output)
    (metaReg : s.getReg .x7=BitVec.ofNat 64 metadata)
    (ordered : output≤source) (separate : source+30≤metadata) (capacity : metadata+2≤MEMORY_BYTES)
    (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (footerEmitCycles s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerEmitState s) coins
          return result.charge (footerEmitCycles s) 0) := by
  have headerCode := controller_footer_header_at openingControllerImage 4096 opening_controller_ops_at
  have fieldCode := controller_footer_field_at openingControllerImage 4096 opening_controller_ops_at
  have bodyPC : (footerHeaderState s).pc=12452 := by rw [footer_header_pc,pc]; rfl
  have numeric : source<2^64 ∧ output<2^64 ∧ metadata<2^64 := by unfold MEMORY_BYTES at capacity; omega
  have sourceNat : ((footerHeaderState s).getReg .x5).toNat=source := by
    rw [footer_header_register _ _ (by decide) (by decide),sourceReg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt numeric.1]
  have outputNat : ((footerHeaderState s).getReg .x6).toNat=output := by
    rw [footer_header_register _ _ (by decide) (by decide),outputReg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt numeric.2.1]
  have metaNat : ((footerHeaderState s).getReg .x7).toNat=metadata := by
    rw [footer_header_register _ _ (by decide) (by decide),metaReg,BitVec.toNat_ofNat,Nat.mod_eq_of_lt numeric.2.2]
  have access := field_build_access 29 (footerHeaderState s)
    (by rw [sourceNat]; omega) (by rw [outputNat]; omega) (by rw [metaNat]; exact capacity)
  have counterPC : (fieldBuildState 29 (footerHeaderState s)).pc=12936 := by rw [field_build_pc,bodyPC]; rfl
  have counter : fetch openingControllerImage (fieldBuildState 29 (footerHeaderState s))=
      some (.base (.ADDI .x19 .x19 1)) := fieldCode.2.2 0 (by decide) _ (by simpa using counterPC)
  have ordinary : ordinaryStep (fieldBuildState 29 (footerHeaderState s)) (.base (.ADDI .x19 .x19 1))=
      some (footerCountState (fieldBuildState 29 (footerHeaderState s))) := rfl
  rw [show footerEmitCycles s+fuel=footerHeaderCycles s+(4*29+5+(fuel+1)) by unfold footerEmitCycles; omega,
    footer_header_execution openingControllerImage 12436 headerCode s pc,
    field_build_execution openingControllerImage 12452 29 fieldCode.1 fieldCode.2.1 _ bodyPC
      access.1 access.2.1 access.2.2.1 access.2.2.2,
    execute_ordinary_step openingControllerImage _ _ _ fuel coins counter ordinary]
  simp [footerEmitState,footerEmitCycles,Execution.charge,instructionCycles,←Nat.add_assoc]

theorem footer_emit_bound (s : MachineState) : footerEmitCycles s≤126 := by
  unfold footerEmitCycles footerHeaderCycles
  split <;> omega

end CommitGolfCandidate.Chained.Native
