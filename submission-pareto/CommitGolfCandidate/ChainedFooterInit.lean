import CommitGolfCandidate.ChainedFooterDescend

/-! Initialize the actual footer cursor from the completed record-stream invariant. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def footerInitOps : List Instr :=
  [.ADDI .x19 .x0 0,.ADDI .x7 .x0 1,.SLLI .x7 .x7 33,.ADD .x7 .x7 .x17,
   .LUI .x8 1,.ADDI .x29 .x0 256,.ADDI .x30 .x0 1]
def footerInitPrefix (s : MachineState) (count : Nat) : MachineState := (footerInitOps.take count).foldl execInstrBr s

theorem opening_footer_init_layout : openingControllerOps=openingControllerOps.take 2071++
    footerInitOps++openingControllerOps.drop 2078 := by decide
theorem controller_footer_init_at : OpsAt openingControllerImage 12380 footerInitOps := by
  have code := opening_controller_ops_at
  rw [opening_footer_init_layout,List.append_assoc] at code
  have body := ops_at_right openingControllerImage 4096 (openingControllerOps.take 2071) _ code
  rw [List.length_take,opening_controller_ops_length] at body
  exact ops_at_left openingControllerImage _ _ _ body
private theorem init_succ (s : MachineState) (index : Nat) (inside : index<7) :
    footerInitPrefix s (index+1)=execInstrBr (footerInitPrefix s index) (footerInitOps.getD index .EBREAK) := by
  interval_cases index <;> rfl
theorem footer_init_pc (s : MachineState) (count : Nat) (inside : count≤7) :
    (footerInitPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [footerInitPrefix]
  | succ count ih =>
    rw [init_succ s count (by omega)]
    have step : (execInstrBr (footerInitPrefix s count) (footerInitOps.getD count .EBREAK)).pc=
        (footerInitPrefix s count).pc+4 := by
      have bounded : count<7 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4=_
    rw [←BitVec.ofNat_add]
    congr 1
theorem footer_init_register (s : MachineState) (reg : Reg)
    (a : reg≠.x7) (b : reg≠.x8) (c : reg≠.x19) (d : reg≠.x29) (e : reg≠.x30) :
    (footerInitPrefix s 7).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem footer_init_byte (s : MachineState) (query : Word) : (footerInitPrefix s 7).getByte query=s.getByte query := rfl
theorem footer_init_memory (s : MachineState) (query : Word) : (footerInitPrefix s 7).getMem query=s.getMem query := rfl
theorem footer_init_meta (s : MachineState) : (footerInitPrefix s 7).getReg .x7=s.getReg .x17+0x200000000 := by
  change ((1:Word)<<<33)+s.getReg .x17=s.getReg .x17+0x200000000
  rw [BitVec.add_comm]
  rfl
theorem footer_init_count (s : MachineState) : (footerInitPrefix s 7).getReg .x19=0 := rfl
theorem footer_init_marks (s : MachineState) : (footerInitPrefix s 7).getReg .x8=4096 := rfl
theorem footer_init_limit (s : MachineState) : (footerInitPrefix s 7).getReg .x29=256 := rfl
theorem footer_init_node (s : MachineState) : (footerInitPrefix s 7).getReg .x30=1 := rfl

theorem footer_init_execution (s : MachineState) (pc : s.pc=12380) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (7+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerInitPrefix s 7) coins
          return result.charge 7 0) := by
  apply execute_unit_steps (states := footerInitPrefix s)
  intro index inside
  refine ⟨.base (footerInitOps.getD index .EBREAK),?_,?_,?_⟩
  · apply controller_footer_init_at index (by simpa [footerInitOps] using inside)
    rw [footer_init_pc s index (by omega),pc]
  · rw [init_succ s index inside]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl

theorem record_stream_footer_entry (footer : Proof) (s : MachineState) (source output metadata : Nat)
    (ready : RecordStreamReady [] footer s source output metadata) :
    let next := footerInitPrefix s 7
    next.pc=12408 ∧ next.getReg .x5=BitVec.ofNat 64 source ∧ next.getReg .x6=BitVec.ofNat 64 output ∧
    next.getReg .x7=BitVec.ofNat 64 metadata ∧ BytesAt next (BitVec.ofNat 64 source) footer := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [footer_init_pc s 7 (by decide),show s.pc=12380 by simpa using ready.pc]
    rfl
  · rw [footer_init_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.sourcePointer
  · rw [footer_init_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ready.outputPointer
  · rw [footer_init_meta]
    exact ready.scratch
  · intro index inside
    rw [footer_init_byte]
    exact ready.memory index inside

end CommitGolfCandidate.Chained.Native
