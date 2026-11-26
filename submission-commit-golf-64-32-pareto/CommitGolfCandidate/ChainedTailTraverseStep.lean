import CommitGolfCandidate.ChainedTailLoad

/-! One actual field-row traversal, including decrement and the native back edge. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailDecrease (s : MachineState) : MachineState := execInstrBr s (.ADDI .x22 .x22 4095)
def tailMore (s : MachineState) : Bool := !(s.getReg .x22 == 0)
def tailBackEdge (s : MachineState) : MachineState := execInstrBr s (.BNE .x22 .x0 8144)

theorem tail_decrease_count (s : MachineState) : (tailDecrease s).getReg .x22 = s.getReg .x22-1 := by
  change s.getReg .x22+signExtend12 4095 = _
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem tail_decrease_frame (s : MachineState) (reg : Reg) (counter : reg ≠ .x22) :
    (tailDecrease s).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem tail_back_pc (s : MachineState) : (tailBackEdge s).pc =
    if tailMore s then s.pc+signExtend13 8144 else s.pc+4 := by
  change (if tailMore s then s.setPC (s.pc+signExtend13 8144) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_back_register (s : MachineState) (reg : Reg) : (tailBackEdge s).getReg reg = s.getReg reg := by
  by_cases more : tailMore s
  · have same : tailBackEdge s = s.setPC (s.pc+signExtend13 8144) := ite_eq_left more
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailBackEdge s = s.setPC (s.pc+4) := ite_eq_right more
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC

theorem tail_back_memory (s : MachineState) (query : Word) : (tailBackEdge s).getMem query = s.getMem query := by
  by_cases more : tailMore s
  · have same : tailBackEdge s = s.setPC (s.pc+signExtend13 8144) := ite_eq_left more
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : tailBackEdge s = s.setPC (s.pc+4) := ite_eq_right more
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC

def tailStepEmitted (s : MachineState) : MachineState := tailEmitState (tailLoadPrefix s 3)
def tailStepDecreased (s : MachineState) : MachineState := tailDecrease (tailStepEmitted s)
def tailStepState (s : MachineState) : MachineState := tailBackEdge (tailStepDecreased s)
def tailStepCycles (s : MachineState) : Nat := 5+tailEmitCycles (tailLoadPrefix s 3)

theorem tail_step_emitted_pc (s : MachineState) : (tailStepEmitted s).pc = s.pc+44 := by
  rw [tailStepEmitted,tail_emit_end_pc,tail_load_pc s 3 (by decide),BitVec.add_assoc]
  rfl

theorem tail_step_decreased_pc (s : MachineState) : (tailStepDecreased s).pc = s.pc+48 := by
  change (tailStepEmitted s).pc+4 = _
  rw [tail_step_emitted_pc,BitVec.add_assoc]
  rfl

theorem tail_step_end_pc (s : MachineState) (base : Word) (pc : s.pc = base+4) :
    (tailStepState s).pc = if tailMore (tailStepDecreased s) then base+4 else base+56 := by
  rw [tailStepState,tail_back_pc,tail_step_decreased_pc,pc]
  split <;> rw [BitVec.add_assoc,BitVec.add_assoc] <;> rfl

theorem tail_step_execution (image : Image) (base : Word) (code : TailTraverseAt image base)
    (s : MachineState) (pc : s.pc = base+4)
    (value : accessValid (s.getReg .x21) 1 = true)
    (width : accessValid (s.getReg .x21+1) 1 = true)
    (valid : ¬tailSkips (tailAppendPrefix (tailLoadPrefix s 3) 3) →
      accessValid ((tailLoadPrefix s 3).getReg .x20) 1 = true) (fuel : Nat) (coins : Bool) :
    execute image (tailStepCycles s+fuel) s coins =
      (do let result ← execute image fuel (tailStepState s) coins
          return result.charge (tailStepCycles s) 0) := by
  have emitted : (tailLoadPrefix s 3).pc = base+16 := by
    rw [tail_load_pc s 3 (by decide),pc,BitVec.add_assoc]
    rfl
  have decrement : fetch image (tailStepEmitted s) = some (.base (.ADDI .x22 .x22 4095)) := by
    apply code ⟨12,by decide⟩
    rw [tail_step_emitted_pc,pc,BitVec.add_assoc]
    rfl
  have branch : fetch image (tailStepDecreased s) = some (.base (.BNE .x22 .x0 8144)) := by
    apply code ⟨13,by decide⟩
    rw [tail_step_decreased_pc,pc,BitVec.add_assoc]
    rfl
  have down : ordinaryStep (tailStepEmitted s) (.base (.ADDI .x22 .x22 4095)) = some (tailStepDecreased s) := rfl
  have back : ordinaryStep (tailStepDecreased s) (.base (.BNE .x22 .x0 8144)) = some (tailStepState s) := rfl
  have splitFuel : tailStepCycles s+fuel = 3+(tailEmitCycles (tailLoadPrefix s 3)+((fuel+1)+1)) := by
    unfold tailStepCycles
    omega
  rw [splitFuel,tail_load_execution image base code s pc value width,
    tail_emit_execution image (base+16) code.emit _ emitted valid]
  simp only [bind_assoc,pure_bind]
  change (do let result ← execute image ((fuel+1)+1) (tailStepEmitted s) coins
             return (result.charge (tailEmitCycles (tailLoadPrefix s 3)) 0).charge 3 0) = _
  rw [execute_ordinary_step image _ _ _ (fuel+1) coins decrement down,
    execute_ordinary_step image _ _ _ fuel coins branch back]
  simp [tailStepCycles,Execution.charge,instructionCycles,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  congr 1
  funext result
  congr 1
  omega

theorem tail_step_counter (s : MachineState) : (tailStepState s).getReg .x22 = s.getReg .x22-1 := by
  rw [tailStepState,tail_back_register,tailStepDecreased,tail_decrease_count,
    tailStepEmitted,tail_emit_frame _ .x22 (by decide) (by decide) (by decide) (by decide),
    tail_load_frame s .x22 (by decide) (by decide) (by decide)]

theorem tail_step_source (s : MachineState) : (tailStepState s).getReg .x21 = s.getReg .x21+2 := by
  rw [tailStepState,tail_back_register,tailStepDecreased,tail_decrease_frame _ .x21 (by decide),
    tailStepEmitted,tail_emit_frame _ .x21 (by decide) (by decide) (by decide) (by decide),tail_load_pointer]

theorem tail_step_cycles_bound (s : MachineState) : tailStepCycles s ≤ 13 := by
  unfold tailStepCycles tailEmitCycles
  split <;> omega

end CommitGolfCandidate.Chained.Native
