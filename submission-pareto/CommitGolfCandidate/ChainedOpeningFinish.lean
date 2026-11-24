import CommitGolfCandidate.ChainedFooterTailReady

/-! The actual opener finalization writes its result ABI and halts successfully. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[local simp] private theorem finish_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def openingFinishOps : List Instr :=
  [.ADDI .x6 .x20 0,.SUB .x11 .x6 .x17,.ADDI .x5 .x0 1,.ADDI .x10 .x0 0,.ECALL]
def openingFinishPrefix (s : MachineState) (count : Nat) : MachineState :=
  (openingFinishOps.take count).foldl execInstrBr s

theorem controller_opening_finish_at : OpsAt openingControllerImage 13068 openingFinishOps := by
  have code := opening_controller_ops_at
  have layout : openingControllerOps=openingControllerOps.take 2243++openingFinishOps := by decide
  rw [layout] at code
  have suffix := ops_at_right openingControllerImage 4096 (openingControllerOps.take 2243) openingFinishOps code
  rw [List.length_take,opening_controller_ops_length] at suffix
  exact suffix

theorem opening_finish_pc (s : MachineState) (count : Nat) (small : count≤4) :
    (openingFinishPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [openingFinishPrefix,openingFinishOps,execInstrBr,BitVec.add_assoc]
theorem opening_finish_output (s : MachineState) : (openingFinishPrefix s 4).getReg .x6=s.getReg .x20 := by
  change s.getReg .x20+0=s.getReg .x20
  exact BitVec.add_zero _
theorem opening_finish_length (s : MachineState) :
    (openingFinishPrefix s 4).getReg .x11=s.getReg .x20-s.getReg .x17 := by
  change (s.getReg .x20+0)-s.getReg .x17=_
  exact congrArg (fun value : Word => value-s.getReg .x17) (BitVec.add_zero (s.getReg .x20))
theorem opening_finish_byte (s : MachineState) (address : Word) :
    (openingFinishPrefix s 4).getByte address=s.getByte address := rfl

theorem opening_finish_execution (s : MachineState) (pc : s.pc=13068) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (5+fuel) s coins=pure ⟨.success,openingFinishPrefix s 4,5,0⟩ := by
  have block (rest : Nat) : execute openingControllerImage (4+rest) s coins=
      (do let result ← execute openingControllerImage rest (openingFinishPrefix s 4) coins
          return result.charge 4 0) := by
    apply execute_unit_steps (states := openingFinishPrefix s)
    intro index inside
    refine ⟨.base (openingFinishOps.getD index .EBREAK),?_,?_,?_⟩
    · apply controller_opening_finish_at index (by simp only [openingFinishOps,List.length_cons,List.length_nil]; omega)
      rw [opening_finish_pc s index (by omega),pc]
    · interval_cases index <;> rfl
    · interval_cases index <;> rfl
  have fetched : fetch openingControllerImage (openingFinishPrefix s 4)=some (.base .ECALL) := by
    exact controller_opening_finish_at 4 (by decide) _ (by rw [opening_finish_pc s 4 (by decide),pc])
  have halt : (openingFinishPrefix s 4).getReg .x5=1 := rfl
  have success : (openingFinishPrefix s 4).getReg .x10=0 := rfl
  rw [show 5+fuel=4+(fuel+1) by omega,block]
  unfold execute
  rw [fetched]
  simp only [halt,success]
  rfl

end CommitGolfCandidate.Chained.Native
