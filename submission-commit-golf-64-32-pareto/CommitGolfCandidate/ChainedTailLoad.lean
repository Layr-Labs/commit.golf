import CommitGolfCandidate.ChainedTailTraverseCode

/-! Load one field row without altering the output or the traversal counter. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count < 3) :
    tailLoadPrefix s (count+1) = execInstrBr (tailLoadPrefix s count) (tailLoadOp count) := by
  interval_cases count <;> rfl

theorem tail_load_pc (s : MachineState) (count : Nat) (small : count ≤ 3) :
    (tailLoadPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [tailLoadPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (tailLoadPrefix s count) (tailLoadOp count)).pc =
        (tailLoadPrefix s count).pc+4 := by
      have inside : count < 3 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [←BitVec.ofNat_add]
    congr 1

theorem tail_load_execution (image : Image) (base : Word) (code : TailTraverseAt image base)
    (s : MachineState) (pc : s.pc = base+4)
    (value : accessValid (s.getReg .x21) 1 = true)
    (width : accessValid (s.getReg .x21+1) 1 = true) (fuel : Nat) (coins : Bool) :
    execute image (3+fuel) s coins =
      (do let result ← execute image fuel (tailLoadPrefix s 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := tailLoadPrefix s)
  intro i inside
  refine ⟨.base (tailLoadOp i),?_,?_,?_⟩
  · have op : tailTraverseOp (1+i) = tailLoadOp i := by interval_cases i <;> rfl
    have location : (tailLoadPrefix s i).pc = base+BitVec.ofNat 64 (4*(1+i)) := by
      rw [tail_load_pc s i (by omega),pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    simpa only [op] using code ⟨1+i,by omega⟩ _ location
  · rw [prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,tailLoadPrefix,tailLoadOp,tailLoadOps,signExtend12] using value
    · have access : memoryArgumentsValid (tailLoadPrefix s 1) (.LBU .x26 .x21 1) = true := by
        change accessValid (s.getReg .x21+1) 1 = true
        exact width
      change ordinaryStep (tailLoadPrefix s 1) (.base (.LBU .x26 .x21 1)) = _
      simp only [ordinaryStep,access,↓reduceIte]
      rfl
    · rfl
  · interval_cases i <;> rfl

theorem tail_load_value (s : MachineState) :
    (tailLoadPrefix s 3).getReg .x24 = (s.getByte (s.getReg .x21+0)).zeroExtend 64 := rfl

theorem tail_load_width (s : MachineState) :
    (tailLoadPrefix s 3).getReg .x26 = (s.getByte (s.getReg .x21+1)).zeroExtend 64 := rfl

theorem tail_load_pointer (s : MachineState) : (tailLoadPrefix s 3).getReg .x21 = s.getReg .x21+2 := rfl

theorem tail_load_memory (s : MachineState) (query : Word) : (tailLoadPrefix s 3).getMem query = s.getMem query := rfl

theorem tail_load_frame (s : MachineState) (reg : Reg) (pointer : reg ≠ .x21)
    (value : reg ≠ .x24) (width : reg ≠ .x26) : (tailLoadPrefix s 3).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

end CommitGolfCandidate.Chained.Native
