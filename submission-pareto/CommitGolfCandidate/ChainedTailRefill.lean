import CommitGolfCandidate.ChainedTailReadCode

/-! Checked byte refill, including source advancement and accumulator frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count < 5) :
    tailRefillPrefix s (count+1) = execInstrBr (tailRefillPrefix s count) (tailRefillOp count) := by
  interval_cases count <;> rfl

theorem tail_refill_pc (s : MachineState) (count : Nat) (small : count ≤ 5) :
    (tailRefillPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [tailRefillPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (tailRefillPrefix s count) (tailRefillOp count)).pc =
        (tailRefillPrefix s count).pc+4 := by
      have inside : count < 5 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [←BitVec.ofNat_add]
    congr 1

theorem tail_refill_execution (image : Image) (base : Word) (code : TailReadAt image base)
    (s : MachineState) (pc : s.pc = base+4) (valid : accessValid (s.getReg .x20) 1 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (5+fuel) s coins =
      (do let result ← execute image fuel (tailRefillPrefix s 5) coins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := tailRefillPrefix s)
  intro i inside
  refine ⟨.base (tailRefillOp i),?_,?_,?_⟩
  · have op : tailReadOp (1+i) = tailRefillOp i := by interval_cases i <;> rfl
    have location : (tailRefillPrefix s i).pc = base+BitVec.ofNat 64 (4*(1+i)) := by
      rw [tail_refill_pc s i (by omega),pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    simpa only [op] using code ⟨1+i,by omega⟩ _ location
  · rw [prefix_succ s i inside]
    interval_cases i
    · simpa [ordinaryStep,memoryArgumentsValid,memAccess,tailRefillPrefix,tailRefillOp,tailRefillOps,signExtend12] using valid
    all_goals rfl
  · interval_cases i <;> rfl

theorem tail_refill_value (s : MachineState) : (tailRefillPrefix s 5).getReg .x23 =
    s.getReg .x23 ||| ((s.getByte (s.getReg .x20+0)).zeroExtend 64 <<< ((s.getReg .x25).toNat%64)) := rfl

theorem tail_refill_count (s : MachineState) :
    (tailRefillPrefix s 5).getReg .x25 = s.getReg .x25+8 := rfl

theorem tail_refill_pointer (s : MachineState) :
    (tailRefillPrefix s 5).getReg .x20 = s.getReg .x20+1 := rfl

theorem tail_refill_memory (s : MachineState) (query : Word) :
    (tailRefillPrefix s 5).getMem query = s.getMem query := rfl

theorem tail_refill_frame (s : MachineState) (reg : Reg) (pointer : reg ≠ .x20)
    (value : reg ≠ .x23) (loaded : reg ≠ .x24) (count : reg ≠ .x25) :
    (tailRefillPrefix s 5).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

end CommitGolfCandidate.Chained.Native
