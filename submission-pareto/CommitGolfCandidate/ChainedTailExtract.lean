import CommitGolfCandidate.ChainedTailRefill

/-! Checked low-field extraction and residual-buffer update. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

private theorem prefix_succ (s : MachineState) (count : Nat) (inside : count < 6) :
    tailExtractPrefix s (count+1) = execInstrBr (tailExtractPrefix s count) (tailExtractOp count) := by
  interval_cases count <;> rfl

theorem tail_extract_pc (s : MachineState) (count : Nat) (small : count ≤ 6) :
    (tailExtractPrefix s count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  induction count with
  | zero => simp [tailExtractPrefix]
  | succ count ih =>
    rw [prefix_succ s count (by omega)]
    have step : (execInstrBr (tailExtractPrefix s count) (tailExtractOp count)).pc =
        (tailExtractPrefix s count).pc+4 := by
      have inside : count < 6 := by omega
      interval_cases count <;> rfl
    rw [step,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*count)+BitVec.ofNat 64 4 = _
    rw [←BitVec.ofNat_add]
    congr 1

theorem tail_extract_execution (image : Image) (base : Word) (code : TailReadAt image base)
    (s : MachineState) (pc : s.pc = base+24) (fuel : Nat) (coins : Bool) :
    execute image (6+fuel) s coins =
      (do let result ← execute image fuel (tailExtractPrefix s 6) coins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := tailExtractPrefix s)
  intro i inside
  refine ⟨.base (tailExtractOp i),?_,?_,?_⟩
  · have op : tailReadOp (6+i) = tailExtractOp i := by interval_cases i <;> rfl
    have location : (tailExtractPrefix s i).pc = base+BitVec.ofNat 64 (4*(6+i)) := by
      rw [tail_extract_pc s i (by omega),pc,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    simpa only [op] using code ⟨6+i,by omega⟩ _ location
  · rw [prefix_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem tail_extract_value (s : MachineState) : (tailExtractPrefix s 6).getReg .x24 =
    s.getReg .x23 &&& ((1#64 <<< ((s.getReg .x26).toNat%64))-1) := by
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem tail_extract_buffer (s : MachineState) : (tailExtractPrefix s 6).getReg .x23 =
    s.getReg .x23 >>> ((s.getReg .x26).toNat%64) := rfl

theorem tail_extract_count (s : MachineState) :
    (tailExtractPrefix s 6).getReg .x25 = s.getReg .x25-s.getReg .x26 := rfl

theorem tail_extract_memory (s : MachineState) (query : Word) :
    (tailExtractPrefix s 6).getMem query = s.getMem query := rfl

theorem tail_extract_frame (s : MachineState) (reg : Reg) (buffer : reg ≠ .x23)
    (value : reg ≠ .x24) (count : reg ≠ .x25) (mask : reg ≠ .x28) :
    (tailExtractPrefix s 6).getReg reg = s.getReg reg := by
  cases reg <;> first | contradiction | rfl

end CommitGolfCandidate.Chained.Native
