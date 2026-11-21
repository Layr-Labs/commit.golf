import CommitGolfCandidate.ChainedHashExecution
import CommitGolfCandidate.ChainedCommitGeometry

/-! Native level setup, outer call edge and return to the heap-copy suffix. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def levelPC (h : Height) : Word := 184628+BitVec.ofNat 64 (4*(5+20*h.val))

theorem level_prefix_pc (s : MachineState) (h : Height) (count : Nat) (small : count ≤ 7) :
    (parentLevelPrefix s h count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp [parentLevelPrefix,parentLevelOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem level_fetch (h : Height) (i : Fin 8) (s : MachineState)
    (pc : s.pc = 184628+BitVec.ofNat 64 (4*(5+20*h.val+i.val))) :
    fetch chainedCommitImage s = some (.base (((parentLevelOps h)[i.val]?).getD .EBREAK)) := by
  have opEq : chainedParentOp (5+20*h.val+i.val) = ((parentLevelOps h)[i.val]?).getD .EBREAK := by
    fin_cases h <;> fin_cases i <;> rfl
  simpa only [opEq] using chained_parent_at ⟨5+20*h.val+i.val,by have := h.isLt; have := i.isLt; omega⟩ s pc

theorem level_setup_execution (s : MachineState) (h : Height) (pc : s.pc = levelPC h)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (8+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (parentLevelPrefix s h 8) coins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := parentLevelPrefix s h)
  intro i inside
  refine ⟨.base (((parentLevelOps h)[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply level_fetch h ⟨i,inside⟩
    rw [level_prefix_pc s h i (by omega),pc]
    unfold levelPC
    rw [BitVec.add_assoc,←BitVec.ofNat_add,
      show 4*(5+20*h.val)+4*i = 4*(5+20*h.val+i) by omega]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem LoopArgs.levelCalled {s : MachineState} (args : LoopArgs s 256) (h : Height) :
    LoopArgs (parentLevelPrefix s h 8) 256 :=
  ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
    args.inputValid,args.outputValid,args.access⟩

theorem level_called_source (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 8).getReg .x14 = s.getReg .x6 := by
  change s.getReg .x6+signExtend12 0 = _
  exact BitVec.add_zero _

theorem level_called_counter (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 8).getReg .x18 = BitVec.ofNat 64 (calls h-1) := by
  fin_cases h <;> rfl

theorem level_called_pc (s : MachineState) (h : Height) (pc : s.pc = levelPC h) :
    (parentLevelPrefix s h 8).pc = 186612 := by
  change s.pc+4+4+4+4+4+4+4+signExtend21 (BitVec.ofNat 21 (1936-80*h.val)) = _
  rw [pc]
  fin_cases h <;> decide

theorem level_called_link (s : MachineState) (h : Height) :
    (parentLevelPrefix s h 8).getReg .x19 = s.pc+32 := by
  change s.pc+4+4+4+4+4+4+4+4 = _
  simp only [BitVec.add_assoc]
  rfl

def levelHashTrace (h : Height) (s : MachineState) : OracleComp World MachineState :=
  hashTrace (calls h-1) (parentLevelPrefix s h 8)

theorem level_hash_execution (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (pc : s.pc = levelPC h)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (43+continuationInstructions (calls h-1)+fuel) s coins =
      (do let out ← levelHashTrace h s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (50+continuationCycles (calls h-1)) (calls h)) := by
  have small : calls h-1 ≤ 7 := by fin_cases h <;> decide
  have valid : ∀ k : Fin 8,
      accessValid ((parentLevelPrefix s h 8).getReg .x14+BitVec.ofNat 64 (8*k.val)) 8 = true := by
    rw [level_called_source]
    exact inputs
  have total : calls h-1+1 = calls h := by fin_cases h <;> decide
  rw [show 43+continuationInstructions (calls h-1)+fuel =
    8+(35+continuationInstructions (calls h-1)+fuel) by omega,level_setup_execution s h pc,
    hash_execution (calls h-1) small _ (args.levelCalled h) (level_called_pc s h pc)
      (level_called_counter s h) valid]
  simp [levelHashTrace,bind_assoc,Execution.charge,total,←Nat.add_assoc]

theorem level_hash_return_pc (s out : MachineState) (h : Height) (pc : s.pc = levelPC h)
    (reached : out ∈ support (levelHashTrace h s)) : out.pc = levelPC h+32 := by
  rw [hash_return_pc _ _ _ reached,level_called_link,pc]
  fin_cases h <;> decide

end CommitGolfCandidate.Chained.Native
