import CommitGolfCandidate.ChainedHeapCopy

/-! Separate one-time level setup from the three-instruction repeated call prefix. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def bodyPC (h : Height) : Word := 184628+BitVec.ofNat 64 (4*(10+20*h.val))
def bodyOps (h : Height) : List Instr := (parentLevelOps h).drop 5 |>.take 3
def bodyPrefix (s : MachineState) (h : Height) (count : Nat) : MachineState :=
  ((bodyOps h).take count).foldl execInstrBr s

theorem body_pc_eq (h : Height) : bodyPC h = levelPC h+20 := by fin_cases h <;> rfl

theorem level_header_execution (s : MachineState) (h : Height) (pc : s.pc = levelPC h)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (5+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (parentLevelPrefix s h 5) coins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := parentLevelPrefix s h)
  intro i inside
  refine ⟨.base (((parentLevelOps h)[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply level_fetch h ⟨i,by omega⟩
    rw [level_prefix_pc s h i (by omega),pc]
    unfold levelPC
    rw [BitVec.add_assoc,←BitVec.ofNat_add,
      show 4*(5+20*h.val)+4*i = 4*(5+20*h.val+i) by omega]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem level_header_pc (s : MachineState) (h : Height) (pc : s.pc = levelPC h) :
    (parentLevelPrefix s h 5).pc = bodyPC h := by
  rw [level_prefix_pc s h 5 (by decide),pc,body_pc_eq]
  rfl

theorem body_prefix_pc (s : MachineState) (h : Height) (count : Nat) (small : count ≤ 2) :
    (bodyPrefix s h count).pc = s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp [bodyPrefix,bodyOps,parentLevelOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem body_setup_execution (s : MachineState) (h : Height) (pc : s.pc = bodyPC h)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (3+fuel) s coins =
      (do let result ← execute chainedCommitImage fuel (bodyPrefix s h 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := bodyPrefix s h)
  intro i inside
  refine ⟨.base (((bodyOps h)[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pcHere : (bodyPrefix s h i).pc = 184628+BitVec.ofNat 64 (4*(5+20*h.val+(5+i))) := by
      rw [body_prefix_pc s h i (by omega),pc]
      unfold bodyPC
      rw [BitVec.add_assoc,←BitVec.ofNat_add,
        show 4*(10+20*h.val)+4*i = 4*(5+20*h.val+(5+i)) by omega]
    have fetched := level_fetch h ⟨5+i,by omega⟩ (bodyPrefix s h i) pcHere
    have opEq : ((parentLevelOps h)[5+i]?).getD .EBREAK = ((bodyOps h)[i]?).getD .EBREAK := by
      interval_cases i <;> rfl
    simpa only [opEq] using fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem LoopArgs.bodyCalled {s : MachineState} (args : LoopArgs s 256) (h : Height) :
    LoopArgs (bodyPrefix s h 3) 256 :=
  ⟨args.source,args.target,args.selector,args.size,args.kind,args.aligned,
    args.inputValid,args.outputValid,args.access⟩

theorem body_called_source (s : MachineState) (h : Height) :
    (bodyPrefix s h 3).getReg .x14 = s.getReg .x6 := by
  change s.getReg .x6+signExtend12 0 = _
  exact BitVec.add_zero _

theorem body_called_counter (s : MachineState) (h : Height) :
    (bodyPrefix s h 3).getReg .x18 = BitVec.ofNat 64 (calls h-1) := by
  fin_cases h <;> rfl

theorem body_called_pc (s : MachineState) (h : Height) (pc : s.pc = bodyPC h) :
    (bodyPrefix s h 3).pc = 186612 := by
  change s.pc+4+4+signExtend21 (BitVec.ofNat 21 (1936-80*h.val)) = _
  rw [pc]
  fin_cases h <;> decide

theorem body_called_link (s : MachineState) (h : Height) :
    (bodyPrefix s h 3).getReg .x19 = s.pc+12 := by
  change s.pc+4+4+4 = _
  simp only [BitVec.add_assoc]
  rfl

theorem body_register (s : MachineState) (h : Height) (reg : Reg)
    (kept : reg ∉ ([.x14,.x18,.x19] : List Reg)) :
    (bodyPrefix s h 3).getReg reg = s.getReg reg := by
  cases reg <;> first | exact (kept (by decide)).elim | rfl

theorem body_memory (s : MachineState) (h : Height) (query : Word) :
    (bodyPrefix s h 3).getMem query = s.getMem query := by rfl

def bodyHashTrace (h : Height) (s : MachineState) : OracleComp World MachineState :=
  hashTrace (calls h-1) (bodyPrefix s h 3)

theorem body_hash_execution (s : MachineState) (h : Height) (args : LoopArgs s 256)
    (pc : s.pc = bodyPC h)
    (inputs : ∀ k : Fin 8, accessValid (s.getReg .x6+BitVec.ofNat 64 (8*k.val)) 8 = true)
    (fuel : Nat) (coins : Bool) :
    execute chainedCommitImage (38+continuationInstructions (calls h-1)+fuel) s coins =
      (do let out ← bodyHashTrace h s
          let result ← execute chainedCommitImage fuel out coins
          return result.charge (45+continuationCycles (calls h-1)) (calls h)) := by
  have small : calls h-1 ≤ 7 := by have := calls_bound h; omega
  have valid : ∀ k : Fin 8,
      accessValid ((bodyPrefix s h 3).getReg .x14+BitVec.ofNat 64 (8*k.val)) 8 = true := by
    rw [body_called_source]
    exact inputs
  have total : calls h-1+1 = calls h := by have := calls_positive h; omega
  rw [show 38+continuationInstructions (calls h-1)+fuel =
    3+(35+continuationInstructions (calls h-1)+fuel) by omega,body_setup_execution s h pc,
    hash_execution (calls h-1) small _ (args.bodyCalled h) (body_called_pc s h pc)
      (body_called_counter s h) valid]
  simp [bodyHashTrace,Execution.charge,total,←Nat.add_assoc]

theorem body_hash_return_pc (s out : MachineState) (h : Height) (pc : s.pc = bodyPC h)
    (reached : out ∈ support (bodyHashTrace h s)) : out.pc = copyPC h := by
  rw [hash_return_pc _ _ _ reached,body_called_link,pc]
  fin_cases h <;> decide

theorem body_hash_register (s out : MachineState) (h : Height)
    (reached : out ∈ support (bodyHashTrace h s)) (reg : Reg)
    (kept : reg ∉ ([.x1,.x14,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)) :
    out.getReg reg = s.getReg reg := by
  rw [hash_trace_register _ _ _ reached reg (by simp_all),body_register s h reg (by simp_all)]

end CommitGolfCandidate.Chained.Native
