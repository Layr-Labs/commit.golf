import CommitGolfCandidate.ReconstructedHonestRegionBlocks

namespace CommitGolfCandidate.Reconstruction.HonestForward
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestRegionStep HonestMemoryRanges

def access (span : Range) (n : Nat) := span.hi+n≤MEMORY_BYTES &&
  (n==1 || (span.lo==span.hi && span.lo%n==0))

private theorem access_ok {span : Range} {x : Word} {n : Nat} (bound : Contains span x) (checked : access span n=true) :
    accessValid x n=true := by
  simp only [access,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at checked
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
  obtain ⟨lo,hi⟩ := bound
  refine ⟨by omega,?_⟩
  rcases checked.2 with rfl|⟨eq,multiple⟩
  · exact Nat.mod_one _
  · rwa [show x.toNat=span.lo by omega]

def validBase (a : Abstract) : Instr→Bool
  | .ECALL | .EBREAK | .CSRS .. | .LI .. | .MV .. | .NOP => false
  | .LD _ b n | .SD b _ n => access (addressRange (a.regs b) n) 8
  | .LW _ b n | .LWU _ b n | .SW b _ n => access (addressRange (a.regs b) n) 4
  | .LH _ b n | .LHU _ b n | .SH b _ n => access (addressRange (a.regs b) n) 2
  | .LB _ b n | .LBU _ b n | .SB b _ n => access (addressRange (a.regs b) n) 1
  | _ => true

def validOp (a : Abstract) : Instruction→Bool
  | .base op => validBase a op
  | _ => true

theorem steps {a : Abstract} {s : MachineState} (meaning : Models s a) (op : Instruction)
    (valid : validOp a op=true) : ∃ t, ordinaryStep s op=some t := by
  cases op with
  | base op =>
    refine ⟨execInstrBr s op,?_⟩
    cases op <;> try cases valid
    all_goals simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true]
    all_goals try (apply ite_eq_left; exact access_ok (address_ok (meaning.1 _) _) valid)
  | word _ _ _ _ | sraiw _ _ _ => exact ⟨_,rfl⟩

def check {n : Nat} (packed : ArtifactEncoding.Packed n) (cut : Word→Bool) (clock : Nat) (pc : Word) (a : Abstract) :
    Bool := match clock with
  | 0 => false
  | k+1 => match HonestBlocks.readOp packed pc with
    | none => false
    | some op => validOp a op && HonestFlow.direct op &&
      (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun q => cut q || check packed cut k q (advance a op))

def Forward (im : Image) (coins : Bool) (cut : Word→Bool) (clock : Nat) (s : MachineState) :=
  ∃ time fee t, time≤clock ∧ HonestCuts.Reaches im coins cut s t ∧ ∀ fuel,
    execute im (time+fuel) s coins = (do let r ← execute im fuel t coins; return r.charge fee 0)

theorem sound {n : Nat} (packed : ArtifactEncoding.Packed n) (im : Image) (image : im.code=ArtifactEncoding.decode 32 packed)
    (bound : 4096+4*n<2^64) (cut : Word→Bool) (clock : Nat) (pc : Word) (a : Abstract)
    (holds : check packed cut clock pc a=true) (s : MachineState) (coins : Bool)
    (loc : s.pc=pc) (meaning : Models s a) : Forward im coins cut clock s := by
  induction clock generalizing pc a s with
  | zero => cases holds
  | succ k ih =>
    cases opAt : HonestBlocks.readOp packed pc with
    | none => simp [check,opAt] at holds
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at holds
      obtain ⟨⟨valid,direct⟩,edges⟩ := holds
      obtain ⟨u,step⟩ := steps meaning op valid
      have read := HonestBlocks.fetch_op packed im image bound s op (loc ▸ opAt)
      have exactStep := execute_ordinary_step im op s u 0 coins read step
      let out : Execution := ⟨.unfinished,u,instructionCycles op,0⟩
      have reach : out∈support (execute im 1 s coins) := by
        rw [exactStep]; simp [execute,out,Execution.charge]
      have pub : op=.base .ECALL → s.getReg .x5=0 := by rintro rfl; cases valid
      obtain ⟨target,next⟩ := one im s coins a _ meaning read direct pub out reach rfl
      rw [loc] at target
      have edge := List.all_eq_true.mp edges _ target
      cases stop : cut u.pc with
      | true =>
        exact ⟨1,_,u,by omega,.hit reach rfl stop,fun f => by rw [Nat.add_comm]; exact execute_ordinary_step im op s u f coins read step⟩
      | false =>
        change (cut u.pc || check packed cut k u.pc (advance a op))=true at edge
        simp only [stop,Bool.false_or] at edge
        obtain ⟨time,fee,t,le,path,tail⟩ := ih _ _ edge u rfl next
        refine ⟨time+1,instructionCycles op+fee,t,by omega,.more reach rfl stop path,?_⟩
        intro f
        rw [show time+1+f=(time+f)+1 by omega,execute_ordinary_step im op s u (time+f) coins read step,tail]
        simp [Execution.charge,Nat.add_assoc]

end CommitGolfCandidate.Reconstruction.HonestForward
