import CommitGolfCandidate.PairLayer
import CommitGolfCandidate.PairBranches
import CommitGolfCandidate.PairAccess
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 200000

def pairRegs := [Reg.x19,.x22,.x23,.x24,.x26,.x27]
def Carries (s t : MachineState) := ∀ r∈pairRegs,t.getReg r=s.getReg r
theorem carriesRefl (s : MachineState) : Carries s s := fun _ _ => rfl
theorem carriesTrans {a b c : MachineState} (h : Carries a b) (g : Carries b c) : Carries a c :=
  fun r hr => (g r hr).trans (h r hr)
theorem carriesPC (s : MachineState) (pc : Word) : Carries s (s.setPC pc) := fun _ _ => rfl

def AreaQuiet (s t : MachineState) (p : Nat) :=
  ∀ a, a<2^64 → Separate a 1 (sourceRow p) 64 → Separate a 1 (outSlot p) 32 → byteAt t a=byteAt s a

structure PairEffect (H : Compression) (input : CheckInput) (p : Nat) (s t : MachineState) : Prop where
  pc : t.pc=5468
  keep : Carries s t
  result : digestAt t (outSlot p)=parentAt H input p
  quiet : AreaQuiet s t p

theorem areaDigest {s t : MachineState} {p a : Nat} (h : AreaQuiet s t p)
    (bound : a+32≤2^64) (ch : Separate a 32 (sourceRow p) 64) (dst : Separate a 32 (outSlot p) 32) :
    digestAt t a=digestAt s a := by
  unfold digestAt readBuffer
  apply congrArg _;apply Finset.sum_congr rfl;intro j hj
  have bj:=Finset.mem_range.mp hj
  have e:=h (a+j) (by omega) (by unfold Separate at ch ⊢;omega) (by unfold Separate at dst ⊢;omega)
  unfold byteAt at e;rw [e]

def pairLatch (s : MachineState) := execInstrBr (pairNextState s) (.BNE .x27 .x0 8020)
theorem latchRuns (o : Oracle) (s : MachineState) (pc : s.pc=5468) : Runs o s (pairLatch s) 6 0 := by
  apply pureBlockRuns (cyc:=6)
  intro fuel
  have nextPC : (pairNextState s).pc=5488 := by simp [pairNextState,pairNextOps,execInstrBr,MachineState.setPC,pc]
  rw [show 6+fuel=5+(fuel+1) by omega,pairNextRun _ pc,edge348 _ nextPC]
  simp [pairLatch,Execution.charge,← Nat.add_assoc]

theorem latchMemory (s : MachineState) : (pairLatch s).mem=s.mem := by
  unfold pairLatch;dsimp only [execInstrBr];split <;> rfl

theorem ptrAdd (base stride n : Nat) :
    BitVec.ofNat 64 (base+stride*n)+BitVec.ofNat 64 stride=BitVec.ofNat 64 (base+stride*(n+1)) := by
  rw [← BitVec.ofNat_add]; congr 1;ring

theorem latchControl (s : MachineState) (pc : s.pc=5468) (k : Nat) (small : k<128)
    (rem : s.getReg .x27=BitVec.ofNat 64 (128-k)) :
    (pairLatch s).pc=(if k+1=128 then 5492 else 5316) ∧
    (pairLatch s).regs=(pairNextState s).regs ∧ (pairNextState s).getReg .x27=BitVec.ofNat 64 (128-(k+1)) := by
  have cc : (pairNextState s).getReg .x27=s.getReg .x27+signExtend12 4095 := rfl
  rw [rem,show 128-k=(128-(k+1))+1 by omega,BitVec.ofNat_add,BitVec.add_assoc,
    show BitVec.ofNat 64 1+signExtend12 4095=0#64 by decide,BitVec.add_zero] at cc
  have zero : (BitVec.ofNat 64 (128-(k+1))=0#64) ↔ k+1=128 := by
    constructor
    · intro e;have eqn:=congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at eqn
      change _=0 at eqn;omega
    · rintro eqn;rw [eqn] <;> decide
  have np : (pairNextState s).pc=5488 := by simp [pairNextState,pairNextOps,execInstrBr,MachineState.setPC,pc]
  refine ⟨?_,?_,cc⟩
  · simp only [pairLatch,execInstrBr,beq_iff_eq,cc,show (pairNextState s).getReg .x0=0#64 from rfl,zero,np]
    split <;> simp_all [MachineState.setPC,signExtend13]
  · dsimp only [pairLatch,execInstrBr];split <;> rfl

end CommitGolfCandidate.PairCap.Batch
