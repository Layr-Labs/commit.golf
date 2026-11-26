import CommitGolfCandidate.S4Evaluation
import CommitGolfCandidate.LateCalls
import CommitGolfCandidate.WriteMemory

namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (pcAt submission)

inductive Code | opening | check deriving DecidableEq
def Code.image : Code→Image | .opening=>Late.submission.image .opening | .check=>Late.submission.image .check
def Code.count : Code→Nat | .opening=>5876 | .check=>4858
def Code.payload : (c : Code) → ArtifactEncoding.Packed c.count
  | .opening=>Artifact.openingCode
  | .check=>Artifact.checkCode

def Code.word (c : Code) (n : Nat) : BitVec 32 :=
  if h : n<c.count then c.payload.get 32 ⟨n,h⟩ else 0

private theorem packedLookup {m : Nat} (a : ArtifactEncoding.Packed m) (n : Nat) (h : n<m) :
    (ArtifactEncoding.decode 32 a)[n]?=some (a.get 32 ⟨n,h⟩) := by
  simp only [ArtifactEncoding.decode,List.getElem?_ofFn,dif_pos h]
attribute [local irreducible] ArtifactEncoding.decode

theorem fetched (c : Code) (n : Nat) (hi : n<c.count) (s : MachineState) (pc : s.pc=pcAt n) :
    fetch c.image s=decodeInstruction (c.word n) := by
  have atWord : c.image.code[n]?=some (c.word n) := by
    rw [Code.word,dif_pos hi]
    cases c with
    | opening=>exact packedLookup Artifact.openingCode n hi
    | check=>exact packedLookup Artifact.checkCode n hi
  have small : c.count<10000:=by cases c <;> decide
  simp only [fetch,pc,pcAt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4096+4*n<2^64 by omega)]
  rw [if_pos (by constructor <;> omega)]
  simp only [Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by decide : 0<4),atWord]

def Runs (c : Code) (s t : MachineState) (steps cycles : Nat) := ∀ fuel coins,
  execute c.image (fuel+steps) s coins=(do let r←execute c.image fuel t coins;pure (r.charge cycles 0))

theorem Runs.refl (c : Code) (s : MachineState) : Runs c s s 0 0 := by
  intro fuel coins;simp [Execution.charge]

theorem Runs.trans {c : Code} {s t u : MachineState} {a b m n : Nat}
    (x : Runs c s t a m) (y : Runs c t u b n) : Runs c s u (a+b) (m+n) := by
  intro fuel coins
  rw [show fuel+(a+b)=fuel+b+a by omega,x,y];simp [bind_assoc,Execution.charge,Nat.add_assoc]

theorem one {c : Code} {n : Nat} (hi : n<c.count) {s t : MachineState} (pc : s.pc=pcAt n)
    (op : Instr) (code : decodeInstruction (c.word n)=some (.base op)) (step : ordinaryStep s (.base op)=some t) :
    Runs c s t 1 (instructionCycles (.base op)) :=
  fun fuel coins=>execute_ordinary_step _ _ _ _ fuel coins ((fetched c n hi s pc).trans code) step

def obs (o : Oracle) (n : Nat) (s : MachineState) : Exit×Nat :=
  let e:=checkEvaluation o (execute Code.check.image n s false)
  (e.1.exit,e.2)

def CheckRuns (o : Oracle) (s t : MachineState) (steps calls : Nat) :=
  ∀ fuel,obs o (steps+fuel) s=((obs o fuel t).1,calls+(obs o fuel t).2)

theorem CheckRuns.trans {o : Oracle} {s t u : MachineState} {a b m n : Nat}
    (x : CheckRuns o s t a m) (y : CheckRuns o t u b n) : CheckRuns o s u (a+b) (m+n) := by
  intro fuel;rw [Nat.add_assoc,x,y];simp [Nat.add_assoc]

theorem ofRuns {s t : MachineState} {n m : Nat} (o : Oracle) (x : Runs .check s t n m) :
    CheckRuns o s t n 0 := by
  intro fuel
  simp only [obs,Nat.add_comm n fuel,x fuel false,bind_pure_comp,check_evaluation_map,Nat.zero_add]
  rfl

theorem stop {c : Code} {s : MachineState} {n : Nat} (hn : n<c.count) (pc : s.pc=pcAt n)
    (op : decodeInstruction (c.word n)=some (.base .ECALL)) (mode : s.getReg .x5=1)
    (fuel : Nat) (coins : Bool) :
    execute c.image (fuel+1) s coins=pure ⟨if s.getReg .x10=0 then .success else .failure,s,1,0⟩ := by
  rw [execute,(fetched c n hn s pc).trans op,mode]
  rfl
end CommitGolfCandidate.S4.Machine
