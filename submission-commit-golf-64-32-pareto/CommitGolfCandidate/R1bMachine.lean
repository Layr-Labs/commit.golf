import CommitGolf.Artifact
import CommitGolfCandidate.Execution
import CommitGolfCandidate.WriteMemory
namespace CommitGolfCandidate.R1bPC
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def pcAt (n : Nat) := BitVec.ofNat 64 (4096+4*n)
theorem pc_succ (n : Nat) : pcAt (n+1) = pcAt n+4 := by
  unfold pcAt
  rw [show 4096+4*(n+1) = (4096+4*n)+4 by omega, BitVec.ofNat_add]; rfl

end CommitGolfCandidate.R1bPC
namespace CommitGolfCandidate.R1b.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open R1bPC (pcAt pc_succ)

inductive Code | opening | check deriving DecidableEq
def Code.image : Code→Image | .opening=>Artifact.submission.image .opening | .check=>Artifact.submission.image .check
def Code.count : Code→Nat | .opening=>12626 | .check=>10542
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
  have small : c.count<30000:=by cases c <;> decide
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


abbrev W (a : Nat) := BitVec.ofNat 64 a
def byte (s : MachineState) (a : Nat) := s.getByte (W a)
def proofBase := 10334769248
theorem wordNumber {a b : Nat} (ba : a<2^64) (bb : b<2^64) (e : W a=W b) : a=b := by
  have h:=congrArg BitVec.toNat e
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ba,Nat.mod_eq_of_lt bb] using h

def Safe (a n : Nat) := a+n≤MEMORY_BYTES ∧ a%n=0
theorem Safe.valid {a n : Nat} (ok : Safe a n) : accessValid (W a) n=true := by
  have sr:=ok.1;unfold MEMORY_BYTES at sr
  simp only [accessValid,rangeValid,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),ok.1,ok.2,decide_true,Bool.true_and]
def Matches (c : Code) (pc : Nat) (xs : List Instr) :=
  ∀ j (bj : j<xs.length),decodeInstruction (c.word (pc+j))=some (.base xs[j])

theorem Matches.head {c : Code} {pc : Nat} {op : Instr} {ops : List Instr} (h : Matches c pc (op::ops)) :
    decodeInstruction (c.word pc)=some (.base op):=h 0 (by simp)
theorem Matches.tail {c : Code} {pc : Nat} {op : Instr} {ops : List Instr} (h : Matches c pc (op::ops)) :
    Matches c (pc+1) ops:=by
  intro j bj;rw [show pc+1+j=pc+(j+1) by omega];exact h (j+1) (by simp;omega)
theorem Matches.left {c : Code} {pc : Nat} {a b : List Instr} (h : Matches c pc (a++b)) :
    Matches c pc a:=by
  intro j bj;have e:=h j (by rw [List.length_append];omega)
  rwa [List.getElem_append_left bj] at e
theorem Matches.right {c : Code} {pc : Nat} {a b : List Instr} (h : Matches c pc (a++b)) :
    Matches c (pc+a.length) b:=by
  intro j bj
  have e:=h (a.length+j) (by simp only [List.length_append];omega)
  simpa only [List.getElem_append_right (show a.length≤a.length+j by omega),Nat.add_sub_cancel_left,Nat.add_assoc] using e

theorem stepAdd (c : Code) (s : MachineState) (pc : Nat) (d r : Reg) (imm : BitVec 12)
    (small : pc<c.count) (atPC : s.pc=pcAt pc)
    (code : decodeInstruction (c.word pc)=some (.base (.ADDI d r imm))) :
    Runs c s (execInstrBr s (.ADDI d r imm)) 1 1 := one small atPC _ code rfl
theorem getAfterAdd (s : MachineState) (d r : Reg) (imm : BitVec 12) (nonzero : d≠.x0) :
    (execInstrBr s (.ADDI d r imm)).getReg d=s.getReg r+signExtend12 imm:=by
  simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nonzero]
theorem keepAdd (s : MachineState) (d r k : Reg) (imm : BitVec 12) (away : d≠k) :
    (execInstrBr s (.ADDI d r imm)).getReg k=s.getReg k :=
  MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ away)
theorem addPC {s : MachineState} (d r : Reg) (imm : BitVec 12) {n : Nat} (h : s.pc=pcAt n) :
    (execInstrBr s (.ADDI d r imm)).pc=pcAt (n+1):=(congrArg (·+4) h).trans (pc_succ n).symm

def stands (c : Code) (n : Nat) (op : Instr) : Bool :=
  match decodeInstruction (c.word n) with | some (.base actual)=>decide (actual=op) | _=>false
theorem stood {c : Code} {n : Nat} {op : Instr} (h : stands c n op) : decodeInstruction (c.word n)=some (.base op) := by
  unfold stands at h;split at h
  · next actual e=>rw [e,of_decide_eq_true h]
  · contradiction

def listed (c : Code) (pc : Nat) (ops : List Instr) : Bool :=
  (List.finRange ops.length).all (fun j=>stands c (pc+j.val) ops[j.val])
theorem matchesListed {c : Code} {pc : Nat} {ops : List Instr} (h : listed c pc ops) : Matches c pc ops := by
  intro i bi
  apply stood
  exact List.all_eq_true.mp h ⟨i,bi⟩ (List.mem_finRange ..)

def Wrote (s t : MachineState) (a n : Nat) (val : Nat→Byte) := ∀ q,q<2^64 →
  byte t q=if a≤q ∧ q<a+n then val (q-a) else byte s q

theorem storedFlag (s : MachineState) (a : Nat) (v : Byte) (ba : a<2^64) :
    Wrote s (s.setByte (W a) v) a 1 (fun _=>v) := by
  intro q bq;unfold byte;rw [set_byte_read]
  by_cases eqv : q=a
  · subst q;rw [if_pos rfl,if_pos (by omega)]
  · have distinct : W q≠W a:=fun e=>eqv (wordNumber bq ba e)
    rw [if_neg distinct,if_neg (by omega)]

theorem Wrote.mem {s t t' : MachineState} {a n : Nat} {v : Nat→Byte} (w : Wrote s t a n v)
    (e : t'.mem=t.mem) : Wrote s t' a n v := by
  intro q h;simpa only [byte,MachineState.getByte,MachineState.getMem,e] using w q h

theorem flagRun {c : Code} {n a : Nat} {r v : Reg} {off : BitVec 12} {s : MachineState}
    (limit : n<c.count) (pc : s.pc=pcAt n) (enc : decodeInstruction (c.word n)=some (.base (.SB r v off)))
    (addr : s.getReg r+signExtend12 off=W a) (bound : a+1≤MEMORY_BYTES) :
    let t:=execInstrBr s (.SB r v off)
    Runs c s t 1 1 ∧ t.pc=pcAt (n+1) ∧ (∀ k,t.getReg k=s.getReg k) ∧
      Wrote s t a 1 (fun _=>(s.getReg v).truncate 8) := by
  have ok : memoryArgumentsValid s (.SB r v off)=true:=by
    change accessValid _ 1=true;rw [addr];apply Safe.valid;exact ⟨bound,Nat.mod_one _⟩
  refine ⟨one limit pc _ enc (by simp only [ordinaryStep,if_pos ok]),(congrArg (·+4) pc).trans (pc_succ n).symm,
    fun k=>by cases k <;> rfl,?_⟩
  apply (storedFlag s a ((s.getReg v).truncate 8) (by unfold MEMORY_BYTES at bound;omega)).mem
  simp only [execInstrBr,addr];rfl

end CommitGolfCandidate.R1b.Machine
