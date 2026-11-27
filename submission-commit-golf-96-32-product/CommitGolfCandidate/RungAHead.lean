import CommitGolfCandidate.RungAKnown
import CommitGolfCandidate.R4Header
namespace CommitGolfCandidate.RungA.Setup
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4
open Late (pcAt)
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
def opsAt (n k : Nat) := (List.range k).map fun j=>match getOp (n+j) with | some (.base i)=>i | _=>.EBREAK
theorem runSetup (n : Nat) (ops : List Instr) (o : Oracle) (s : MachineState) (pc : s.pc=pcAt n)
    (valid : ops.all setupOp) (encoding : listed n ops) :
    let t:=ops.foldl execInstrBr s
    MRun o s ops.length t ops.length 0 ∧ t.mem=s.mem ∧ t.pc=pcAt (n+ops.length) := by
  have good : ∀ i∈ops,setupOp i:=List.all_eq_true.mp valid
  have prop:=header_properties ops s good
  refine ⟨?_,prop.1,prop.2.trans (by rw [pc,plusPC])⟩
  apply exec_alu_list
  intro i hi
  have part:=header_properties (ops.take i) s (fun x hx=>good _ (List.mem_of_mem_take hx))
  have next:=part.2
  rw [pc,List.length_take_of_le (Nat.le_of_lt hi),plusPC] at next
  refine ⟨listHere encoding i hi _ next,?_⟩
  have val:=good ops[i] (List.getElem_mem hi)
  generalize e : ops[i]=ins at val ⊢
  cases ins <;> simp [setupOp] at val <;> exact ⟨rfl,rfl⟩

def envRegs : KnownRegs
  | .x0 | .x5 | .x13=>some 0
  | .x11=>some 96
  | .x26=>some 4294971392
  | _=>none
theorem envOk {s} (e : Env s) : Agrees envRegs s := by
  intro q v h;cases q <;> simp only [envRegs,Option.some.injEq,reduceCtorEq] at h
  all_goals subst v;first | rfl | exact e.mode | exact e.kind | exact e.width | exact e.root

def headOps := opsAt 131123 17
def headRegs := headOps.foldl knownStep envRegs
private theorem facts : headOps.all setupOp=true ∧ listed 131123 headOps=true ∧ headOps.length=17 ∧
    headRegs .x21=some 5905586080 ∧ headRegs .x22=some 5301604576 ∧ headRegs .x25=some 2208 ∧
    headRegs .x20=some (Z (Late.nodeAddress 4 699048)) ∧ headRegs .x5=some 0 ∧ headRegs .x13=some 0 ∧
    headRegs .x11=some 96 ∧ headRegs .x26=some 4294971392 := by decide +kernel

theorem header (o : Oracle) (s : MachineState) (pc : s.pc=pcAt 131123) (e : Env s) :
    ∃ t,MRun o s 17 t 17 0 ∧ t.pc=pcAt 131140 ∧ t.mem=s.mem ∧ Env t ∧
    t.getReg .x21=5905586080 ∧ t.getReg .x22=5301604576 ∧ t.getReg .x25=2208 ∧ t.getReg .x20=Z (Late.nodeAddress 4 699048) := by
  obtain ⟨val,enc,len,src,dst,stride,stop,mode,kind,width,root⟩:=facts
  obtain ⟨go,mem,ip⟩:=runSetup _ headOps o s pc val enc
  have reg:=known_header headOps envRegs s (List.all_eq_true.mp val) (envOk e)
  rw [len] at go ip
  exact ⟨_,go,ip,mem,⟨reg _ _ mode,reg _ _ kind,reg _ _ width,reg _ _ root⟩,reg _ _ src,reg _ _ dst,reg _ _ stride,reg _ _ stop⟩

def finishOps := opsAt 132378 2
private theorem endSites : finishOps.all setupOp=true ∧ listed 132378 finishOps=true ∧ finishOps.length=2 ∧
  (finishOps.foldl knownStep envRegs) .x28=some 16383 ∧
  (∀ q : Reg,q∈([.x5,.x11,.x13,.x26] : List Reg) → (finishOps.foldl knownStep envRegs) q=envRegs q) ∧
  hasOp 132380 (.JAL .x0 (BitVec.ofInt 21 (4*(238455-132380 : Int))))=true :=by decide +kernel

theorem finish (o : Oracle) (s : MachineState) (pc : s.pc=pcAt 132378) (e : Env s) :
    ∃ t,MRun o s 3 t 3 0 ∧ t.pc=pcAt 238455 ∧ t.mem=s.mem ∧ Env t ∧ t.getReg .x28=16383 := by
  obtain ⟨v,enc,len,mask,fields,jump⟩:=endSites
  let u:=finishOps.foldl execInstrBr s
  obtain ⟨run,mem,ip⟩:=runSetup _ finishOps o s pc v enc
  rw [len] at run ip
  have r:=known_header finishOps envRegs s (List.all_eq_true.mp v) (envOk e)
  let t:=u.setPC (pcAt 238455)
  have go : MRun o u 1 t 1 0:=by
    apply DetRun.step1 (hasOp_sound jump u ip)
    change some (u.setPC (u.pc+_))=some t
    rw [show u.pc=pcAt 132380 from ip];rfl
  have endMask : u.getReg .x28=16383:=r .x28 16383 mask
  have eu : Env u := by
    constructor
    · exact r .x5 0 (fields .x5 (by decide))
    · exact r .x13 0 (fields .x13 (by decide))
    · exact r .x11 96 (fields .x11 (by decide))
    · exact r .x26 4294971392 (fields .x26 (by decide))
  exact ⟨t,run.trans go,rfl,mem,⟨eu.mode,eu.kind,eu.width,eu.root⟩,endMask⟩
end CommitGolfCandidate.RungA.Setup
