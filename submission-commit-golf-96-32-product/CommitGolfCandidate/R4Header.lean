import CommitGolfCandidate.R4ParentLane
import CommitGolfCandidate.R4Known
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt rowAddress nodeAddress)
def header (d : Width) :=
  (List.range (bodyPC d-stagePC d)).map fun j=>match getOp (stagePC d+j) with | some (.base i)=>i | _=>Instr.EBREAK
def seed (d : Width) : Late.KnownRegs
  | .x0 | .x5 | .x13=>some 0
  | .x11=>some 96
  | .x26=>some 4294971392
  | .x28=>if d.val=0 then none else some 16383
  | _=>none
def EnterFacts (d : Width) : Prop :=
  let ops:=header d
  let r:=ops.foldl Late.knownStep (seed d)
  (ops.all Late.setupOp=true) ∧ listed (stagePC d) ops ∧ stagePC d+ops.length=bodyPC d ∧
    r .x10=some (Z (rowAddress d 0)) ∧ r .x12=some (Z (nodeAddress (d.val+1) 0)) ∧
    r .x5=some 0 ∧ r .x13=some 0 ∧ r .x11=some 96 ∧ r .x26=some 4294971392 ∧
    r .x28=some 16383 ∧ (0<bulkCount d → r .x19=some (Z (rowAddress d (bulkCount d))))
instance (d : Width) : Decidable (EnterFacts d) := inferInstanceAs (Decidable (_ ∧ _))
set_option maxRecDepth 10000 in
private theorem facts : ∀ d : Width,EnterFacts d:=by decide +kernel
theorem plusPC (p k : Nat) : pcAt p+Z (4*k)=pcAt (p+k) := by unfold pcAt;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega
theorem enter (o : Oracle) (d : Width) (s : MachineState) (pc : s.pc=pcAt (stagePC d)) (env : Env s)
    (mask : d.val≠0 → s.getReg .x28=16383) :
    ∃ t,MRun o s (header d).length t (header d).length 0 ∧ t.mem=s.mem ∧ t.pc=pcAt (bodyPC d) ∧
      Pointers d 0 t ∧ (0<bulkCount d → t.getReg .x19=Z (rowAddress d (bulkCount d))) := by
  obtain ⟨safe,code,last,a,b,c,k,w,rt,m,lim⟩:=facts d
  let ops:=header d
  let t:=ops.foldl execInstrBr s
  have all (x : Instr) (hx : x∈ops) : Late.setupOp x:=List.all_eq_true.mp safe x hx
  have seeds : Late.Agrees (seed d) s:=by
    intro r v e
    cases r <;> simp only [seed,Option.some.injEq,reduceCtorEq] at e
    case x28 => split at e <;> simp_all
    all_goals subst v;first | rfl | exact env.mode | exact env.kind | exact env.width | exact env.root
  have known:=Late.known_header ops (seed d) s all seeds
  have props:=Late.header_properties ops s all
  refine ⟨t,?_,props.1,props.2.trans ?_,⟨⟨known _ _ c,known _ _ k,known _ _ w,known _ _ rt⟩,
    known _ _ a,known _ _ b,known _ _ m⟩,fun h=>known _ _ (lim h)⟩
  · apply exec_alu_list
    intro i hi
    have pre:=Late.header_properties (ops.take i) s (fun x hx=>all x (List.mem_of_mem_take hx))
    have ip := pre.2
    rw [pc,List.length_take_of_le (Nat.le_of_lt hi),plusPC] at ip
    refine ⟨listHere code i hi _ ip,?_⟩
    have valid:=all ops[i] (List.getElem_mem hi)
    generalize e : ops[i]=ins at valid ⊢
    cases ins <;> simp [Late.setupOp] at valid <;> exact ⟨rfl,rfl⟩
  · rw [pc,plusPC,last]
end CommitGolfCandidate.R4
