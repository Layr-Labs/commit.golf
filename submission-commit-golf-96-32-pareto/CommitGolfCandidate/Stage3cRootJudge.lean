import CommitGolfCandidate.Stage3cCapUpperMemory
import CommitGolfCandidate.Stage3cCheckOrdinary
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def rootMatches (H : Compression) (x : CheckInput) (q : Fin 4) :=capVal H x q 8 0=x.commitment
noncomputable instance (H x q) : Decidable (rootMatches H x q):=Classical.propDecidable _
def rootPC (_later : Bool) :=1084
def rootCompare (_later : Bool) : CompareSite:=⟨1086,2144,true,.x28,.x8,.x6,.x7⟩
private def rootOps:=liOps .x28 (nodeAt 8 0)
private theorem rootSites : ∀ b : Bool,Sym.Listed rootOps (rootPC b) ∧ (rootCompare b).valid ∧
    rootPC b+rootOps.length=(rootCompare b).start ∧ JumpSite ((rootCompare b).pc 4) 2141 .x0 :=by decide +kernel
private theorem cmpRegs (r : Reg) (h : r∈capRegs) (b : Bool) : r≠(rootCompare b).temp ∧ r≠(rootCompare b).other ∧ r≠.x28 := by
  cases b <;> cases r <;> simp_all [capRegs,rootCompare]
theorem root_judge (o : Oracle) (x : CheckInput) (s : MachineState) (b : Bool) (q : Fin 4) (pc : s.pc=pcAt (rootPC b))
    (env : CapEnv x s) (cache : Cache s (capVal o.compression x q)) :
    ∃ t n,n≤19 ∧ Flow o s t n 0 ∧ t.pc=pcAt (if rootMatches o.compression x q then 2141 else (rootCompare b).mismatch)
      ∧ t.mem=s.mem ∧ CapKeeps s t := by
  obtain ⟨listed,valid,end_,leap⟩:=rootSites b
  obtain ⟨run,regs,mem,ip⟩:=Sym.compiled o rootOps (rootPC b) s pc listed (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  let u:=Sym.evaluated rootOps s
  have lhs : u.getReg (rootCompare b).lhs=W (nodeAt 8 0):=by cases b <;> exact regs .x28
  have rhs : u.getReg (rootCompare b).rhs=W rootBase:=by cases b <;> exact (regs .x8).trans env.root
  have saved (r : Reg) (h : r≠.x28) : u.getReg r=s.getReg r:=by apply (regs r).trans;cases r <;> first | contradiction | rfl
  obtain ⟨v,k,lim,comp,vp,vm,keep⟩:=compare_digest o u (rootCompare b) valid (nodeAt 8 0) rootBase (ip.trans (congrArg pcAt end_)) lhs rhs
    ⟨by decide,by decide⟩ ⟨by decide,by decide⟩
  have eq : (readBuffer u (nodeAt 8 0) 32=readBuffer u rootBase 32) ↔ rootMatches o.compression x q:=by
    rw [(read_buffer_memory_congr u s mem _ _).trans (cache.node 8 (by decide) 0 (by decide)),
      (read_buffer_memory_congr u s mem _ _).trans env.read];rfl
  have kv : CapKeeps s v:=fun r h=>(keep r (cmpRegs r h b).1 (cmpRegs r h b).2.1).trans (saved r (cmpRegs r h b).2.2)
  by_cases ok : rootMatches o.compression x q
  · rw [if_pos (eq.mpr ok)] at vp
    have last:=jump o v _ _ .x0 leap vp
    exact ⟨_,2+k+1,by omega,(run.trans comp).trans last,by rw [if_pos ok];rfl,vm.trans mem,fun r h=>MachineState.getReg_setPC.trans (kv r h)⟩
  · rw [if_neg (fun h=>ok (eq.mp h))] at vp
    exact ⟨v,2+k,by omega,run.trans comp,by rw [if_neg ok];exact vp,vm.trans mem,kv⟩

end CommitGolfCandidate.Chained.BinaryMachine.Check
