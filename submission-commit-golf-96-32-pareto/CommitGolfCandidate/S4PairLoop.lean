import CommitGolfCandidate.S4PairBody
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

theorem pairStep (o : Oracle) (x : CheckInput) (s : MachineState) (j : Nat) (bj : j<171)
    (start : PairCursor o.compression x s j) : ∃ t n q,n≤106 ∧ q≤1 ∧ CheckRuns o s t n q ∧ PairCursor o.compression x t (j+1) := by
  obtain ⟨u,n,q,bn,bq,f⟩:=pairBody o x j bj s start
  let v:=Sym.evaluated pairAdv u
  obtain ⟨incs,regs,mem,endPC⟩:=evalMath .check pairAdv 4504 4508 u f.pc pairSites.advance
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : pairAdv.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ he=>by cases he)
  have ptr : v.getReg .x1=W (flagAddr (2*(j+1))):=by
    apply (regs .x1).trans;change u.getReg .x1+W 2=_;rw [f.flags]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold flagAddr;omega))
  have children : v.getReg .x29=W (capAddr (2*(j+1))):=by
    apply (regs .x29).trans;change u.getReg .x29+W 64=_;rw [f.children]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold capAddr;omega))
  have dest : v.getReg .x30=W (upperAddr (j+1)):=by
    apply (regs .x30).trans;change u.getReg .x30+W 32=_;rw [f.dest]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold upperAddr;omega))
  have count : v.getReg .x19=W (171-(j+1)):=by
    apply (regs .x19).trans;change u.getReg .x19+18446744073709551615=_;rw [f.remaining]
    exact (prev _ (by omega)).trans (congrArg W (by omega))
  have guard:=alternate .check 4508 4510 4393 .x19 .x0 true pairSites.finish pairSites.more rfl v endPC
  have eqv : ((v.getReg .x19==v.getReg .x0)==true)=decide (171≤j+1):=by
    change ((v.getReg .x19==W 0)==true)=_;rw [count,eqNatural _ _ (by omega) (by decide)]
    by_cases e:171≤j+1
    · rw [decide_eq_true e,decide_eq_true (by omega : 171-(j+1)=0)];rfl
    · rw [decide_eq_false e,decide_eq_false (by omega : ¬171-(j+1)=0)];rfl
  rw [eqv] at guard
  let t:=v.setPC (pcAt (pairPC (j+1)))
  have mu : t.mem=u.mem:=mem
  have keep (r : Reg) (hr : r∉[Reg.x1,.x29,.x30,.x19]) : t.getReg r=u.getReg r:=
    MachineState.getReg_setPC.trans (outsideCalc pairAdv u v regs _ rfl r hr)
  have disjoint : ∀ r : Reg,envReg r → r∉[Reg.x1,.x29,.x30,.x19]:=by intro r;cases r <;> decide
  have cursor : PairCursor o.compression x t (j+1):=⟨f.env.move (fun r h=>keep r (disjoint r h)) (f.env.data.regs mu),rfl,
    (keep _ (by decide)).trans f.proof,ptr,children,dest,count,f.seen.sameMem mu,
    fun i hi=>(read_buffer_memory_congr t u mu _ _).trans (f.closed i hi)⟩
  by_cases more:j+1<171
  · rw [decide_eq_false (Nat.not_le_of_lt more)] at guard
    have step : Runs .check v t 2 2:=by dsimp only [t,pairPC];rw [if_pos more];exact guard
    exact ⟨t,n+4+2,q,by omega,bq,(f.run.trans (ofRuns o incs)).trans (ofRuns o step),cursor⟩
  · rw [decide_eq_true (Nat.le_of_not_gt more)] at guard
    have step : Runs .check v t 1 1:=by dsimp only [t,pairPC];rw [if_neg more];exact guard
    exact ⟨t,n+4+1,q,by omega,bq,(f.run.trans (ofRuns o incs)).trans (ofRuns o step),cursor⟩

theorem pairLoop (o : Oracle) (x : CheckInput) (s : MachineState) (start : PairCursor o.compression x s 0) (j : Nat) (limit : j≤171) :
    ∃ t n q,n≤106*j ∧ q≤j ∧ CheckRuns o s t n q ∧ PairCursor o.compression x t j := by
  induction j with
  | zero=>exact ⟨s,0,0,le_rfl,le_rfl,CheckRuns.refl o s,start⟩
  | succ j ih=>
    obtain ⟨u,n,q,nb,qb,p,cur⟩:=ih (by omega)
    obtain ⟨t,m,c,mb,cb,next,final⟩:=pairStep o x u j (by omega) cur
    exact ⟨t,n+m,q+c,by omega,by omega,p.trans next,final⟩

theorem completedCap (o : Oracle) (x : CheckInput) (s : MachineState) (f : PairCursor o.compression x s 171) :
    s.pc=pcAt (upperHeader 0) ∧ Level o.compression (readView x) 0 s := by
  refine ⟨f.pc,?_⟩;intro j bj
  change j<171 at bj
  change readBuffer s (upperAddr j) 32=if j<171 then capValue o.compression (readView x) j else 0
  rw [if_pos bj];exact f.closed j bj
end CommitGolfCandidate.S4.Machine
