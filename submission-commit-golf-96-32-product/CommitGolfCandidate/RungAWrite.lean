import CommitGolfCandidate.RungALive
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1300000
attribute [local irreducible] execute readBuffer DetRun

theorem scratchApart (i j : Nat) (ne : i≠j) : Apart (32*i) 32 (32*j) := by unfold Apart;omega

theorem preserve {o d c b s t} (live : Live o d c b s) (dst : Dest)
    (small : DestOK dst)
    (v : Term) (stored : readBuffer t (location c dst) 32=d.eval v)
    (away : MemPreservedOutside s t (location c dst) (location c dst+32))
    (st : Stable s t) :
    Frame c s t ∧ R4.Env t ∧ t.getReg .x21=Z (rowPtr c+1920) ∧ t.getReg .x22=Z c.base ∧
      (∀ j,j<c.limit → readBuffer t (address c (.leaf j)) 96=d.row j) ∧
      (∀ n,n<32 → readBuffer t (32*n) 32=d.eval ((b.put dst v).cells n)) ∧
      (∀ z,(b.put dst v).out=some z → readBuffer t (location c .output) 32=d.eval z) := by
  have db:=destBounds c
  have size:=(show c.limit≤24 from c.small)
  have group:=c.gfit
  refine ⟨?_,Env.stable live.env st,(st _ (by decide)).trans live.source,(st _ (by decide)).trans live.dest,?_,?_,?_⟩
  · intro a n lo hi range
    apply away.readBuffer_eq hi
    cases dst with
    | scratch j=>change j<32 at small;exact Or.inr (by change 32*j+32≤a;omega)
    | output=>exact range
  · intro j valid
    apply (away.readBuffer_eq ?_ (Or.inr ?_)).trans (live.rows j valid)
    · dsimp [address,rowPtr,rowBase,displacement];omega
    · cases dst with
      | scratch i=>change i<32 at small;dsimp [location,address,rowPtr,rowBase,displacement];omega
      | output=>change location c .output+32≤rowPtr c+displacement j;dsimp [rowPtr,rowBase,displacement];omega
  · intro n fit
    cases dst with
    | scratch j=>
      change readBuffer t (32*n) 32=d.eval (if n=j then v else b.cells n)
      by_cases eq : n=j
      · subst j;rw [if_pos rfl];exact stored
      · rw [if_neg eq];exact (away.readBuffer_eq (by omega) (scratchApart n j eq)).trans (live.scratch _ fit)
    | output=>exact (away.readBuffer_eq (by omega) (Or.inl (by omega))).trans (live.scratch _ fit)
  · intro z mem
    cases dst with
    | output=>change some v=some z at mem;cases mem;exact stored
    | scratch j=>
      change j<32 at small
      exact (away.readBuffer_eq (by omega) (Or.inr (by change 32*j+32≤location c .output;omega))).trans (live.out z mem)

structure Step (o : Oracle) (d : Data o) (c : Layout) (s t : MachineState) (n k q : Nat) (b : Bank) : Prop where
  run : MRun o s k t (k+7*q) q
  pc : t.pc=pcAt (n+k)
  stable : Stable s t
  frame : Frame c s t
  live : Live o d c b t

theorem callStep {o d c b s} (live : Live o d c b s) (n : Nat) (pc : s.pc=pcAt n)
    (w : List Nat) (src : Source) (dst : Dest) (set sh : Bool)
    (allowed_ : allowed c.limit w b (.call src dst set sh)=true)
    (sites : listed n ((Act.call src dst set sh).ops c.off)=true) :
    ∃ t,Step o d c s t n (((Act.call src dst set sh).ops c.off).length) 1 (b.put dst (b.word src sh)) := by
  have valid : ReadOK c sh src ∧ DestOK dst ∧ (set=false → b.ptr=some dst) := by
    cases src <;> cases dst <;> cases set <;> cases sh <;> simp [ReadOK,DestOK,allowed] at allowed_ ⊢ <;> tauto
  have source : SourceOK c src := by
    have h:=valid.1
    cases src with
    | leaf=>exact h.1
    | scratch=>exact h
  have db:=destBounds c
  have align : location c dst%8=0 ∧ location c dst+32≤MEMORY_BYTES := by
    cases dst with
    | output=>exact ⟨db.2.2,db.2.1.trans (by decide)⟩
    | scratch j=>have bound : j<32:=valid.2.1;dsimp [location,MEMORY_BYTES];omega
  have safe:=sourceBounds c src source
  have p0 : Site n (.ADDI .x10 (srcReg src) (srcImm src)) := by
    have site:=listHere sites 0 (by cases set <;> cases sh <;> simp [Act.ops])
    cases src <;> cases set <;> simpa [Site,Here,Act.ops,sourceOp,srcReg,srcImm] using site
  have p1 (h : set=true) : Site (n+1) (.ADDI .x12 (dstReg dst) (dstImm c.off dst)) := by
    subst set
    have site:=listHere sites 1 (by cases sh <;> simp [Act.ops])
    cases dst <;> simpa [Site,Here,Act.ops,destOp,dstReg,dstImm] using site
  let k:=if set then 2 else 1
  obtain ⟨u,p⟩:=assign o s n (location c dst) (address c src) (srcReg src) (dstReg dst)
    (srcImm src) (dstImm c.off dst) set pc (srcEq live src source) (dstEq live dst valid.2.1)
    (by cases dst <;> simp [dstReg]) (fun h=>live.ptr dst (valid.2.2 h)) p0 p1
  have ecall : Site (n+k) .ECALL := by
    have site:=listHere sites k (by cases set <;> cases sh <;> simp [Act.ops,k])
    cases set <;> cases sh <;> simpa [Site,Here,Act.ops,k] using site
  have short (h : sh=true) : Site (n+k+1) (.SH .x12 .x0 30) := by
    subst sh
    have site:=listHere sites (k+1) (by cases set <;> simp [Act.ops,k])
    cases set <;> simpa [Site,Here,Act.ops,k,Nat.add_assoc] using site
  obtain ⟨t,put⟩:=hash o s u n k (address c src) (location c dst) live.env p _ rfl sh safe.1 align.1 safe.2 align.2 ecall short
  have used : ((Act.call src dst set sh).ops c.off).length=k+1+(if sh then 1 else 0) := by cases set <;> cases sh <;> rfl
  rw [used]
  obtain ⟨fr,env,sr,dr,rs,cs,out⟩:=preserve live dst valid.2.1 (b.word src sh)
    (put.result.trans (wordEq live src sh valid.1)) put.away put.stable
  exact ⟨t,put.run,put.pc,put.stable,fr,env,sr,dr,rs,cs,out,fun a mem=>by
    have eq : dst=a:=Option.some.inj (by cases dst <;> exact mem)
    subst a;exact put.ptr⟩

theorem oneStep {o d c b s} (live : Live o d c b s) (n : Nat) (pc : s.pc=pcAt n) (w : List Nat) (a : Act)
    (ok : allowed c.limit w b a=true) (sites : listed n (a.ops c.off)=true) :
    ∃ t,Step o d c s t n (a.ops c.off).length a.queries (update b a) := by
  cases a with
  | call src dst set sh=>exact callStep live n pc w src dst set sh ok sites
  | clear j=>
    have fit : j<32:=(show j∈w ∧ j<32 from of_decide_eq_true ok).2
    obtain ⟨t,run,ip,regs,away,stored⟩:=clearCell o s n j fit sites pc
    obtain ⟨fr,e,sr,dr,rs,cs,out⟩:=preserve live (.scratch j) fit .zero stored away (fun r _=>regs r)
    exact ⟨t,run,ip,fun r _=>regs r,fr,e,sr,dr,rs,cs,out,fun dst h=>(regs _).trans (live.ptr dst h)⟩

theorem executePlan {o d c} (w : List Nat) (ls : List Act) (n : Nat) (b : Bank) (s : MachineState)
    (live : Live o d c b s) (pc : s.pc=pcAt n)
    (ok : legal c.limit w b ls=true) (sites : listed n (code ls c.off)=true) :
    ∃ t,Step o d c s t n (code ls c.off).length (queries ls) (ls.foldl update b) := by
  induction ls generalizing n b s with
  | nil=>exact ⟨s,DetRun.refl o (R4.submission.image .commit) s,pc,fun _ _=>rfl,fun _ _ _ _ _=>rfl,live⟩
  | cons a ls ih=>
    obtain ⟨en,more⟩:=Bool.and_eq_true_iff.mp ok
    change listed n (a.ops c.off++code ls c.off)=true at sites
    obtain ⟨one,rest⟩:=listed_take sites
    obtain ⟨u,first⟩:=oneStep live n pc w a en one
    obtain ⟨t,last⟩:=ih _ _ _ first.live first.pc more rest
    change ∃ t,Step o d c s t n (a.ops c.off++code ls c.off).length (a.queries+queries ls) (ls.foldl update (update b a))
    rw [List.length_append]
    exact ⟨t,by rw [Nat.mul_add];convert first.run.trans last.run using 1 <;> omega,
      by simpa only [Nat.add_assoc] using last.pc,first.stable.trans last.stable,first.frame.trans last.frame,last.live⟩
end CommitGolfCandidate.RungA.Kernel
