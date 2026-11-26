import CommitGolfCandidate.S5CheckBoot
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def recordBegin (b : Bool) := if b then 233 else 1282
def expectLen (b : Bool) (k : Nat):=if b then 69396 else 824*k
def sizeSite (b : Bool):=if b then 228 else 1278
def sizeOps : Bool→List Sym.Calc
  | true=>[.lui .x6 17,.addi .x6 .x6 3860]
  | false=>[.addi .x6 .x0 824,.mul .x6 .x6 .x23]
theorem word_eq (a b : Nat) (ha : a<2^64) (hb : b<2^64) : (W a==W b)=decide (a=b) := by
  by_cases eq : a=b
  · subst a;simp
  · have ne : W a≠W b:=by intro h;have num:=congrArg BitVec.toNat h;simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at num;exact eq num
    simp only [beq_eq_false_iff_ne.mpr ne,decide_eq_false eq]
private theorem size_entry (o : Oracle) (s : MachineState) (k : Nat) (limit : k≤16777216) (pc : s.pc=pcAt 225) (cnt : s.getReg .x23=W k) :
    let b:=decide (k=128)
    ∃ t nSteps, nSteps≤3 ∧ Flow o s t nSteps 0 ∧ t.pc=pcAt (sizeSite b) ∧ t.mem=s.mem ∧
      ∀ q,q≠.x6 → t.getReg q=s.getReg q := by
  let u:=(s.setReg .x6 128).setPC (pcAt 226)
  have put:=imm_step o s 225 .x6 .x0 128 128 pc (known (by decide +kernel)) rfl
  let b:=decide (k=128)
  have cond : Rel.eq.test (u.getReg .x23) (u.getReg .x6)=b:=by change (s.getReg .x23==W 128)=_;rw [cnt];exact word_eq k 128 (by omega) (by decide)
  have choose:=branch o u 226 228 .eq .x23 .x6 (by decide +kernel) rfl b cond
  have keep (q : Reg) (h : q≠.x6) : u.getReg q=s.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm)
  by_cases eq : k=128
  · simp only [b,eq,decide_true,ite_true] at choose ⊢
    exact ⟨_,2,by decide,put.trans choose,rfl,rfl,fun q h=>MachineState.getReg_setPC.trans (keep q h)⟩
  · simp only [b,decide_eq_false eq,Bool.false_eq_true,ite_false] at choose ⊢
    have leap:=jump o (u.setPC (pcAt 227)) 227 1278 .x0 (by decide +kernel) rfl
    exact ⟨_,3,by decide,(put.trans choose).trans leap,rfl,rfl,fun q h=>MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (keep q h))⟩

structure Dispatched (o : Oracle) (x : CheckInput) (s : MachineState) (b valid : Bool) (steps : Nat) : Prop where
  run : Flow o (initial x) s steps 0
  pc : s.pc=pcAt (if valid then recordBegin b else 2333)
  mem : s.mem=(initial x).mem
  radix : s.getReg .x3=3
  leaf : s.getReg .x24=W leafBuf
  row : s.getReg .x25=W rowBuf
  chain : s.getReg .x26=W chainBuf
  digest : s.getReg .x27=W digestBuf
  root : s.getReg .x8=W rootBase
  ix : s.getReg .x9=W indexBase
  value : s.getReg .x18=W valueBase
  proof : s.getReg .x19=W proofBase
  end_ : s.getReg .x20=W (proofBase+x.proof.length+(if b && valid then 1 else 0))
  num : s.getReg .x23=W x.positions.card
  held : s.getReg .x21=0
  bits : s.getReg .x22=0

private theorem size_terms (b : Bool) (s : MachineState) (k : Nat) (num : s.getReg .x23=W k) :
    (((sizeOps b).foldl Sym.bump Sym.original) .x6).eval s = W (expectLen b k) := by
  cases b
  · change 824#64*s.getReg .x23=_
    rw [num];exact (BitVec.ofNat_mul 824 k).symm
  · change 69632#64+signExtend12 3860=W 69396;decide
private theorem kept_terms (b : Bool) (s : MachineState) (q : Reg) (ne : q≠.x6) :
    (((sizeOps b).foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by cases b <;> cases q <;> first | contradiction | rfl
private theorem size_test (o : Oracle) (s : MachineState) (b : Bool) (k len : Nat) (kBound : k≤16777216) (lBound : len≤17179869184)
    (pc : s.pc=pcAt (sizeSite b)) (num : s.getReg .x23=W k) (length : s.getReg .x17=W len) (end_ : s.getReg .x20=W (proofBase+len)) :
    let valid:=decide (len=expectLen b k)
    ∃ t n,n≤4 ∧ Flow o s t n 0 ∧ t.pc=pcAt (if valid then recordBegin b else 2333) ∧ t.mem=s.mem ∧
      t.getReg .x20=W (proofBase+len+(if b && valid then 1 else 0)) ∧ ∀ q,q≠.x6 → q≠.x20 → t.getReg q=s.getReg q := by
  let u:=Sym.evaluated (sizeOps b) s
  have code : ∀ mode : Bool,Sym.Listed (sizeOps mode) (sizeSite mode):=by decide +kernel
  obtain ⟨prep,reg,mem,ip⟩:=Sym.compiled o _ _ s pc (code b) (by cases b <;> change ∀ e∈([] : List (Sym.Expr×Nat)),_ <;> simp)
  have sz : (sizeOps b).length=2:=by cases b <;> rfl
  rw [sz] at prep ip
  have keep (q : Reg) (h : q≠.x6) : u.getReg q=s.getReg q:=(reg q).trans (kept_terms b s q h)
  have matchLen : Rel.eq.test (u.getReg .x17) (u.getReg .x6)=decide (len=expectLen b k):=by
    change (_==_)=_;rw [keep .x17 (by decide),length,(reg .x6).trans (size_terms b s k num)]
    apply word_eq <;> cases b <;> dsimp [expectLen] <;> omega
  let valid:=decide (len=expectLen b k)
  have sites : ∀ b : Bool,BranchSite (sizeSite b+2) (sizeSite b+4) .eq .x17 .x6 ∧ JumpSite (sizeSite b+3) 2333 .x0:=by decide +kernel
  have test:=branch o u (sizeSite b+2) (sizeSite b+4) .eq .x17 .x6 (sites b).1 ip valid matchLen
  have ep : u.getReg .x20=W (proofBase+len):=(keep _ (by decide)).trans end_
  by_cases ok : len=expectLen b k
  · have yes : valid=true:=decide_eq_true ok
    rw [yes] at test
    simp only [decide_eq_true ok,ite_true,Bool.and_true]
    cases b with
    | false=>exact ⟨_,3,by decide,prep.trans test,rfl,mem,MachineState.getReg_setPC.trans ep,fun q h _=>MachineState.getReg_setPC.trans (keep q h)⟩
    | true=>
      let z:=u.setPC (pcAt 232)
      have inc:=imm_step o z 232 .x20 .x20 1 (W (proofBase+len+1)) rfl (known (by decide +kernel)) ((congrArg (·+signExtend12 1) ep).trans (BitVec.ofNat_add _ 1).symm)
      exact ⟨_,4,by decide,(prep.trans test).trans inc,rfl,mem,rfl,fun q h e=>MachineState.getReg_setPC.trans
        ((MachineState.getReg_setReg_ne _ _ _ _ e.symm).trans (MachineState.getReg_setPC.trans (keep q h)))⟩
  · have no : valid=false:=decide_eq_false ok
    rw [no] at test
    simp only [decide_eq_false ok,Bool.false_eq_true,ite_false,Bool.and_false]
    have leap:=jump o (u.setPC (pcAt (sizeSite b+3))) _ _ .x0 (sites b).2 rfl
    exact ⟨_,4,by decide,(prep.trans test).trans leap,rfl,mem,MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans ep),
      fun q h _=>MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (keep q h))⟩

theorem dispatch (o : Oracle) (x : CheckInput) (nonempty : 0<x.positions.card) (fit : x.proof.length≤17179869184) :
    let b:=decide (x.positions.card=BATCH)
    ∃ t n,n≤25 ∧ Dispatched o x t b (decide (x.proof.length=expectLen b x.positions.card)) n := by
  obtain ⟨s,ready⟩:=boot o x nonempty
  let k:=x.positions.card
  let b:=decide (k=128)
  have bound : k≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  obtain ⟨u,m,lim,choose,first,mem,keep⟩:=size_entry o s k bound ready.pc ready.input.num
  obtain ⟨t,n,lim',test,last,same,ep,hold⟩:=size_test o u b k x.proof.length bound fit first ((keep _ (by decide)).trans ready.input.num)
    ((keep _ (by decide)).trans ready.input.length) ((keep _ (by decide)).trans ready.input.end_)
  have safe (q : Reg) (qh : q≠.x6) (qe : q≠.x20) : t.getReg q=s.getReg q:=(hold q qh qe).trans (keep q qh)
  refine ⟨t,18+m+n,by omega,⟨(ready.run.trans choose).trans test,last,same.trans (mem.trans ready.mem),
    (safe _ (by decide) (by decide)).trans ready.radix,(safe _ (by decide) (by decide)).trans ready.leaf,
    (safe _ (by decide) (by decide)).trans ready.row,(safe _ (by decide) (by decide)).trans ready.chain,
    (safe _ (by decide) (by decide)).trans ready.digest,(safe _ (by decide) (by decide)).trans ready.input.root,
    (safe _ (by decide) (by decide)).trans ready.input.indices,(safe _ (by decide) (by decide)).trans ready.input.values,
    (safe _ (by decide) (by decide)).trans ready.input.proof,ep,(safe _ (by decide) (by decide)).trans ready.input.num,
    (safe _ (by decide) (by decide)).trans ready.input.held,(safe _ (by decide) (by decide)).trans ready.input.bits⟩⟩
end CommitGolfCandidate.S5Machine.Check
