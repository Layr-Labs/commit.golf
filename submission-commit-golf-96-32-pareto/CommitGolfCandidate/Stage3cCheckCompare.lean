import CommitGolfCandidate.Stage3cCheckCopy
import CommitGolfCandidate.Stage3cCheckEdges
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W wordAt AddrOK)
structure CompareSite where
  start : Nat
  mismatch : Nat
  far : Bool
  lhs : Reg
  rhs : Reg
  temp : Reg
  other : Reg
def CompareSite.pc (p : CompareSite) (j : Nat):=p.start+(if p.far then 4 else 3)*j
def CompareSite.valid (p : CompareSite) :=
  p.temp≠.x0 ∧ p.other≠.x0 ∧ p.temp≠p.other ∧ p.lhs≠p.temp ∧ p.rhs≠p.temp ∧ p.lhs≠p.other ∧ p.rhs≠p.other ∧
  ∀ j : Fin 4,let n:=p.pc j.val;let imm:=BitVec.ofNat 12 (8*j.val)
    matchesWord .check (n,.LD p.temp p.lhs imm) ∧ matchesWord .check (n+1,.LD p.other p.rhs imm) ∧
    (if p.far then BranchSite (n+2) (p.pc (j.val+1)) .eq p.temp p.other ∧ JumpSite (n+3) p.mismatch .x0
     else BranchSite (n+2) p.mismatch .ne p.temp p.other)
instance instDecidableCompareSiteValid (p : CompareSite) : Decidable p.valid:=by unfold CompareSite.valid;infer_instance
def DiagKeep (p : CompareSite) (s t : MachineState) := ∀ q,q≠p.temp → q≠p.other → t.getReg q=s.getReg q
theorem DiagKeep.trans {p s t u} (x : DiagKeep p s t) (y : DiagKeep p t u) : DiagKeep p s u:=fun q a b=>(y q a b).trans (x q a b)

private theorem compare_branch (o : Oracle) (s : MachineState) (p : CompareSite) (j : Fin 4) (ok : p.valid)
    (pc : s.pc=pcAt (p.pc j.val+2)) (b : Bool) (eq : (s.getReg p.temp==s.getReg p.other)=b) :
    ∃ t steps,steps≤2 ∧ Flow o s t steps 0 ∧ t.pc=pcAt (if b then p.pc (j.val+1) else p.mismatch) ∧ t.mem=s.mem ∧
      ∀ q,t.getReg q=s.getReg q := by
  have known_:=((ok.2.2.2.2.2.2.2 j).2.2)
  let n:=p.pc j.val
  cases f : p.far
  · simp only [f,Bool.false_eq_true,ite_false] at known_
    have test : Rel.ne.test (s.getReg p.temp) (s.getReg p.other)= !b:=congrArg Bool.not eq
    have step:=branch o s (n+2) p.mismatch .ne p.temp p.other known_ pc (!b) test
    have next : n+2+1=p.pc (j.val+1):=by dsimp [n,CompareSite.pc];rw [f];simp;omega
    cases b
    · exact ⟨_,1,by decide,step,rfl,rfl,fun _=>MachineState.getReg_setPC⟩
    · exact ⟨_,1,by decide,step,congrArg pcAt next,rfl,fun _=>MachineState.getReg_setPC⟩
  · simp only [f,ite_true] at known_
    have step:=branch o s (n+2) (p.pc (j.val+1)) .eq p.temp p.other known_.1 pc b eq
    cases b
    · let u:=s.setPC (pcAt (n+3))
      have leap:=jump o u (n+3) p.mismatch .x0 known_.2 rfl
      exact ⟨_,2,by decide,step.trans leap,rfl,rfl,fun _=>MachineState.getReg_setPC.trans MachineState.getReg_setPC⟩
    · exact ⟨_,1,by decide,step,rfl,rfl,fun _=>MachineState.getReg_setPC⟩

private theorem compare_one (o : Oracle) (s : MachineState) (p : CompareSite) (j : Fin 4) (ok : p.valid)
    (a b : Nat) (pc : s.pc=pcAt (p.pc j.val)) (sa : s.getReg p.lhs=W a) (sb : s.getReg p.rhs=W b)
    (al : AddrOK a 32) (bl : AddrOK b 32) :
    let match_:=wordAt s (a+8*j.val)==wordAt s (b+8*j.val)
    ∃ t steps,steps≤4 ∧ Flow o s t steps 0 ∧ t.pc=pcAt (if match_ then p.pc (j.val+1) else p.mismatch) ∧ t.mem=s.mem ∧ DiagKeep p s t := by
  obtain ⟨t0,t1,apart,l0,r0,l1,r1,h⟩:=ok
  let n:=p.pc j.val
  let imm:=BitVec.ofNat 12 (8*j.val)
  let u:=(s.setReg p.temp (wordAt s (a+8*j.val))).setPC (pcAt (n+1))
  let v:=(u.setReg p.other (wordAt u (b+8*j.val))).setPC (pcAt (n+2))
  have word : signExtend12 imm=W (8*j.val):=(by decide +kernel : ∀ i : Fin 4,signExtend12 (BitVec.ofNat 12 (8*i.val))=W (8*i.val)) j
  have uk (q : Reg) (ne : q≠p.temp) : u.getReg q=s.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have um : u.mem=s.mem:=by unfold u;cases p.temp <;> rfl
  have ak:=al.1;have bk:=bl.1;have af:=al.2;have bf:=bl.2
  have left:=load_word o s n (a+8*j.val) p.temp p.lhs imm pc (known (h j).1) (by rw [sa,word];exact (BitVec.ofNat_add ..).symm) (by omega) (by omega)
  have right:=load_word o u (n+1) (b+8*j.val) p.other p.rhs imm rfl (known (h j).2.1)
    (by rw [uk _ r0,sb,word];exact (BitVec.ofNat_add ..).symm) (by omega) (by omega)
  have v0 : v.getReg p.temp=wordAt s (a+8*j.val):=MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ apart.symm).trans
    (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_eq t0)))
  have v1 : v.getReg p.other=wordAt s (b+8*j.val):=MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_eq t1).trans (congrFun um _))
  have vm : v.mem=u.mem:=by unfold v;cases p.other <;> rfl
  obtain ⟨t,k,small,arm,ep,mem,keep⟩:=compare_branch o v p j ⟨t0,t1,apart,l0,r0,l1,r1,h⟩ rfl _ (by rw [v0,v1])
  exact ⟨t,2+k,by omega,(left.trans right).trans arm,ep,mem.trans (vm.trans um),fun q a b=>(keep q).trans
    (MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ b.symm).trans (uk q a)))⟩

def wordsMatch (s : MachineState) (a b j n : Nat) :=(List.range' j n).all fun i=>wordAt s (a+8*i)==wordAt s (b+8*i)
theorem compare_range (o : Oracle) (s : MachineState) (p : CompareSite) (j n : Nat) (ok : p.valid) (end_ : j+n≤4)
    (a b : Nat) (pc : s.pc=pcAt (p.pc j)) (sa : s.getReg p.lhs=W a) (sb : s.getReg p.rhs=W b) (al : AddrOK a 32) (bl : AddrOK b 32) :
    ∃ t steps,steps≤4*n ∧ Flow o s t steps 0 ∧ t.pc=pcAt (if wordsMatch s a b j n then p.pc (j+n) else p.mismatch) ∧ t.mem=s.mem ∧ DiagKeep p s t := by
  induction n generalizing s j with
  | zero=>exact ⟨s,0,by decide,Flow.refl o s,pc,rfl,fun _ _ _=>rfl⟩
  | succ n ih=>
    let i : Fin 4:=⟨j,by omega⟩
    obtain ⟨u,k,kmax,first,ep,mem,keep⟩:=compare_one o s p i ok a b pc sa sb al bl
    have next : wordsMatch s a b j (n+1)=((wordAt s (a+8*j)==wordAt s (b+8*j)) && wordsMatch u a b (j+1) n) := by
      simp only [wordsMatch,List.range'_succ,List.all_cons,wordAt,MachineState.getMem,mem]
    cases eq : wordAt s (a+8*j)==wordAt s (b+8*j)
    · rw [next,eq,Bool.false_and];exact ⟨u,k,by omega,first,by simpa only [i,eq,Bool.false_eq_true,ite_false] using ep,mem,keep⟩
    · have good : u.pc=pcAt (p.pc (j+1)):=by simpa only [i,eq,ite_true] using ep
      obtain ⟨t,m,bound,last,ip,same,kept⟩:=ih u (j+1) (by omega) good ((keep _ ok.2.2.2.1 ok.2.2.2.2.2.1).trans sa)
        ((keep _ ok.2.2.2.2.1 ok.2.2.2.2.2.2.1).trans sb)
      rw [next,eq,Bool.true_and]
      exact ⟨t,k+m,by omega,first.trans last,by simpa only [show j+1+n=j+(n+1) by omega] using ip,same.trans mem,keep.trans kept⟩

theorem compare_digest (o : Oracle) (s : MachineState) (p : CompareSite) (ok : p.valid) (a b : Nat) (pc : s.pc=pcAt p.start)
    (sa : s.getReg p.lhs=W a) (sb : s.getReg p.rhs=W b) (al : AddrOK a 32) (bl : AddrOK b 32) :
    ∃ t steps,steps≤16 ∧ Flow o s t steps 0 ∧ t.pc=pcAt (if readBuffer s a 32=readBuffer s b 32 then p.pc 4 else p.mismatch) ∧ t.mem=s.mem ∧ DiagKeep p s t := by
  obtain ⟨t,k,lim,run,ep,mem,keep⟩:=compare_range o s p 0 4 ok le_rfl a b pc sa sb al bl
  have eq : wordsMatch s a b 0 4=true ↔ readBuffer s a 32=readBuffer s b 32 := by
    rw [read_digest_eq_iff _ _ _ _ al.1 bl.1,wordsMatch,←List.range_eq_range',List.all_eq_true]
    simp only [List.mem_range,beq_iff_eq];rfl
  exact ⟨t,k,lim,run,by simpa only [eq] using ep,mem,keep⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
