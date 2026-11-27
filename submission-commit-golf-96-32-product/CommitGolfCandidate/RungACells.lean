import CommitGolfCandidate.RungACellFacts
import CommitGolfCandidate.RungAHashSpec
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Machine (W Code Runs)
open R4b (NRegs Agree)
open Late (pcAt levelCount nodeAddress)

private theorem compareLt {a b : Nat} (ha:a<2^64) (hb:b<2^64) : (W a).ult (W b)=decide (a<b) := by
  simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]
theorem branchLT (o : Oracle) (s : MachineState) (p endPC a b : Nat) (ra rb : Reg) (pc:s.pc=pcAt p)
    (space:p<Code.opening.count) (word:S4.Machine.stands .opening p (.BLTU ra rb 8))
    (far:S4.Machine.directs .opening (p+1) endPC) (left:s.getReg ra=W a) (right:s.getReg rb=W b)
    (ha:a<2^64) (hb:b<2^64) :
    let cost:=if a<b then 1 else 2
    let t:=s.setPC (pcAt (if a<b then p+2 else endPC))
    DetRun o image s cost t cost 0 := by
  have jump : s.pc+signExtend13 8=pcAt (p+2):=by
    rw [pc];change W (4096+4*p)+W 8=W _;rw [←BitVec.ofNat_add];exact congrArg W (by omega)
  have inc:s.pc+4=pcAt (p+1):=(congrArg (·+4) pc).trans (Late.pc_succ _).symm
  have f:=(S4.Machine.fetched .opening p space s pc).trans (S4.Machine.stood word)
  by_cases touch:a<b
  · simp only [if_pos touch]
    apply DetRun.step1 f
    change some (if (s.getReg ra).ult (s.getReg rb) then _ else _)=_
    rw [left,right,compareLt ha hb,decide_eq_true touch,if_pos (rfl : true=true),jump]
  · simp only [if_neg touch]
    let u:=s.setPC (pcAt (p+1))
    have one:DetRun o image s 1 u 1 0:=by
      apply DetRun.step1 f
      change some (if (s.getReg ra).ult (s.getReg rb) then _ else _)=_
      rw [left,right,compareLt ha hb,decide_eq_false touch,if_neg (by decide : ¬false=true),inc]
    exact one.trans (liftRun o (S4.Machine.jump .opening (p+1) endPC u rfl far))

def keepCell (g h n : Nat) := decide (baseIndex g h+n<levelCount h)
def cellSteps (g h n : Nat) := if keepCell g h n then 4+hashLength h else 3
def cellCycles (g h n : Nat) := if keepCell g h n then 4+hashCycles h else 3
def cellCalls (g h n : Nat) := if keepCell g h n then 1 else 0
theorem cellRun (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (C : Cover) (k r g h n : Nat)
    (bg:g≤699050) (bh:h<4) (bn:n<sizeAt h) (s : MachineState)
    (pc:s.pc=pcAt (cellPC h n)) (ag : Agree (stageRegs k r g h) s)
    (mem : View o.compression td ps (frontier C g h n) s) :
    ∃ t,DetRun o image s (cellSteps g h n) t (cellCycles g h n) (cellCalls g h n) ∧
      t.pc=pcAt (cellPC h (n+1)) ∧ Agree (stageRegs k r g h) t ∧ View o.compression td ps (frontier C g h (n+1)) t := by
  let p:=cellPC h n
  have small : n<24:=by let u:Fin 4:=⟨h,bh⟩;have: sizeAt h≤24:=(show ∀ i : Fin 4,sizeAt i≤24 by decide) u;omega
  obtain ⟨ts,cmp,jump,pp,hashSiteOK,last⟩:=cellSite ⟨h,bh⟩ ⟨n,small⟩ bn
  obtain ⟨ok,kept,idx,limit,ptrs,back,a,b⟩:=cellFacts k r g h n bg bh bn
  obtain ⟨u,test,ip,mu,regs,_⟩:=arithRun o _ 1 1 _ _ s pc ag ok ts
  let j:=baseIndex g h+n
  have max : j<2^64:=by
    have bound:sizeAt h≤24:=(show ∀ d : Fin 4,sizeAt d≤24 by decide) ⟨h,bh⟩
    have low:=Nat.mul_le_mul bound bg
    change sizeAt h*g+n<2^64;omega
  have bv:levelCount h<2^64:=(Late.level_count_le _).trans_lt (by decide)
  have edge:=branchLT o u (p+1) (cellPC h (n+1)) j (levelCount h) (testReg h) (limReg h) ip
    (by have room : p+3+2≤Code.opening.count:=pp.2.2.2;omega) cmp jump (regs _ _ idx) (regs _ _ limit) max bv
  have restored : Agree (stageRegs k r g h) u:=Agree.weaken regs kept
  by_cases real:j<levelCount h
  · simp only [if_pos real] at edge
    let v:=u.setPC (pcAt (p+3))
    have agV : Agree (finalRegs (stageRegs k r g h) (testOps h n)) v:=regs
    obtain ⟨w,setup,wp,mw,all,_⟩:=arithRun o (p+3) 2 2 _ _ v rfl agV ptrs pp
    have st : Agree (stageRegs k r g h) w:=Agree.weaken all back
    have core (reg : Reg) (v : Nat) (hold : ∀ d : Fin 4,stageRegs k r g d reg=some v) := st _ _ (hold ⟨h,bh⟩)
    obtain ⟨z,call,ipz,rz,endMem⟩:=hash.runHash g h n (p+5) bh bn real ((mem.ofMem mu).ofMem (show w.mem=u.mem from mw)) wp hashSiteOK
      (core .x5 0 (fun _=>rfl)) (core .x11 96 (fun _=>rfl)) (core .x13 0 (fun _=>rfl)) (all _ _ a) (all _ _ b)
    have yes : keepCell g h n=true:=decide_eq_true real
    simp only [cellSteps,cellCycles,cellCalls,yes,ite_true]
    exact ⟨z,((test.trans edge).trans setup).trans call,ipz.trans (congrArg pcAt last),
      fun reg v eq=>(rz _).trans (st _ _ eq),endMem⟩
  · simp only [if_neg real] at edge
    have no : keepCell g h n=false:=decide_eq_false real
    simp only [cellSteps,cellCycles,cellCalls,no,Bool.false_eq_true,ite_false]
    exact ⟨_,test.trans edge,rfl,restored,((mem.ofMem mu).equiv (frontierSkip C g h n (Nat.le_of_not_gt real))).ofMem rfl⟩

def sumN (f : Nat→Nat) : Nat→Nat | 0=>0 | n+1=>sumN f n+f n
theorem bankRun (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (C : Cover) (k r g h : Nat)
    (bg:g≤699050) (bh:h<4) (s : MachineState) (pc:s.pc=pcAt (firstCell h)) (ag : Agree (stageRegs k r g h) s)
    (mem : View o.compression td ps (frontier C g h 0) s) :
    let n:=sizeAt h
    ∃ t,DetRun o image s (sumN (cellSteps g h) n) t (sumN (cellCycles g h) n) (sumN (cellCalls g h) n) ∧
      t.pc=pcAt (cellPC h n) ∧ Agree (stageRegs k r g h) t ∧ View o.compression td ps (frontier C g (h+1) 0) t := by
  have ind (n : Nat) (lim:n≤sizeAt h) :
      ∃ t,DetRun o image s (sumN (cellSteps g h) n) t (sumN (cellCycles g h) n) (sumN (cellCalls g h) n) ∧
        t.pc=pcAt (cellPC h n) ∧ Agree (stageRegs k r g h) t ∧ View o.compression td ps (frontier C g h n) t := by
    induction n with
    | zero=>exact ⟨s,DetRun.refl o image s,by simpa [cellPC] using pc,ag,mem⟩
    | succ n ih=>
      obtain ⟨u,pre,atN,ready,seen⟩:=ih (by omega)
      obtain ⟨v,last,next,done,view⟩:=cellRun hash o td ps C k r g h n bg bh (by omega) u atN ready seen
      exact ⟨v,pre.trans last,next,done,view⟩
  obtain ⟨t,path,ip,j,v⟩:=ind (sizeAt h) le_rfl
  exact ⟨t,path,ip,j,v.equiv (frontierEnd C g h)⟩
end CommitGolfCandidate.RungA
