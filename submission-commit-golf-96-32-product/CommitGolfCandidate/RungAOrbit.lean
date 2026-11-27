import CommitGolfCandidate.RungAIteration
import CommitGolfCandidate.RungAHandoff
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (Agree)
open S4.Open (initial indices)
open S4.Machine (W)
open Late (pcAt)
def countFor (xs : List Index) := (xs.map (perIndex .twentyFour)).sum

theorem countAll (ps : Positions) : countFor (indices ps)=publicCalls .twentyFour ps := by
  have eqv : (↑(indices ps) : Multiset Index)=ps.val:=Finset.sort_eq _ _
  change _=(ps.val.map (perIndex .twentyFour)).sum
  rw [←eqv];rfl

theorem loopRun (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (non:0<ps.card) (s : MachineState)
    (pc:s.pc=pcAt 17870) (ag : Agree (baseRegs ps.card 0) s) (mem:View o.compression td ps (seen []) s) :
    ∃ t n c,DetRun o image s n t c (publicCalls .twentyFour ps) ∧ n≤257*ps.card ∧ c+1≤553*ps.card ∧
       t.pc=pcAt 18165 ∧ Agree (finishRegs ps.card) t ∧ View o.compression td ps (selected .twentyFour ps) t := by
  let k:=ps.card;let xs:=indices ps
  have ind (r : Nat) (br:r≤k) : ∃ t n c,DetRun o image s n t c (countFor (xs.take r)) ∧ n≤257*r ∧
      c+(if r=k then 1 else 0)≤553*r ∧ t.pc=pcAt (edgePC k r) ∧ Agree (baseRegs k r) t ∧
      View o.compression td ps (seen (xs.take r)) t := by
    induction r with
    | zero=>
      refine ⟨s,0,0,DetRun.refl o image s,by decide,?_,?_,ag,mem⟩
      · simp only [k,if_neg (by omega : ¬0=ps.card)];omega
      · simpa only [edgePC,k,if_neg (by omega : ¬0=ps.card)] using pc
    | succ r ih=>
      obtain ⟨u,n,c,pre,ns,cs,ip,regs,known⟩:=ih (by omega)
      have lt:r<k:=by omega
      rw [edgePC,if_neg (by omega : r≠k)] at ip
      obtain ⟨t,step,out,ready,view⟩:=iteration hash o td ps r lt u ip regs known
      let i:=S4.recordIndex ps r
      have hx:r<xs.length:=by simpa only [xs,indices,Finset.length_sort] using lt
      have pick : xs[r]=i:=(show (xs[r]?).getD ⟨0,by decide⟩=xs[r] by rw [List.getElem?_eq_getElem hx];rfl).symm
      have nextCount : countFor (xs.take (r+1))=countFor (xs.take r)+perIndex .twentyFour i:=by
        rw [List.take_succ_eq_append_getElem hx,pick];simp [countFor]
      rw [nextCount]
      refine ⟨_,_,_,pre.trans step,?_,?_,out,ready,view⟩
      · have a:ordSteps i≤252:=by unfold ordSteps;split <;> decide
        have b:edgeCost k r≤2:=by unfold edgeCost;split <;> decide
        change n+(1+ordSteps i+2+edgeCost k r)≤257*(r+1)
        omega
      · have a:ordCycles i≤548:=by unfold ordCycles;split <;> decide
        change c+(1+ordCycles i+2+edgeCost k r)+(if r+1=k then 1 else 0)≤553*(r+1)
        unfold edgeCost;split <;> omega
  obtain ⟨t,n,c,whole,ns,cs,atEnd,ready,known⟩:=ind k le_rfl
  have len:xs.length=k:=Finset.length_sort ..
  rw [List.take_of_length_le len.le,countAll] at whole
  rw [List.take_of_length_le len.le] at known
  exact ⟨t,n,c,whole,ns,by simpa using cs,by simpa [edgePC] using atEnd,Agree.weaken ready (lastOK k),known.equiv (selectedSeen ps)⟩

private theorem abiValue (td : Late.Trapdoor) (ps : Positions) (r : Reg) :
    (initial td ps).getReg r=W ((abi ps.card r).getD 0) := by
  cases r
  case x2=>exact congrArg W Late.openingDataBase
  all_goals rfl

theorem boot (o : Oracle) (td : Late.Trapdoor) (ps : Positions) :
    let k:=ps.card;let s:=initial td ps
    ∃ t,DetRun o image s 5 t 5 0 ∧ t.mem=s.mem ∧ t.pc=pcAt (if k=0 then 18165 else 17860) ∧
      Agree (finalRegs (abi k) initOps) t := by
  intro k s
  have ag : Agree (abi k) s:=by intro reg n h;change abi ps.card reg=some n at h;change (initial td ps).getReg reg=W n;simpa only [h,Option.getD_some] using abiValue td ps reg
  have first:=liftRun o (S4.Machine.jump .opening 0 17856 s rfl (by decide))
  let u:=s.setPC (pcAt 17856)
  obtain ⟨v,setup,ip,m,regs,_⟩:=arithRun o 17856 3 3 initOps (abi k) u rfl ag (setupOK k) initSite
  have ctrl:=S4.Machine.branch .opening 17859 18165 .x18 .x0 true (by decide) v ip
  rw [regs _ _ (testInit k)] at ctrl
  have bound:k≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have cmp:((W k==v.getReg .x0)==true)=decide (k=0):=by
    change ((W k==W 0)==true)=_;rw [S4.Machine.eqNatural _ _ (by omega) (by decide)];simp
  rw [cmp] at ctrl
  let t:=v.setPC (pcAt (if k=0 then 18165 else 17860))
  have one : DetRun o image v 1 t 1 0:=by
    apply liftRun;by_cases ek:k=0 <;> simpa [t,ek] using ctrl
  exact ⟨t,(first.trans setup).trans one,m,rfl,regs⟩

theorem restored (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (s : MachineState)
    (pc:s.pc=pcAt 18165) (ag : Agree (finishRegs ps.card) s) (known : View o.compression td ps (selected .twentyFour ps) s) :
    ∃ t,DetRun o image s 24 t 24 0 ∧ WriterEntry .twentyFour (Late.submission.image .commit) image o td ps t := by
  have bk:ps.card≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  obtain ⟨ok,back⟩:=restoreOK ps.card bk
  obtain ⟨u,math,ip,mem,regs,_⟩:=arithRun o 18165 23 23 restoreOps _ s pc ag ok restoreSite
  have far:=liftRun o (S4.Machine.jump .opening 18188 1 u ip (by decide))
  let t:=u.setPC (pcAt 1)
  have same:t.mem=s.mem:=mem
  have v:=known.ofMem same
  have finalRegs : Agree (original ps.card) t:=Agree.weaken regs back
  refine ⟨t,math.trans far,savedTD t,savedRebuilt v,rfl,?_,savedBytes v⟩
  intro reg
  change t.getReg reg=((initial (savedTD t) ps).setReg .x6 128).getReg reg
  by_cases e:reg=.x6
  · subst reg;exact (finalRegs .x6 128 rfl).trans (MachineState.getReg_setReg_eq (by decide)).symm
  · rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm e),abiValue]
    apply finalRegs
    simp only [original,if_neg e];cases reg <;> rfl

theorem prelude (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) :
    ∃ s n c,DetRun o image (initial td ps) n s c (publicCalls .twentyFour ps) ∧
      n≤260*ps.card+50 ∧ (ps.card=BATCH → c≤70822) ∧ WriterEntry .twentyFour (Late.submission.image .commit) image o td ps s := by
  obtain ⟨u,front,mem,ip,base⟩:=boot o td ps
  have empty : View o.compression td ps (seen []) (initial td ps):=by
    refine ⟨?_,?_,fun _ _ _=>rfl⟩ <;> intro h j hit <;> rcases hit with ⟨i,im,_⟩ <;> cases im
  by_cases zero:ps.card=0
  · rw [if_pos zero] at ip
    rw [zero] at base
    have reg : Agree (finishRegs ps.card) u:=by rw [zero];exact Agree.weaken base emptyOK
    have eps:ps=∅:=Finset.card_eq_zero.mp zero
    have view : View o.compression td ps (selected .twentyFour ps) u:=(empty.ofMem mem).equiv (by
      intro h j;simp [seen,selected,eps])
    obtain ⟨s,tail,done⟩:=restored o td ps u ip reg view
    have calls : publicCalls .twentyFour ps=0:=by simp [publicCalls,eps]
    rw [calls];exact ⟨s,29,29,front.trans tail,by omega,fun _=>by decide,done⟩
  · rw [if_neg zero] at ip
    obtain ⟨ok,form⟩:=constantsOK ps.card
    obtain ⟨v,init,pc,m,cfg,_⟩:=arithRun o 17860 10 10 constantsOps _ u ip base ok constantsSite
    obtain ⟨w,n,c,loop,nb,cb,last,ready,view⟩:=loopRun hash o td ps (by omega) v pc (Agree.weaken cfg form) (empty.ofMem (m.trans mem))
    obtain ⟨s,tail,done⟩:=restored o td ps w last ready view
    refine ⟨s,15+n+24,15+c+24,?_,by omega,?_,done⟩
    · simpa only [Nat.zero_add,Nat.add_zero] using ((front.trans init).trans loop).trans tail
    · intro batch;change ps.card=128 at batch;omega
end CommitGolfCandidate.RungA
