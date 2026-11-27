import CommitGolfCandidate.RungALevels
import CommitGolfCandidate.S4Header
import CommitGolfCandidate.RungABoundaryFacts
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (Agree alu aluGet aluKeep)
open S4.Machine (W indexBase)
open S4.Open (indices)
open Late (pcAt)
def edgePC (k r : Nat) := if r=k then 18165 else 17870
def edgeCost (k r : Nat) := if r+1=k then 1 else 2
def cheap (i : Index) := decide (i.val/24=699050)
def ordSteps (i : Index) := if cheap i then 229 else 252
def ordCycles (i : Index) := if cheap i then 448 else 548

theorem queryPrice (i : Index) : perIndex .twentyFour i=(if i.val/24=699050 then 27 else 38) := by
  rw [perIndex_exact];have b:i.val<16777216:=i.isLt
  change 38-(if i.val≥16777200 then 11 else 0)=_;split_ifs <;> omega

private theorem indexLoad (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (r : Nat) (br:r<ps.card)
    (s : MachineState) (C : Cover) (mem : View o.compression td ps C s) (ag : Agree (baseRegs ps.card r) s) (pc:s.pc=pcAt 17870) :
    let i:=S4.recordIndex ps r
    let t:=alu s .x19 (W i.val)
    DetRun o image s 1 t 1 0 ∧ t.pc=pcAt 17871 ∧ t.mem=s.mem ∧ Agree (loaded ps.card r i.val) t := by
  intro i t
  have len:ps.card≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have ptr:=ag .x9 (indexBase+8*r) rfl
  have ld:=R4b.justLoad s .x19 .x9 0 (indexBase+8*r) (by rw [ptr];exact BitVec.add_zero _)
    ⟨by unfold indexBase;change _≤68719476736;omega,by unfold indexBase;omega⟩
  rw [mem.index r br] at ld
  have got:=ld.exec 17870 pc (by decide) (S4.Machine.matchesListed (by decide : S4.Machine.listed .opening 17870 [.LD .x19 .x9 0]))
  refine ⟨liftRun o got.1,got.2,rfl,?_⟩
  intro reg n h;unfold loaded at h;split at h
  next eq=>subst reg;cases h;exact aluGet _ _ _ (by decide)
  next ne=>exact (aluKeep _ _ _ _ (Ne.symm ne)).trans (ag _ _ h)

theorem iteration (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (r : Nat) (br:r<ps.card) (s : MachineState)
    (pc:s.pc=pcAt 17870) (ag : Agree (baseRegs ps.card r) s) (mem : View o.compression td ps (seen ((indices ps).take r)) s) :
    let i:=S4.recordIndex ps r;let c:=edgeCost ps.card r
    ∃ t,DetRun o image s (1+ordSteps i+2+c) t (1+ordCycles i+2+c) (perIndex .twentyFour i) ∧
      t.pc=pcAt (edgePC ps.card (r+1)) ∧ Agree (baseRegs ps.card (r+1)) t ∧ View o.compression td ps (seen ((indices ps).take (r+1))) t := by
  intro i c
  let u:=alu s .x19 (W i.val)
  obtain ⟨first,ip,same,loaded⟩:=indexLoad o td ps r br s _ mem ag pc
  obtain ⟨v,body,atEnd,state,updated⟩:=groupBody hash o td ps ((indices ps).take r) r i u ip loaded (mem.ofMem same)
  obtain ⟨ok,forms⟩:=nextOK ps.card r (i.val/24) br
  obtain ⟨w,inc,edge,nm,post,_⟩:=arithRun o 18161 2 2 updateOps _ v atEnd state ok updateSite
  have ready:=Agree.weaken post forms
  have ctrl:=S4.Machine.alternate .opening 18163 18165 17870 .x18 .x0 true (by decide) (by decide) rfl w edge
  have len : ps.card≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have cnt:=ready .x18 (ps.card-(r+1)) rfl
  have cmp : ((w.getReg .x18==w.getReg .x0)==true)=decide (r+1=ps.card):=by
    rw [cnt];change ((W _==W 0)==true)=_
    rw [S4.Machine.eqNatural _ _ (by omega) (by decide)]
    by_cases last:r+1=ps.card
    · simp only [decide_eq_true last,decide_eq_true (by omega : ps.card-(r+1)=0)];rfl
    · simp only [decide_eq_false last,decide_eq_false (by omega : ¬ps.card-(r+1)=0)];rfl
  rw [cmp] at ctrl
  let z:=w.setPC (pcAt (edgePC ps.card (r+1)))
  have last : DetRun o image w c z c 0:=by
    apply liftRun
    by_cases e:r+1=ps.card <;> simp [z,c,edgePC,edgeCost,e] at ctrl ⊢ <;> exact ctrl
  have hr:r<(indices ps).length:=by simpa [indices] using br
  have xs : ((indices ps).take r)++[i]=(indices ps).take (r+1):=by
    rw [List.take_succ_eq_append_getElem hr];change _++[(indices ps)[r]?.getD _]=_
    rw [List.getElem?_eq_getElem hr];rfl
  rw [xs] at updated
  refine ⟨z,?_,rfl,ready,updated.ofMem nm⟩
  have all:=((first.trans body).trans inc).trans last
  simpa only [ordSteps,ordCycles,cheap,Bool.decide_coe,decide_eq_true_eq,Nat.zero_add,Nat.add_zero,queryPrice] using all
end CommitGolfCandidate.RungA
