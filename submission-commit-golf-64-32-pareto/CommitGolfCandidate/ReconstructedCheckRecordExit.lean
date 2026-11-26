import CommitGolfCandidate.ReconstructedCheckRecordDecision

namespace CommitGolfCandidate.Reconstruction.CheckRecordExit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckLayout CheckRecordABI CheckRecordSlots CheckRecordDecision CheckWalkValues
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
abbrev W:=BitVec.ofNat 64

def Accepts (v : View) (a : Slots) (idx : Index) := v.header=[0,0,0,0] ∧ Compatible a (heap idx 9) v.node
deriving instance Decidable for Accepts

private theorem frame {s t : MachineState} (m : CheckRecordAccess.Mem s t) : CheckRecordFrame.Frame s t := CheckRecordFrame.fromWords m

private theorem finish (o : Oracle) (s : MachineState) (input : CheckInput) (i : Fin input.positions.card) (a : Slots) (idx : Index) (v : View)
    (k : Nat) (key : k=heap idx 9) (p : Persistent s input) (sh : Holds s a) (pc : s.pc=CommitBlocks.addr 386)
    (sp : s.getReg .x2=W CheckLayout.sp) (fp : s.getReg .x8=W CheckLayout.fp) (proof : s.getReg .x19=W proofBase)
    (route : s.getReg .x23=W k) (marker : s.getReg .x10=0xffffffffffffffff#64)
    (cursor : s.getReg .x24=W (CheckRecordSpec.cursor (i.val+1))) (node : CheckPairPhysical.child s CheckPair.current v.node)
    (ordinal : s.getMem (W (CheckLayout.fp-2376))=W i.val) :
    ∃ t n,n≤36 ∧ Segment o n s t [] ∧ (if Compatible a k v.node then Advance t input (replace a k v.node) (i.val+1) else Failure t) := by
  have small : k<1024:=key ▸ (hashRange idx).2
  obtain ⟨u,access,h⟩:=CheckRecordAccess.positive o s k small pc route fp
  have pu:=CheckRecordFrame.persistent (frame h.memory) p
  have su:=sameWord sh h.memory
  have nu : CheckPairPhysical.child u CheckPair.current v.node:=fun j=>
    (h.preserved _ ((by decide : ∀ j : Fin 4,CheckPair.current j∈CheckRecordAccess.keep) j)).trans (node j)
  have prepc : u.pc=(if u.getByte (CheckRecordAccess.flag k)=0 then CommitBlocks.addr 109 else CommitBlocks.addr 398):=by
    change u.pc=(if u.getByte (W (4259840+k))=0 then _ else _);rw [CheckRecordAccess.bytes h.memory (4259840+k) (by omega)];exact h.pc
  obtain ⟨z,n,bound,cmp,zpc,zr,zm⟩:=decision o u a k v.node small su nu prepc h.shifted
  have pz:=CheckRecordFrame.persistent (frame zm) pu
  have full (r : Reg) (one : r∈CheckRecordAccess.keep) (two : r∈checkKeep) : z.getReg r=s.getReg r:=
    (zr r two).trans (h.preserved r one)
  by_cases yes : Compatible a k v.node
  · rw [ite_eq_left yes] at zpc
    have iz : z.getMem (W (CheckLayout.fp-2376))=W i.val:=by
      rw [show W (CheckLayout.fp-2376)=wordAddress 8589934169 by decide,zm _ (by decide),h.memory _ (by decide)];exact ordinal
    have limit : input.positions.card≤2^24:=by simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ input.positions
    have x5 : z.getReg .x5=W input.positions.card:=(zr .x5 (by decide)).trans (h.count.trans p.count)
    obtain ⟨t,store,after⟩:=CheckRecordWrite.positive o z k i input.positions.card small (Nat.lt_of_lt_of_le i.isLt limit) limit zpc
      ((zr .x15 (by decide)).trans h.flagAddr) ((zr .x23 (by decide)).trans h.shifted)
      ((full .x8 (by decide) (by decide)).trans fp) x5 iz
    have nz : CheckPairPhysical.child z CheckPair.current v.node:=fun j=>(zr _ ((by decide : ∀ j : Fin 4,CheckPair.current j∈checkKeep) j)).trans (nu j)
    refine ⟨t,12+n+13,by omega,by simpa only [List.nil_append] using compose (compose access cmp) store,?_⟩
    rw [ite_eq_left yes]
    refine ⟨?_,(after.keep .x2 (by decide)).trans ((full .x2 (by decide) (by decide)).trans sp),
      (after.keep .x8 (by decide)).trans ((full .x8 (by decide) (by decide)).trans fp),after.next,
      (after.keep .x24 (by decide)).trans ((full .x24 (by decide) (by decide)).trans cursor),
      (after.keep .x19 (by decide)).trans ((full .x19 (by decide) (by decide)).trans proof),
      (after.keep .x6 (by decide)).trans ((zr .x6 (by decide)).trans h.beginCopy),
      (after.keep .x7 (by decide)).trans ((zr .x7 (by decide)).trans h.endCopy),
      CheckRecordImmutable.carry (CheckRecordEffect.fixed after small) pz,
      CheckRecordEffect.holds (sameWord su zm) after small v.node nz,(after.keep .x5 (by decide)).trans x5⟩
    by_cases last : i.val+1=input.positions.card <;> simpa only [last,ite_true,ite_false] using after.pc
  · refine ⟨z,12+n,by omega,by simpa only [List.nil_append] using compose access cmp,?_⟩
    rw [ite_eq_right yes];exact ⟨by simpa only [ite_eq_right yes] using zpc,(full .x10 (by decide) (by decide)).trans marker,
      (full .x2 (by decide) (by decide)).trans sp,pz.returnPC⟩

theorem positive (o : Oracle) (s : MachineState) (input : CheckInput) (i : Fin input.positions.card) (a : Slots) (idx : Index) (v : View)
    (p : Persistent s input) (sh : Holds s a) (atS : At s idx 9 v) (cursor : v.cursor=CheckRecordSpec.cursor (i.val+1))
    (ordinal : s.getMem (W (CheckLayout.fp-2376))=W i.val) :
    ∃ t n,n≤41 ∧ Segment o n s t [] ∧ (if Accepts v a idx then Advance t input (replace a (heap idx 9) v.node) (i.val+1) else Failure t) := by
  obtain ⟨u,guard,pc,status,keep,mem⟩:=CheckRecordGuard.positive o s atS.pc
  have pu:=CheckRecordFrame.persistent (frame mem) p
  rw [atS.head] at pc
  by_cases hd : v.header=[0,0,0,0]
  · rw [ite_eq_left hd] at pc
    have nu : CheckPairPhysical.child u CheckPair.current v.node:=fun j=>
      (keep _ ((by decide : ∀ j : Fin 4,CheckPair.current j∈CheckRecordGuard.keep) j)).trans (atS.node j)
    have ord : u.getMem (W (CheckLayout.fp-2376))=W i.val:=by
      rw [show W (CheckLayout.fp-2376)=wordAddress 8589934169 by decide,mem _ (by decide)];exact ordinal
    obtain ⟨t,n,lim,tail,post⟩:=finish o u input i a idx v _ rfl pu (sameWord sh mem) pc
      ((keep .x2 (by decide)).trans atS.sp) ((keep .x8 (by decide)).trans atS.fp) ((keep .x19 (by decide)).trans atS.proof)
      ((keep .x23 (by decide)).trans atS.route) status ((keep .x24 (by decide)).trans (atS.bit.trans (congrArg W cursor))) nu ord
    exact ⟨t,5+n,by omega,by simpa only [List.nil_append] using compose guard tail,by simpa only [Accepts,hd,true_and] using post⟩
  · refine ⟨u,5,by decide,guard,?_⟩
    rw [ite_eq_right (fun h=>hd h.1)];exact ⟨by simpa only [ite_eq_right hd] using pc,status,(keep .x2 (by decide)).trans atS.sp,pu.returnPC⟩

end CommitGolfCandidate.Reconstruction.CheckRecordExit
