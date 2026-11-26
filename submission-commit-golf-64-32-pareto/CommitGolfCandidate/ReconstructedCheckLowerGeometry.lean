import CommitGolfCandidate.ReconstructedCheckLowerWords
import CommitGolfCandidate.ReconstructedCheckLowerPlan

namespace CommitGolfCandidate.Reconstruction.CheckLowerGeometry
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckParentRun CheckStream CheckLowerPlan
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

structure Placed (g : Reader) : Prop extends CheckStream.Placed g where
  widthAlign : g.widthCell%8=0
  maskAlign : g.maskCell%8=0
  widthRoom : g.widthCell+8≤MEMORY_BYTES
  maskRoom : g.maskCell+8≤MEMORY_BYTES
  flags : g.widthCell≠g.maskCell
  widthApart : g.widthCell+8≤wordBase g ∨ wordBase g+40≤g.widthCell
  maskApart : g.maskCell+8≤wordBase g ∨ wordBase g+40≤g.maskCell

private def limit : Nat→Nat | 3=>40 | 5=>8 | 6=>8 | _=>0

private theorem good {a : Loc} (w : Nat) (h : (table w).allowed a=true) :
    (a.region=3 ∨ a.region=5 ∨ a.region=6) ∧ a.offset.toNat%8=0 ∧ a.offset.toNat+8≤limit a.region := by
  change decide (_ ∨ _)=true at h
  rcases of_decide_eq_true h with ⟨reg,al,x⟩|⟨r,z⟩
  · rw [reg];change _ ∧ _ ∧ a.offset.toNat+8≤40;omega
  · rw [z];rcases r with r|r <;> rw [r] <;> decide

theorem layout (s : MachineState) (g : Reader) (placed : Placed g) (width : Nat)
    (widthValue : s.getMem (BitVec.ofNat 64 g.widthCell)=BitVec.ofNat 64 width)
    (maskValue : s.getMem (BitVec.ofNat 64 g.maskCell)=0xffffffff) : Layout (env s g) (table width) := by
  have reg (a : Loc) (ok : (table width).allowed a=true) :
      base g a.region%8=0 ∧ base g a.region+limit a.region≤MEMORY_BYTES := by
    rcases (good width ok).1 with r|r|r <;> rw [r]
    · exact ⟨by have:=placed.align;change (g.proofBase+8*g.block)%8=0;omega,placed.room⟩
    · exact ⟨placed.widthAlign,placed.widthRoom⟩
    · exact ⟨placed.maskAlign,placed.maskRoom⟩
  have small (a : Loc) (v : (table width).allowed a=true) : base g a.region+a.offset.toNat<2^64 := by
    have b:=(reg a v).2;have k:=(good width v).2.2;unfold MEMORY_BYTES at b;omega
  constructor
  · intro a v
    have h:=good width v;have t:=reg a v
    rw [phys]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (small a v),Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  · intro a b va vb same
    obtain ⟨ar,_,ha⟩:=good width va;obtain ⟨br,_,hb⟩:=good width vb
    have n:=congrArg BitVec.toNat same
    simp only [phys,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (small a va),Nat.mod_eq_of_lt (small b vb)] at n
    have r : a.region=b.region := by
      rcases ar with ra|ra|ra <;> rcases br with rb|rb|rb <;> simp only [ra,rb,base,limit] at n ha hb ⊢ <;>
        have a:=placed.widthApart <;> have b:=placed.maskApart <;> have c:=placed.flags <;> omega
    have k : a.offset=b.offset := by apply BitVec.eq_of_toNat_eq;rw [r] at n;omega
    cases a;cases b;simp_all
  · intro a v found
    change (if a=loc 5 0 then some (BitVec.ofNat 64 width) else if a=loc 6 0 then some 0xffffffff else none)=some v at found
    split_ifs at found <;> try contradiction
    · rename_i p;subst a;cases found;change s.getMem _=_;rw [point];exact widthValue
    · rename_i p;subst a;cases found;change s.getMem _=_;rw [point];exact maskValue

theorem read (o : Oracle) (s : MachineState) (g : Reader) (placed : Placed g) (r : Fin 64) (d : Fin 15) (stream : Nat)
    (source : CheckStream.Source s g stream) (pc : s.pc=CommitBlocks.addr 280)
    (cursor : s.getReg .x24=BitVec.ofNat 64 (64*g.block+r.val)) (baseReg : s.getReg .x19=BitVec.ofNat 64 g.proofBase)
    (widthReg : s.getReg .x9=BitVec.ofNat 64 g.widthCell) (frame : s.getReg .x8=BitVec.ofNat 64 (g.maskCell+2368))
    (widthValue : s.getMem (BitVec.ofNat 64 g.widthCell)=BitVec.ofNat 64 (lowWidth (10+d.val)))
    (maskValue : s.getMem (BitVec.ofNat 64 g.maskCell)=0xffffffff) :
    let c:=64*g.block+r.val
    let w:=lowWidth (10+d.val)
    ∃ t, CheckRecorded.Segment o (done r w).ticks s t [] ∧ t.pc=CommitBlocks.addr 350 ∧
      (t.getReg .x10).toNat=HonestStream.get stream c 64 ∧ (t.getReg .x16).toNat=HonestStream.get stream (c+64) 64 ∧
      (t.getReg .x17).toNat=HonestStream.get stream (c+128) 64 ∧ (t.getReg .x6).toNat=HonestStream.get stream (c+192) (w-192) ∧
      t.getReg .x5=BitVec.ofNat 64 (w-192) ∧ t.getReg .x15=BitVec.ofNat 64 w ∧ t.getReg .x24=BitVec.ofNat 64 (c+192) ∧
      (∀ p,t.getMem p=s.getMem p) ∧ t.getReg .x7=11 ∧ t.getReg .x28=s.getReg .x26+(-8) ∧
      (∀ v∈CheckLowerPlan.keep,t.getReg v=s.getReg v) ∧ Matches (env s g) (done r w).state t := by
  let w:=lowWidth (10+d.val)
  let e:=env s g
  have match0 : Matches e (CheckLowerPlan.start r) s := by
    refine ⟨pc,?_,fun _=>rfl⟩;intro reg;cases reg <;> try rfl
    all_goals
      simp only [CheckLowerPlan.start,State.get,ite_false,reduceCtorEq,Term.val,ptr,e]
      rw [point]
    all_goals first | exact cursor | exact baseReg | exact widthReg | exact frame
  have src:=CheckStream.input s g stream source
  obtain ⟨t,sg,hm,pos,lo,mi,hi,top,nb,wd,cur,mem,cost⟩:=
    positive o e (context s g (block_bound g placed.toPlaced)) r d (layout s g placed _ widthValue maskValue) s match0
  have ww : 192≤w ∧ w≤240 := (by decide : ∀ k : Fin 15,192≤lowWidth (10+k.val) ∧ lowWidth (10+k.val)≤240) d
  obtain ⟨guard,sub,retained⟩:=CheckLowerPlan.control_ok r d
  refine ⟨t,sg,pos,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hm⟩
  · rw [hm.regs,lo];exact CheckLowerWords.low e stream _ r src
  · rw [hm.regs,mi];exact CheckLowerWords.mid e stream _ r 1 (by decide) src
  · rw [hm.regs,hi];exact CheckLowerWords.mid e stream _ r 2 (by decide) src
  · rw [hm.regs,top];exact CheckLowerWords.high e stream _ r w ww src
  · rw [hm.regs,nb];rfl
  · rw [hm.regs,wd];rfl
  · rw [hm.regs,cur];change physical (env s g) (loc 1 (r.val+192))=_
    rw [point];change BitVec.ofNat 64 (64*g.block+(r.val+192))=_
    rw [Nat.add_assoc]
  · intro p;rw [hm.mem,mem];rfl
  · rw [hm.regs,guard];rfl
  · rw [hm.regs,sub];rfl
  · intro v hv;rw [hm.regs,retained _ hv,←match0.regs]

end CommitGolfCandidate.Reconstruction.CheckLowerGeometry
