import CommitGolfCandidate.ReconstructedCheckLeafGeometry

namespace CommitGolfCandidate.Reconstruction.CheckLeafPhysical
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOracleMemory CheckRecorded CheckLeafPlan CheckLeafCall CheckLeafWords CheckLeafGeometry
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 18000
set_option maxHeartbeats 1100000
set_option exponentiation.threshold 2048

structure Called (s : MachineState) (g : Geometry) (idx : Index) (n : Words 2) (msg : Words 32) : Prop where
  pc : s.pc=CommitBlocks.addr 197
  fp : s.getReg .x8=BitVec.ofNat 64 (g.frame+2400)
  value : s.getReg .x13=BitVec.ofNat 64 g.message
  copyBegin : s.getReg .x6=BitVec.ofNat 64 (g.frame+72)
  copyEnd : s.getReg .x7=BitVec.ofNat 64 (g.frame+328)
  cursor : s.getReg .x17=BitVec.ofNat 64 (g.frame+72)
  index : s.getReg .x16=BitVec.ofNat 64 idx.val
  nonceLow : s.getReg .x14=n 0
  nonceHigh : s.getReg .x15=n 1
  data : ∀ i : Fin 32, s.getMem (BitVec.ofNat 64 (g.message+8*i.val))=msg i
  marker : s.getMem (BitVec.ofNat 64 (g.frame+16))=3633

def callerSaved : List Reg := [.x1,.x2,.x3,.x4,.x9,.x19,.x20,.x21,.x22,.x23,.x24,.x26,.x28,.x29,.x30,.x31]
def savedUpper := Term.bin .bitAnd (.reg .x10) (.lit 63)
def lowHalf (r : Reg) := Term.bin .shr (.bin .shl (.reg r) (.lit 32)) (.lit 32)

private theorem headers : third.state.get .x25=lowHalf .x11 ∧ third.state.get .x18=lowHalf .x12 ∧
    third.state.get .x27=savedUpper ∧ callerSaved.all (fun r=>decide (third.state.get r=.reg r))=true := by decide +kernel

structure Post (s t : MachineState) (g : Geometry) (leaf : BitVec 256) : Prop where
  pc : t.pc=CommitBlocks.addr 238
  low : t.getReg .x12=leaf.extractLsb' 0 64
  mid : t.getReg .x13=leaf.extractLsb' 64 64
  upper : t.getReg .x14=leaf.extractLsb' 128 64
  high : t.getReg .x11=leaf.extractLsb' 192 64
  saved : ∀ r∈callerSaved,t.getReg r=s.getReg r
  fp : t.getReg .x8=s.getReg .x8
  headLow : t.getReg .x25=(s.getReg .x11 <<< (32 : Nat)) >>> (32 : Nat)
  headThird : t.getReg .x18=(s.getReg .x12 <<< (32 : Nat)) >>> (32 : Nat)
  headHigh : t.getReg .x27=s.getReg .x10 &&& 63#64
  frame : ∀ p, (∀ i : Fin 300, p≠BitVec.ofNat 64 (g.frame+8*i.val)) → t.getMem p=s.getMem p
  compactFrame : ∀ p, (∀ i : Fin 300, 40≤8*i.val→8*i.val<2288→p≠BitVec.ofNat 64 (g.frame+8*i.val)) → t.getMem p=s.getMem p

private theorem outside (e : Env) (p : Word) (xs : Writes) (h : ∀ w∈xs,p≠physical e w.1) :
    memory e p xs=e.initial.getMem p := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    obtain ⟨a,v⟩:=x
    rw [memory,ite_eq_right (h (a,v) (by simp))]
    exact ih (fun w k=>h _ (List.mem_cons_of_mem _ k))

/-- This segment uses arbitrary actual ABI data and an arbitrary fixed public
oracle. Both original permutation rows are available for position binding. -/
theorem positive (o : Oracle) (s : MachineState) (g : Geometry) (placed : Placed g)
    (idx : Index) (n : Words 2) (msg : Words 32) (h : Called s g idx n msg) :
    ∃ t, Segment o 196 s t (CheckLeaf.rows o idx n msg) ∧
      Post s t g (leafDigestW 240 (o.permutation (request o idx n msg 1))) := by
  let e:=env g s o idx n msg
  have source : Source e idx n msg := by
    refine ⟨h.index,h.nonceLow,h.nonceHigh,?_⟩
    intro i
    change s.getMem (physical (env g s o idx n msg) (CheckParentRun.loc 2 (8*i.val)))=_
    rw [phys_loc _ _ _ _ _ _ _ _ (by have:=i.isLt;omega)];exact h.data i
  have init : Matches e start s := by
    refine ⟨h.pc,?_,fun _=>rfl⟩
    intro r
    cases r <;> try rfl
    all_goals
      simp only [start,State.get,ite_false,reduceCtorEq,Term.val,CheckParentRun.ptr,e]
      rw [phys_loc _ _ _ _ _ _ _ _ (by decide)]
    all_goals first | exact h.fp | exact h.value | exact h.copyBegin | exact h.copyEnd | exact h.cursor
  obtain ⟨t,seg,pc,model,safe,lo,mi,up,hi⟩ := CheckLeaf.positive o e (CheckLeafGeometry.layout g placed s h.marker o idx n msg) idx n msg
    (CheckLeafGeometry.params g placed s o idx n msg source) s init
  obtain ⟨_,_,_,_,writes,fp,_⟩:=thirdReceipt.2.2
  obtain ⟨hl,ht,hh,regs⟩:=headers
  simp only [List.all_eq_true,decide_eq_true_eq] at regs
  have limited : ∀ w ∈ third.state.writes,40≤w.1.offset.toNat ∧ w.1.offset.toNat<2288 := by decide +kernel
  have narrowFrame (p : Word) (fresh : ∀ i : Fin 300,40≤8*i.val→8*i.val<2288→p≠BitVec.ofNat 64 (g.frame+8*i.val)) : t.getMem p=s.getMem p := by
    rw [model.mem,outside e p _];rfl
    intro x mem
    have inside:=limited x mem
    have reg:=writes x mem
    have ok:=safe x mem
    obtain ⟨⟨r,w⟩,v⟩:=x;change r=1 at reg;subst r
    change (decide (w.toNat%8=0) && decide (w.toNat<2400))=true at ok
    simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
    change p≠BitVec.ofNat 64 g.frame+w
    have pos : w=BitVec.ofNat 64 (8*(w.toNat/8)) := by rw [show 8*(w.toNat/8)=w.toNat by omega];simp
    rw [pos,←BitVec.ofNat_add];exact fresh ⟨_,by omega⟩ (by change 40≤8*(w.toNat/8);change 40≤w.toNat ∧ _ at inside;omega) (by change 8*(w.toNat/8)<2288;change _ ∧ w.toNat<2288 at inside;omega)

  refine ⟨t,seg,⟨pc,lo,mi,up,hi,?_,?_,?_,?_,?_,fun p far=>narrowFrame p (fun j _ _=>far j),narrowFrame⟩⟩
  · intro r mem;rw [model.regs,regs r mem];rfl
  · rw [model.regs,fp];change physical (env g s o idx n msg) (CheckParentRun.loc 1 2400)=_
    rw [phys_loc _ _ _ _ _ _ _ _ (by decide)];exact h.fp.symm
  · rw [model.regs,hl];rfl
  · rw [model.regs,ht];rfl
  · rw [model.regs,hh];rfl

end CommitGolfCandidate.Reconstruction.CheckLeafPhysical
