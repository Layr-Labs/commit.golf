import CommitGolfCandidate.ReconstructedCheckBranch
import CommitGolfCandidate.ReconstructedCheckRecordHeader

namespace CommitGolfCandidate.Reconstruction.CheckCapCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps CheckRecorded CommitBlocks
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def ops (src dst : Nat) : List Op := [
  .reg .x29 (.addi .x8 2048),.reg .x29 (.addi .x29 3784),.reg .x1 (.addi .x0 65),
  .ld .x10 .x8 3808 (src+3),.sd .x22 .x10 24 (dst+3),
  .ld .x10 .x8 3800 (src+2),.sd .x22 .x10 16 (dst+2),
  .ld .x10 .x8 3792 (src+1),.sd .x22 .x10 8 (dst+1),
  .ld .x10 .x8 3784 src,.sd .x22 .x10 0 dst]

def after (m : Model) (src dst : Nat) := (ops src dst).foldl (fun a op=>op.apply a) m

private theorem listed (src dst : Nat) : CheckStraight.Listed 617 ((ops src dst).map Op.instr):=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩

private theorem offset (b k base : Nat) (imm : BitVec 12) (h : wordAddress base+signExtend12 imm=wordAddress k) :
    wordAddress (b+base)+signExtend12 imm=wordAddress (b+k) := by rw [wordAddress_add,BitVec.add_assoc,h,←wordAddress_add]

private theorem valid (m : Model) (src dst : Nat) (room : src+4≤2^33 ∧ dst+4≤2^33)
    (fp : m.reg .x8=wordAddress (src+39)) (out : m.reg .x22=wordAddress dst) : Checked m (ops src dst) := by
  simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩⟩
  all_goals change m.reg _+signExtend12 _=_
  · rw [fp];exact offset src 3 39 3808 (by decide)
  · rw [out];exact (wordAddress_add dst 3).symm
  · rw [fp];exact offset src 2 39 3800 (by decide)
  · rw [out];exact (wordAddress_add dst 2).symm
  · rw [fp];exact offset src 1 39 3792 (by decide)
  · rw [out];exact (wordAddress_add dst 1).symm
  · rw [fp];exact (offset src 0 39 3784 (by decide)).trans (by rw [Nat.add_zero])
  · rw [out];exact BitVec.add_zero _

private theorem write_shape (m : Model) (src dst : Nat) (apart : src+4≤dst ∨ dst+4≤src) :
    (after m src dst).mem=writeWord (writeWord (writeWord (writeWord m.mem (dst+3) (m.mem (src+3)))
      (dst+2) (m.mem (src+2))) (dst+1) (m.mem (src+1))) dst (m.mem src) := by
  simp [after,ops,Op.apply,Model.set,Model.store,writeWord,show src+2≠dst+3 by omega,
    show src+1≠dst+2 by omega,show src+1≠dst+3 by omega,show src≠dst+1 by omega,
    show src≠dst+2 by omega,show src≠dst+3 by omega]

attribute [local irreducible] after

/-- The return block copies the four computed words to the parent slot and advances the cap loop. -/
theorem complete (o : Oracle) (s : MachineState) (src dst : Nat) (pc : s.pc=addr 617)
    (room : src+4≤2^33 ∧ dst+4≤2^33) (apart : src+4≤dst ∨ dst+4≤src)
    (fp : s.getReg .x8=wordAddress (src+39)) (out : s.getReg .x22=wordAddress dst) :
    ∃ t, Segment o 12 s t [] ∧ t.pc=addr 605 ∧
      (∀ i : Fin 4, t.getMem (wordAddress (dst+i.val))=s.getMem (wordAddress (src+i.val))) ∧
      (∀ a, a<2^33 → (a<dst ∨ dst+4≤a) → t.getMem (wordAddress a)=s.getMem (wordAddress a)) ∧
      t.getReg .x1=65 ∧ t.getReg .x29=s.getReg .x8+signExtend12 2048+signExtend12 3784 ∧
      (∀ v : Reg,v≠.x1→v≠.x29→v≠.x10→t.getReg v=s.getReg v) := by
  let m:=CheckRecordHeader.model s
  obtain ⟨u,sg,hu,hm⟩:=CheckStraight.block o m (ops src dst) 617 (by change 617+11≤796;decide) (listed _ _)
    (valid m src dst room fp out) s pc (CheckRecordHeader.fits s)
  have typ : Fits u (after m src dst):=by unfold after;exact hm
  have j:=CheckBranch.jump o u 628 605 2097060 (by decide) hu (by rfl) (by decide)
  refine ⟨_,by simpa only [List.nil_append,show (ops src dst).length=11 by rfl] using compose sg j,rfl,?_,?_,?_,?_,?_⟩
  · intro i;change u.getMem _=_
    have eq:=typ.memory (dst+i.val) (by have:=i.isLt;omega)
    rw [write_shape _ _ _ apart] at eq
    fin_cases i <;> simpa [writeWord,m,CheckRecordHeader.model,TwoPermutationPrototype.RV64.memoryView] using eq
  · intro a bound fresh;change u.getMem _=_
    have eq:=typ.memory a bound;rw [write_shape _ _ _ apart] at eq
    simpa only [m,CheckRecordHeader.model,memoryView,writeWord,ite_eq_right (by omega : a≠dst),ite_eq_right (by omega : a≠dst+1),
      ite_eq_right (by omega : a≠dst+2),ite_eq_right (by omega : a≠dst+3)] using eq
  · change u.getReg .x1=65;rw [typ.registers];unfold after
    change (0#64)+signExtend12 65=65;decide
  · change u.getReg .x29=_;rw [typ.registers];unfold after;rfl
  · intro v a b c;change u.getReg v=_
    rw [typ.registers];unfold after;simp [ops,Op.apply,Model.set,Model.store,a.symm,b.symm,c.symm,m,CheckRecordHeader.model]


theorem positive (o : Oracle) (s : MachineState) (src dst : Nat) (pc : s.pc=addr 617)
    (room : src+4≤2^33 ∧ dst+4≤2^33) (apart : src+4≤dst ∨ dst+4≤src)
    (fp : s.getReg .x8=wordAddress (src+39)) (out : s.getReg .x22=wordAddress dst) :
    ∃ t, Segment o 12 s t [] ∧ t.pc=addr 605 ∧
      (∀ i : Fin 4, t.getMem (wordAddress (dst+i.val))=s.getMem (wordAddress (src+i.val))) ∧
      (∀ a, a<2^33 → (a<dst ∨ dst+4≤a) → t.getMem (wordAddress a)=s.getMem (wordAddress a)) ∧
      (∀ v : Reg,v≠.x1→v≠.x29→v≠.x10→t.getReg v=s.getReg v) := by
  obtain ⟨t,seg,loc,words,frame,_,_,keep⟩:=complete o s src dst pc room apart fp out
  exact ⟨t,seg,loc,words,frame,keep⟩

end CommitGolfCandidate.Reconstruction.CheckCapCopy
