import CommitGolfCandidate.ReconstructedCheckParentHeap

namespace CommitGolfCandidate.Reconstruction.CheckParentCallCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix Binding CheckParentHeap
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

set_option maxRecDepth 14000
set_option maxHeartbeats 1300000
attribute [local irreducible] execute ArtifactEncoding.decode CheckParent.Cost

def preserved : List Reg := [.x2,.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]
def log (o : Oracle) (e : Nat) (l r : Binding.Digest) := CheckParentExecution.rows o (pairKey (e+1) l r) 0 (work e)

theorem run (o : Oracle) (s : MachineState) (e : Fin 24) (p : Nat) (small : p<512)
    (pc : s.pc=addr 612) (sp : s.getReg .x2=W CheckLayout.sp) (fp : s.getReg .x8=W CheckLayout.fp)
    (depth : s.getReg .x9=W e.val) (pair : s.getReg .x18=W (base (2*p))) (out : s.getReg .x22=W (base p))
    (tables : CheckParentGeometry.constants s) (l r : Binding.Digest) (left : CommitParents.cell s (base (2*p))=l)
    (right : CommitParents.cell s (base (2*p+1))=r) :
    ∃ t, Segment o (5+CheckParent.Cost e+12) s t (log o e l r) ∧ t.pc=addr 605 ∧
      CommitParents.cell t (base p)=parent (oracleCompression o) e l r ∧ t.getReg .x1=65 ∧
      t.getReg .x29=W CheckCapScanData.scratch ∧ Frame p (p+1) s t ∧ (∀ v∈preserved,t.getReg v=s.getReg v) := by
  have rt : CommitParents.cell s ((g p).pair+32)=r:=by change CommitParents.cell s (base (2*p)+32)=r;rw [←next];exact right
  obtain ⟨u,call,up,outcome,spU,fpU,cs,fr⟩:=CheckCapCall.positive o s (g p) e (placed p small)
    ⟨pc,sp,fp,depth,pair⟩ tables l r left rt
  have heapU : u.getReg .x22=wordAddress (word p):=(cs .x22 (by decide)).trans (out.trans (location p))
  have frameU : u.getReg .x8=wordAddress (temp+39):=fpU.trans fp
  obtain ⟨t,copy,atEnd,values,copied,one,scratch,keep⟩:=CheckCapCopy.complete o u temp (word p) up
    ⟨by decide,by unfold word;omega⟩ (.inr (by unfold temp word;omega)) frameU heapU
  have dirty : Frame p (p+1) s t := by
    intro w bound parent stack dest
    have sep : w<word p ∨ word p+4≤w := by unfold word at *;omega
    refine (copied w bound sep).trans (fr _ ?_ ?_)
    · intro i eq;have same:=congrArg BitVec.toNat eq;have hi:=i.isLt
      change (8*w)%2^64=(68719473152+8*i.val)%2^64 at same
      unfold stackWord at stack;omega
    · intro i eq;have same:=congrArg BitVec.toNat eq;have hi:=i.isLt
      change (8*w)%2^64=(68719475416+8*i.val)%2^64 at same
      unfold temp at dest;omega
  refine ⟨t,by simpa only [log,List.append_nil] using compose call copy,atEnd,?_,one,?_,dirty,?_⟩
  · apply Eq.trans _ outcome
    apply CheckParentHeap.values _ _ (by unfold base;omega) (by change 68719475416%8=0;decide)
    intro i
    rw [words]
    change t.getMem (wordAddress (word p+i.val))=u.getMem (W (68719475416+8*i.val))
    rw [values];change u.getMem (W (8*(8589934427+i.val)))=_
    congr 2;omega
  · rw [scratch,fpU,fp];rfl
  · intro v mem
    have facts : v≠.x1 ∧ v≠.x29 ∧ v≠.x10 ∧ (v=.x2 ∨ v=.x8 ∨ v∈CheckParentPlan.preserved) := by
      cases v <;> first | decide | simp [preserved] at mem
    rw [keep v facts.1 facts.2.1 facts.2.2.1]
    rcases facts.2.2.2 with eq|eq|h
    · subst v;exact spU
    · subst v;exact fpU
    · exact cs v h

end CommitGolfCandidate.Reconstruction.CheckParentCallCopy

