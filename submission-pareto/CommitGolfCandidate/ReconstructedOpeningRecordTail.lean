import CommitGolfCandidate.ReconstructedOpeningRecordMark
import CommitGolfCandidate.ReconstructedOpeningLoopRegs

namespace CommitGolfCandidate.Reconstruction.OpeningRecordTail
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningCursor OpeningQuery OpeningRowEntry
open OpeningRecordMark OpeningLoopRegs TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 18000
attribute [local irreducible] ArtifactEncoding.decode execute

def tailOps : List Op := [.reg .x12 (.addi .x14 4095),.reg .x10 (.lui 1),.reg .x10 (.sub .x8 .x10),
  .ld .x11 .x10 1920 8589934270,.reg .x11 (.addi .x11 8)]
def output (e : Env) (m : Model) := after (mark (after m setupOps) e.index) tailOps

theorem keep (e : Env) (m : Model) (w : Nat) (away : w<532480 ∨ 532608≤w) :
    (output e m).mem w=m.mem w := OpeningRecordMark.keep (after m setupOps) e.index w away

private theorem checked (m : Model) (frame : m.reg .x8=W 68719476336) : Checked m tailOps := by
  refine ⟨True.intro,True.intro,True.intro,⟨by decide,?_⟩,True.intro,True.intro⟩
  change m.reg .x8-W 4096+signExtend12 1920=wordAddress 8589934270
  rw [frame];decide

private theorem decrement (n : Nat) : W (n+1)+signExtend12 4095=W n := by
  unfold W;rw [BitVec.ofNat_add,BitVec.add_assoc];exact BitVec.add_zero _

private theorem setupFrame (m : Model) (r : Reg) (a : r≠.x7) (b : r≠.x10) (c : r≠.x11) :
    (after m setupOps).reg r=m.reg r := by
  cases r <;> first | contradiction | rfl

private theorem tailFrame (m : Model) (r : Reg) (a : r≠.x10) (b : r≠.x11) (c : r≠.x12) :
    (after m tailOps).reg r=m.reg r := by
  cases r <;> first | contradiction | rfl

private theorem markRegs (m : Model) (i : Index) (r : Reg) : (mark m i).reg r=m.reg r := rfl
private theorem tailPointer (m : Model) : (after m tailOps).reg .x11=m.mem savePtr+W 8 := rfl
private theorem tailCount (m : Model) : (after m tailOps).reg .x12=m.reg .x14+signExtend12 4095 := rfl
private theorem setupMem (m : Model) : (after m setupOps).mem=m.mem := rfl

private theorem ptrNext (ord : Nat) : wordAddress (indexWord ord)+W 8=wordAddress (indexWord (ord+1)) := by
  change W (8*indexWord ord)+W 8=W (8*indexWord (ord+1))
  rw [←BitVec.ofNat_add];congr 1

theorem registers (e : Env) (m : Model) (h : Ready9 e m) (ord remain : Nat)
    (cnt : e.count=W (remain+1)) (ptr : m.mem savePtr=wordAddress (indexWord ord)) :
    Regs (output e m) (ord+1) remain (e.cursor+3633) := by
  let a := after m setupOps
  let b := mark a e.index
  have keepReg (r : Reg) (dif : r≠.x7 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x12) :
      (output e m).reg r=m.reg r :=
    (tailFrame b r dif.2.1 dif.2.2.1 dif.2.2.2).trans
      ((markRegs a e.index r).trans (setupFrame m r dif.1 dif.2.1 dif.2.2.1))
  have restore := (OpeningRecordMark.keep a e.index savePtr (Or.inr (by decide))).trans
    ((congrFun (setupMem m) savePtr).trans ptr)
  have original := (markRegs a e.index .x14).trans ((setupFrame m .x14 (by decide) (by decide) (by decide)).trans (h.r14.trans cnt))
  refine ⟨(keepReg _ (by decide)).trans h.r0,(keepReg _ (by decide)).trans h.r2,
    (keepReg _ (by decide)).trans h.r6,?_,(keepReg _ (by decide)).trans h.r8,?_,?_,
    (keepReg _ (by decide)).trans h.r22,(keepReg _ (by decide)).trans h.r25,(keepReg _ (by decide)).trans h.r31⟩
  · exact (tailFrame b .x7 (by decide) (by decide) (by decide)).trans
      ((markRegs a e.index .x7).trans (OpeningRecordMark.setup e m h).1)
  · exact (tailPointer b).trans ((congrArg (·+W 8) restore).trans (ptrNext ord))
  · exact (tailCount b).trans ((congrArg (·+signExtend12 4095) original).trans (decrement remain))

theorem run (o : Oracle) (e : Env) (m : Model) (h : Ready9 e m) (remain : Nat)
    (cnt : e.count=W (remain+1)) (bound : remain<2^64)
    (s : MachineState) (pc : s.pc=addr 130) (f : Fits s m) :
    ∃ t n, n≤13 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧
      t.pc=(if remain=0 then addr 1429 else addr 143) ∧ Fits t (output e m) := by
  let a := after m setupOps
  let b := mark a e.index
  obtain ⟨u,ru,pu,fu⟩ := setupRun o m s pc f
  obtain ⟨_,p,one⟩ := OpeningRecordMark.setup e m h
  obtain ⟨v,rv,pv,fv⟩ := OpeningLinear.block (write o a e.index p one) (i:=135) (by decide) ⟨rfl,True.intro⟩ u pu fu
  obtain ⟨w,rw',pw,fw⟩ := OpeningStraight.block o b tailOps 136 (by decide) ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
    (checked b h.r8) v pv fv
  have val : w.getReg .x12=W remain := by
    rw [fw.registers];change m.reg .x14+signExtend12 4095=W remain
    rw [h.r14,cnt,decrement]
  have r := OpeningBranch.nonzero o w 141 142 143 .x12 8 pw (by decide) rfl (by decide) (by decide) (W remain) val
  have complete := CommitExact.compose (CommitExact.compose (CommitExact.compose ru rv) rw') r
  by_cases z : remain=0
  · subst remain
    change CommitExact.Segment _ _ _ s (w.setPC (addr 142)) at complete
    have j := OpeningBranch.jump o (w.setPC (addr 142)) 142 1429 5148 rfl (by decide) rfl (by decide)
    exact ⟨_,13,by decide,CommitExact.compose complete j,rfl,(fw.pc _).pc _⟩
  · have nz : W remain≠0 := by
      intro h;have eq := congrArg BitVec.toNat h;change remain%2^64=0 at eq;omega
    rw [if_neg nz] at complete
    exact ⟨_,12,by decide,complete,by rw [if_neg z];rfl,fw.pc _⟩

end CommitGolfCandidate.Reconstruction.OpeningRecordTail
