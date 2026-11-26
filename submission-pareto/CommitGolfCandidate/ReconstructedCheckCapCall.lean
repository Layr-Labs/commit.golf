import CommitGolfCandidate.ReconstructedCheckPairPhysical
import CommitGolfCandidate.ReconstructedCommitParentsSave

namespace CommitGolfCandidate.Reconstruction.CheckCapCall
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckValues CheckRecorded CheckParentRun CheckParentGeometry
set_option maxRecDepth 16000
set_option maxHeartbeats 1100000

abbrev W:=BitVec.ofNat 64

def code : List CheckLink.Op := [
  .plain (.basic (.arith (.addiw .x11 .x9 0))),.plain (.basic (.arith (.addi .x10 .x8 3784))),
  .plain (.basic (.arith (.addi .x12 .x18 0))),.auipc .x1 0,.jalr .x1 .x1 236]

def start (d : Fin 24) : State where
  pc:=CommitBlocks.addr 612
  regs:=fun r=>match r with
    | .x8=>ptr 1 312
    | .x9=>.lit (W d)
    | _=>.reg r
  writes:=[]

def run (d : Fin 24) := CheckLink.run (CheckRegion.tab 32) (CommitBlocks.addr 612) code (start d)
def done (d : Fin 24) := (run d).getD (start d)

def facts (d : Fin 24) : Prop := (run d).isSome=true ∧ (done d).pc=CommitBlocks.addr 674 ∧ (done d).writes=[] ∧
    (done d).get .x11=.lit (W d) ∧ (done d).get .x10=ptr 1 0 ∧ (done d).get .x12=.reg .x18 ∧
    (done d).get .x8=(start d).get .x8 ∧ (done d).get .x1=.lit (CommitBlocks.addr 617) ∧ (done d).get .x2=.reg .x2 ∧
    ∀ r ∈ CheckParentPlan.preserved, (done d).get r=(start d).get r
deriving instance Decidable for facts

private theorem checked : ∀ d : Fin 24, facts d := by decide +kernel

structure Called (s : MachineState) (g : Geometry) (d : Fin 24) : Prop where
  pc : s.pc=CommitBlocks.addr 612
  sp : s.getReg .x2=W (g.stack+144)
  fp : s.getReg .x8=W (g.out+312)
  depth : s.getReg .x9=W d
  pair : s.getReg .x18=W g.pair

/-- The cap loop calls the same parent procedure with the contiguous pair in the cap table. -/
theorem positive (o : Oracle) (s : MachineState) (g : Geometry) (d : Fin 24) (placed : Placed g)
    (call : Called s g d) (rodata : constants s) (l r : Binding.Digest)
    (left : CommitParents.cell s g.pair=l) (right : CommitParents.cell s (g.pair+32)=r) :
    ∃ t, Segment o (5+CheckParent.Cost d) s t (CheckParentExecution.rows o (pairKey (d.val+1) l r) 0 (work d)) ∧
      t.pc=CommitBlocks.addr 617 ∧ CommitParents.cell t g.out=parent (oracleCompression o) d l r ∧
      t.getReg .x2=s.getReg .x2 ∧ t.getReg .x8=s.getReg .x8 ∧ (∀ v∈CheckParentPlan.preserved,t.getReg v=s.getReg v) ∧
      (∀ p, (∀ i : Fin 18,p≠W (g.stack+8*i.val)) → (∀ i : Fin 4,p≠W (g.out+8*i.val)) → t.getMem p=s.getMem p) := by
  let e:=CheckRegion.env s g.out
  have owner : Layout e (CheckRegion.tab 32):=CheckRegion.layout s g.out 32 (placed.align 3) (by decide) (placed.room 3)
  have ok : Matches e (start d) s:=by
    refine ⟨call.pc,?_,fun _=>rfl⟩;intro v;cases v <;> try rfl
    · change s.getReg .x8=physical (CheckRegion.env s g.out) (loc 1 312);rw [CheckRegion.point];exact call.fp
    · exact call.depth
  obtain ⟨existsRun,pc,blank,depth,dest,pair,fp,ret,stack,regs⟩:=checked d
  have replay : run d=some (done d):=by unfold done;cases h:run d <;> simp_all
  obtain ⟨u,before,hm,_⟩:=CheckLink.run_sound o e (CheckRegion.tab 32) owner code _ (start d) (done d) s ok
    (fun _ h=>by cases h) (CheckDecode.sound _ _ (by decide)) replay
  have mem : ∀ p,u.getMem p=s.getMem p:=by intro p;rw [hm.mem,blank];rfl
  have called : CheckParent.Called u d g:= by
    refine ⟨hm.pc.trans pc,?_,?_,?_,?_⟩
    · rw [hm.regs,stack];exact call.sp
    · rw [hm.regs,dest];change physical (CheckRegion.env s g.out) (loc 1 0)=_;rw [CheckRegion.point,Nat.add_zero]
    · rw [hm.regs,depth];rfl
    · rw [hm.regs,pair];exact call.pair
  have cell (a : Nat) : CommitParents.cell u a=CommitParents.cell s a := by
    apply CommitParents.cell_congr;funext w;exact mem w
  obtain ⟨t,hash,post⟩:=CheckParent.positive o g placed u d called (fun a v al source=>(mem _).trans (rodata a v al source)) l r
    ((cell _).trans left) ((cell _).trans right)
  refine ⟨t,by simpa only [List.nil_append,show code.length=5 by decide] using compose before hash,?_,post.output,?_,?_,?_,?_⟩
  · rw [post.returnPC,hm.regs,ret];exact (by decide : (CommitBlocks.addr 617+signExtend12 0 &&& ~~~1#64)=CommitBlocks.addr 617)
  · rw [post.stack,hm.regs,stack];rfl
  · rw [post.framePointer,hm.regs,fp,←ok.regs]
  · intro v member;rw [post.calleeSaved _ member,hm.regs,regs _ member,←ok.regs]
  · intro p a b;exact (post.memory p a b).trans (mem p)

end CommitGolfCandidate.Reconstruction.CheckCapCall
