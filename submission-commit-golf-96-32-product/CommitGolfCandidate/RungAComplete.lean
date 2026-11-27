import CommitGolfCandidate.RungAGround
import CommitGolfCandidate.RungAGroupMath
import CommitGolfCandidate.RungAUpper
import CommitGolfCandidate.R4Root
import CommitGolfCandidate.RungALaw
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp R4 Late
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000
attribute [local irreducible] execute readBuffer DetRun
inductive Schedule where | compact | rotating deriving DecidableEq
def fusedSteps : Schedule → Nat | .compact=>79866578 | .rotating=>79437617
def fusedCycles (k : Schedule) := fusedSteps k + 7*27262978
def commitPrice : Schedule → Nat | .compact=>841142282 | .rotating=>840713321
def FusedPhase (k : Schedule) := ∀ (o : Oracle) (m : Message) (r : Tape) (s : MachineState),
    Env s → s.pc=pcAt 131123 → Inputs o m r s →
    ∃ t,MRun o s (fusedSteps k) t (fusedCycles k) 27262978 ∧ t.pc=pcAt 238455 ∧ Env t ∧
      t.getReg .x28=16383 ∧ Ground o m r t ∧
      Upper.Levels o.compression (Kernel.baseLeaf o m r) 4 t

private theorem schedule : Upper.bill layerSteps 20=3497481 ∧ Upper.bill layerCycles 20=8390901 ∧
    Upper.bill nodes 20=699060 := by decide +kernel

private theorem sliceRead (s : MachineState) (a n : Nat) (lo : tdAddress≤a) (hi : a+n≤7650414624) :
    slice (readBuffer s tdAddress 3355443200) a n=readBuffer s a n := by
  unfold slice
  exact (read_buffer_slice s tdAddress 3355443200 (a-tdAddress) n (by dsimp [tdAddress] at *;omega)).trans
    (congrArg (fun x=>readBuffer s x n) (show tdAddress+(a-tdAddress)=a by omega))

theorem suffix_of_phase (k : Schedule) (fused : FusedPhase k) :
    FixedTapeCommit .twentyFour (R4.submission.image .commit) (commitPrice k) := by
  intro o m r s seed
  obtain ⟨u,pre,ip,eu,input⟩:=prefixRun o m r s seed
  obtain ⟨v,group,vp,ev,mask,ground,nodes4⟩:=fused o m r u eu ip input
  obtain ⟨w,upper,wp,ew,_,ptr,known,gaps,frame⟩:=
    Upper.suffixChain o (Kernel.baseLeaf o m r) v ev vp mask nodes4 ground.gaps 20 le_rfl
  rw [schedule.1,schedule.2.1,schedule.2.2] at upper
  obtain ⟨t,finish,ipc,mode,zero,root,fr⟩:=R4.exit o w wp (ptr rfl) ew.root
  have run:=(((pre.trans group).trans upper).trans finish).finish
    (hasOp_sound (by decide : hasOp 262122 .ECALL) t ipc) mode zero
  have fit : 151001104+fusedSteps k+3497481+10+1≤2^40-16778266:=by cases k <;> decide
  have answer:=run (2^40-16778266) fit
  have price : 503322640+fusedCycles k+8390901+10+1=commitPrice k-58721306:=by cases k <;> decide
  rw [price] at answer
  refine ⟨t,?_,answer⟩
  have ext:=ground.kept (fun a n _ hi range=>frame a n hi range) gaps
  have atNode (h j : Nat) (lo : 4≤h) (hi : h≤24) (ok : j<levelCount h) :
      readBuffer w (nodeAddress h j) 32=node (tree o m r) h j :=
    (known h lo hi j ok).trans (fixed_tree_node_all o.compression m (pairSalts r) h j hi).symm
  have transfer (a n : Nat) (lo : tdAddress≤a) (hi : a+n≤7650414624) :
      slice (readBuffer t tdAddress 3355443200) a n=readBuffer w a n :=
    (sliceRead t a n lo hi).trans (fr.readBuffer_eq (by omega) (Or.inr lo))
  refine ⟨root.trans (atNode 24 0 (by decide) le_rfl (by decide)),?_,?_,?_,?_,?_,?_⟩
  · intro i;have b : i.val<16777216:=i.isLt
    apply (transfer _ _ ?_ ?_).trans (ext.rows i) <;> dsimp [finalRowAddress,rowBase,tdAddress] <;> omega
  · intro i;have b : i.val<16777216:=i.isLt
    apply (transfer _ _ ?_ ?_).trans (ext.salts i) <;> dsimp [sharedSaltAddr,rowBase,tdAddress] <;> omega
  · intro h lo hi j valid
    obtain ⟨b,end_⟩:=Upper.bounds h j lo hi valid
    exact (transfer _ _ (by dsimp [tdAddress];omega) (by omega)).trans (atNode h j lo hi valid)
  · intro h lo j valid;obtain ⟨b,end_⟩:=earlyRange h j lo valid
    exact (transfer _ _ b (by omega)).trans (ext.omitted h lo j valid)
  · intro h p k gap
    have bound:=padValid h p k gap
    exact (transfer _ _ (by dsimp [unusedSlotAddr,rowAddress,tdAddress];omega) (by change _≤5905584160 at bound;omega)).trans (ext.gaps h p k gap)
  · intro a lo hi region
    exact (transfer a 1 (by change 5368714368≤a at lo;dsimp [tdAddress];omega) (by dsimp [tdAddress] at hi;omega)).trans (ext.tail a ⟨lo,hi,region⟩)

end CommitGolfCandidate.RungA
