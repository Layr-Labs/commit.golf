import CommitGolfCandidate.ReconstructedCheckCapScanPair
import CommitGolfCandidate.ReconstructedCheckCapScanOrder
import CommitGolfCandidate.ReconstructedHonestDepthPair

namespace CommitGolfCandidate.Reconstruction.CheckCapScanLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks
open HonestCapPlan (pairs)
open HonestSizeSchedule (prefixCount row)
open HonestSizeRows (Rows)
open CheckCapScanData (W scratch flag Frame)
open TwoPermutationPrototype.RV64 (memoryView)
set_option maxRecDepth 13000
set_option maxHeartbeats 1400000

def here (d j : Nat) := if j<pairs d then 447 else 460
def index (d j : Nat) := 2^d+2*j
def ids (f : Nat→Bool) (d j : Nat) := CapOrder.ids (2^d) (row f (9-d)) 0 j

structure Inv (f : Nat→Bool) (d j : Nat) (s : MachineState) : Prop where
  pc : s.pc=addr (here d j)
  indexPtr : s.getReg .x16=W (index d j)
  count : s.getReg .x12=W (prefixCount f d j)
  left : s.getReg .x14=flag (index d j)
  right : s.getReg .x13=flag (index d j+1)
  parent : s.getReg .x15=flag (pairs d+j)
  top : s.getReg .x20=W (2^(d+1))
  unit : s.getReg .x18=1
  scratchPtr : s.getReg .x29=W scratch
  rows : Rows f d j s
  slots : CheckCapSlots.Contains (memoryView s) scratch (ids f d j)

theorem next (o : Oracle) (f : Nat→Bool) (d j : Nat) (pos : 0<d) (narrow : pairs d≤256)
    (more : j<pairs d) (s : MachineState) (old : Inv f d j s) :
    ∃ n≤18,∃ t,Segment o n s t [] ∧ Inv f d (j+1) t ∧ Frame s t ∧
      ∀ q∉CheckCapScanPair.changed,t.getReg q=s.getReg q := by
  let k:=index d j
  let p:=prefixCount f d j
  let dd:=pairs d+j
  let h:=2^(d+1)
  let l:=row f (9-d) (2*j)
  let r:=row f (9-d) (2*j+1)
  obtain ⟨width,upper⟩:=HonestCapState.powers d pos
  have kdef : k=2*pairs d+2*j:=by simp only [k,index,width]
  have psmall : p≤256 := (HonestDepthPair.size f d j).trans (by omega)
  have dsmall : dd<1024:=by unfold dd;omega
  have lval : s.getByte (flag k)=HonestFlagState.code l := by
    rw [kdef];exact old.rows.child _ (by omega)
  have rval : s.getByte (flag (k+1))=HonestFlagState.code r := by
    rw [kdef,show 2*pairs d+2*j+1=2*pairs d+(2*j+1) by omega];exact old.rows.child _ (by omega)
  have read : CheckCapScanPair.Before s k p h dd l r :=
    ⟨by simpa only [here,ite_eq_left more] using old.pc,old.left,old.right,old.parent,old.indexPtr,
      old.count,old.top,old.scratchPtr,old.unit,lval,rval⟩
  obtain ⟨n,time,t,segment,out⟩:=CheckCapScanPair.run o s k p h dd l r read (by omega) psmall
    (by dsimp [h];omega) dsmall
  have num : k+2=index d (j+1):=by unfold k index;omega
  have parent : dd+1=pairs d+(j+1):=by unfold dd;omega
  have cond : k+2<h ↔ j+1<pairs d := by dsimp [h];omega
  have dst : CheckCapScanAdvance.dest k h=here d (j+1) := by simp only [CheckCapScanAdvance.dest,here,cond]
  have rows : Rows f d (j+1) t := HonestSizeRows.scanned_pair old.rows narrow more (by
    intro v hv
    rw [←CheckCapScanData.flag_effect s p k dd l r dsmall (by omega) v hv]
    apply congrArg (fun m : Word→Word => extractByte (m (alignToDword (flag v))) (byteOffset (flag v))) out.mem)
  have slots:=CheckCapScanData.ordered s t dd dsmall (row f (9-d)) (2^d) j
    (⟨p,by omega⟩ : Fin 257) (CapOrder.prefix_length f d j) old.slots out.mem
  refine ⟨n,time,t,segment,⟨out.pc.trans (congrArg addr dst),?_,out.pending,?_,?_,?_,
    (out.keep _ (by decide)).trans old.top,(out.keep _ (by decide)).trans old.unit,
    (out.keep _ (by decide)).trans old.scratchPtr,rows,slots⟩,?_,out.keep⟩
  · rw [←num];exact out.index
  · rw [←num];exact out.lo
  · rw [←num];exact out.hiPtr
  · rw [←parent];exact out.parent
  · intro a af as
    exact (congrFun out.mem a).trans (CheckCapScanData.frame s p k dd l r dsmall (by omega) a af as)

theorem through (o : Oracle) (f : Nat→Bool) (d : Nat) (pos : 0<d) (bound : pairs d≤256)
    (s : MachineState) (init : Inv f d 0 s) (j : Nat) (legal : j≤pairs d) :
    ∃ n≤18*j,∃ t, Segment o n s t [] ∧ Inv f d j t ∧ Frame s t ∧
      ∀ q∉CheckCapScanPair.changed,t.getReg q=s.getReg q := by
  induction j with
  | zero=>exact ⟨0,by omega,s,CheckRecorded.empty _ _,init,CheckCapScanData.refl s,fun _ _=>rfl⟩
  | succ j ih=>
    obtain ⟨n,time,u,pre,stage,fr,rg⟩:=ih (by omega)
    obtain ⟨m,more,t,one,done,fr',rg'⟩:=next o f d j pos bound (by omega) u stage
    exact ⟨n+m,by omega,t,compose pre one,done,CheckCapScanData.trans fr fr',fun v hv=>(rg' v hv).trans (rg v hv)⟩

end CommitGolfCandidate.Reconstruction.CheckCapScanLoop
