import CommitGolfCandidate.S5CheckPeers
import CommitGolfCandidate.S5CheckRowHash
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
structure PathRegs (s : MachineState) : Prop where
  radix : s.getReg .x3=3
  row : s.getReg .x25=W rowBuf
  chain : s.getReg .x26=W chainBuf
  digest : s.getReg .x27=W digestBuf
theorem PathRegs.kept {s t} (g : PathRegs s) (keep : RowKeeps s t) : PathRegs t:=
  ⟨(keep _ (by decide)).trans g.radix,(keep _ (by decide)).trans g.row,(keep _ (by decide)).trans g.chain,(keep _ (by decide)).trans g.digest⟩
def pathValue (H : Compression) (b : Bool) (x : CheckInput) (r d : Nat) :=
  S5.Auth.recordAt H (view b x) r d ((view b x).peers r)
def positionAt (x : CheckInput) (r d : Nat) := S4.nodeIndex (S5.recordIndex x.positions r).val d

structure AtHeight (o : Oracle) (b : Bool) (x : CheckInput) (r d : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcAt (rowPC b d)
  index : s.getReg .x14=W (positionAt x r d)
  digest : readBuffer s digestBuf 32=pathValue o.compression b x r d
  stream : WireCursor b x s (peerBit r d) (peerOffset r d)
  fixed : PathRegs s
  inputs : HighInput x s
private theorem row_live (q : Reg) (h : q∈rowRegs) : callKeep q:=by cases q <;> simp_all [rowRegs,callKeep,parentLive]
set_option maxRecDepth 12000 in
theorem path_step (o : Oracle) (x : CheckInput) (r : Nat) (p : RowSite) (s : MachineState) (size : InputSize x p r)
    (old : AtHeight o p.batch x r p.height.val s) :
    ∃ t n,n≤layerFuel p.batch p.height.val ∧ Flow o s t n (levelCalls p.height.val) ∧
      AtHeight o p.batch x r (p.height.val+1) t ∧ RowKeeps s t ∧ RowFrame s t := by
  let j:=positionAt x r p.height.val
  let v:=pathValue o.compression p.batch x r p.height.val
  have indexBound : j<2^64:=by
    have h:=(S5.recordIndex x.positions r).isLt;change (S5.recordIndex x.positions r).val<16777216 at h
    change (S5.recordIndex x.positions r).val/S4.span p.height.val<2^64;have lim:=Nat.div_le_self (S5.recordIndex x.positions r).val (S4.span p.height.val);omega
  obtain ⟨u,put⟩:=place_digest o s p j v size.allowed indexBound old.pc old.index old.fixed.radix old.fixed.row old.fixed.digest old.digest
  obtain ⟨z,a,room,filled⟩:=assemble o x s u p j r v size put old.inputs old.stream old.fixed.radix old.fixed.row
  have fixed:=old.fixed.kept filled.keep
  obtain ⟨t,b,bound,hash,pc,keep,frame,data⟩:=row_hash o z p j v _ size.allowed filled.pc fixed.row fixed.chain fixed.digest filled.cells
  have allRegs:=filled.keep.trans (fun q h=>keep q (row_live q h))
  have allFrame:=filled.frame.trans frame
  refine ⟨t,a+b,?_,by simpa only [Nat.zero_add] using filled.run.trans hash,⟨pc,?_,?_,?_,old.fixed.kept allRegs,old.inputs.after allFrame (by decide)⟩,allRegs,allFrame⟩
  · change a≤24+(p.radix-1)*(p.peerOps.length+_) at room
    rw [(rowNumbers p).2.2.2.1] at room
    change a+b≤24+(p.radix-1)*_+6+parentFuel p.height.val;omega
  · apply (keep .x14 (by simp [callKeep,parentLive])).trans;apply filled.parent.trans;apply congrArg W;exact (S4.nextIndex ..).symm
  · apply data.trans;dsimp only [j,v,positionAt,pathValue,S5.Auth.recordAt];rw [S5.Auth.walk,(view_indices x p.batch).1]
  · apply filled.cursor.frame frame (by decide) (by decide) (by decide)
    all_goals apply keep <;> simp [callKeep,parentLive]

theorem path_segment (o : Oracle) (b : Bool) (x : CheckInput) (r d n : Nat) (s : MachineState)
    (hr : r<x.positions.card) (mode : b=decide (x.positions.card=BATCH)) (limit : d+n≤pathDepth b)
    (old : AtHeight o b x r d s) :
    ∃ t steps,steps≤pathFuel b d n ∧ Flow o s t steps (pathCalls d n) ∧ AtHeight o b x r (d+n) t ∧
      RowKeeps s t ∧ RowFrame s t := by
  induction n generalizing s d with
  | zero=>exact ⟨s,0,le_rfl,Flow.refl _ _,old,RowKeeps.refl _,RowFrame.refl _⟩
  | succ n ih=>
    have depths : pathDepth b≤24:=by cases b <;> decide
    let p : RowSite:=⟨b,⟨d,by omega⟩⟩
    have valid : p.allowed=true:=by cases b <;> simp only [p,RowSite.allowed,Bool.not_false,Bool.not_true,Bool.true_or,Bool.false_or] <;>
      change _≤15 at limit <;> exact decide_eq_true (by omega)
    obtain ⟨u,a,ale,first,mid,keep,frame⟩:=path_step o x r p s ⟨hr,mode,valid⟩ old
    obtain ⟨t,k,kle,tail,last,kept,preserved⟩:=ih (s:=u) (d:=d+1) (by omega) mid
    have joined:=first.trans tail
    refine ⟨t,a+k,?_,?_,?_,keep.trans kept,frame.trans preserved⟩
    · change a≤layerFuel b d at ale;simpa only [pathFuel,List.range'_succ,List.map_cons,List.sum_cons] using Nat.add_le_add ale kle
    · simpa only [pathCalls,List.range'_succ,List.map_cons,List.sum_cons,p] using joined
    · simpa only [Nat.add_assoc,Nat.add_comm 1 n] using last
end CommitGolfCandidate.S5Machine.Check
