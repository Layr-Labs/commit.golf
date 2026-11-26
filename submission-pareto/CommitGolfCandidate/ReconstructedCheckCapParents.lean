import CommitGolfCandidate.ReconstructedCheckParentLoop
import CommitGolfCandidate.ReconstructedCheckParentExit

namespace CommitGolfCandidate.Reconstruction.CheckCapParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix Binding CheckParentHeap CheckParentControl
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] CheckParent.Cost CheckParentLoop.log

def rows (o : Oracle) (d : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) :=
  CheckParentLoop.log o (d-1) (2^(d-1)) (2^(d-1)) active child

structure Input (s : MachineState) (d : Nat) (cursor : Word) : Prop where
  pc : s.pc=addr 598
  depth : s.getReg .x9=W d
  parent : s.getReg .x10=W (2^(d-1))
  child : s.getReg .x11=W (2^d)
  active : s.getReg .x19=CheckCapScanData.flag (2^(d-1))
  limit : s.getReg .x20=W (2^(d+1))
  head : s.getReg .x25=W (2^d)
  static : Context s cursor

structure Post (o : Oracle) (s t : MachineState) (d : Nat) (cursor : Word) (active : Nat→Bool) (child : Nat→Binding.Digest) : Prop where
  ready : CheckParentExit.Ready t (d-1) cursor
  kept : ∀ r∈CheckParentStep.preserve,t.getReg r=s.getReg r
  frame : Frame (2^(d-1)) (2^d) s t
  stored : CheckParentLoop.Stored o (d-1) active child (2^(d-1)) (2^d) s t
  canonical : ∀ p,2^(d-1)≤p→p<2^d→active p=true→Canonical (d-1) (CommitParents.cell t (base p))
  edges : ∀ p,2^(d-1)≤p→p<2^d→active p=true→∀ side : Bool,
    Nonempty (CheckPath.Edge o (rows o d active child) (d-1) side (child (2*p+side.toNat)) (CommitParents.cell t (base p)))

/-- Run every physical cap parent in ascending order. The ordered oracle rows certify an
edge for each active child. Inactive cells, stream, flags, and caller-owned RAM keep their values. -/
theorem run (o : Oracle) (d : Nat) (pos : 0<d) (small : d≤9) (active : Nat→Bool) (child : Nat→Binding.Digest)
    (s : MachineState) (c : Word) (input : Input s d c) (table : CheckParentGeometry.constants s)
    (flags : CheckParentLoop.flags s active (2^(d-1)) (2^d))
    (kids : CheckParentLoop.children s child active (2^(d-1)) (2^d))
    (can : ∀ p,2^(d-1)≤p→p<2^d→active p=true→Canonical d (child (2*p)) ∧ Canonical d (child (2*p+1))) :
    ∃ n t,n≤10+194*2^(d-1) ∧ Segment o n s t (rows o d active child) ∧ Post o s t d c active child := by
  let e : Fin 24:=⟨d-1,by omega⟩
  let k:=2^(d-1)
  have kd : 2^d=2*k:=by dsimp [k];rw [show d=(d-1)+1 by omega] at ⊢;simp only [pow_succ,Nat.add_sub_cancel];omega
  have top : 2^(d+1)=4*k:=by rw [pow_succ,kd];omega
  have bound : k≤256:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : d-1≤8)
  have eq : e.val+1=d:=by dsimp [e];omega
  obtain ⟨u,entry,up,ul,uc,um,ku⟩:=enter o s e.val k c input.pc (Nat.two_pow_pos _) bound (eq ▸ input.depth)
    input.parent (kd ▸ input.child) input.active (top ▸ input.limit) (kd ▸ input.head) input.static
  have uf : CheckParentLoop.flags u active k (2*k) := by
    rw [←kd];intro p lo hi
    exact (CheckCapScanFlags.copiedByte s u um _).trans (flags p lo hi)
  have uk : CheckParentLoop.children u child active k (2*k) := by
    rw [←kd];intro p lo hi on;have old:=kids p lo hi on
    exact ⟨(CommitParents.cell_congr um _).trans old.1,(CommitParents.cell_congr um _).trans old.2⟩
  have site : u.pc=addr (here k (2*k)):=by rw [here,ite_eq_left (by have := Nat.two_pow_pos (d-1);change 0<k at this;omega : k<2*k)];exact up
  obtain ⟨n,v,cost,body,atEnd,vl,vc,fr,stored,kv⟩:=CheckParentLoop.run o e k k k bound le_rfl (by omega) active child u c
    site ul uc uf (fun p w al known=>(congrFun um p).trans (table p w al known)) uk
  obtain ⟨t,out,ready,tm,kt⟩:=CheckParentExit.run o v e.val c atEnd vl.depth (by dsimp [e];omega) vc
  have joined : CheckParentLoop.Stored o (d-1) active child k (2^d) s t:=by
    rw [kd];intro p lo hi
    have hs:=stored p lo hi
    exact ⟨fun on=>(CommitParents.cell_congr tm _).trans (hs.1 on),fun off i=>(congrFun tm _).trans ((hs.2 off i).trans (congrFun um _))⟩
  refine ⟨7+n+3,t,?_,by simpa only [rows,List.nil_append,List.append_nil] using compose (compose entry body) out,
    ⟨ready,?_,?_,joined,?_,?_⟩⟩
  · have limit : CheckParent.Cost e≤170:=by unfold CheckParent.Cost;exact (CheckParentPlan.checked e).2
    have lim:=Nat.mul_le_mul_right k (by omega : 24+CheckParent.Cost e≤194);change 7+n+3≤10+194*k;omega
  · intro r h
    have safe : r∉[Reg.x18,.x22] ∧ r∉[Reg.x9,.x10,.x11,.x18,.x22] := by
      cases r <;> first | decide | simp [CheckParentStep.preserve] at h
    exact (kt r safe.1).trans ((kv r h).trans (ku r safe.2))
  · rw [kd];intro w wb away st dst;exact (congrFun tm _).trans ((fr w wb away st dst).trans (congrFun um _))
  · intro p lo hi on
    rw [(joined p lo hi).1 on]
    exact canonical_project (d-1) _
  · intro p lo hi on side
    obtain ⟨canonL,canonR⟩:=can p lo hi on
    have cert:=CheckParentLoop.observed o (d-1) k k p active child lo (by rw [kd] at hi;omega) on
    rw [←eq] at canonL canonR
    refine ⟨⟨child (2*p),child (2*p+1),canonL,canonR,?_,((joined p lo hi).1 on).symm,cert⟩⟩
    cases side <;> simp

theorem query_bound (o : Oracle) (d : Nat) (active : Nat→Bool) (child : Nat→Binding.Digest) :
    (rows o d active child).length≤2^(d-1)*work (d-1) := CheckParentLoop.length .. 

end CommitGolfCandidate.Reconstruction.CheckCapParents

