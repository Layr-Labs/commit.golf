import CommitGolfCandidate.ReconstructedCheckCapLevelNodes
import CommitGolfCandidate.ReconstructedCheckCapQuery

namespace CommitGolfCandidate.Reconstruction.CheckCapLevel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CommitBlocks
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open HonestCapPlan (pairs)
set_option maxRecDepth 18500
set_option maxHeartbeats 1600000

private theorem cursorBound (f : Nat→Bool) (d c stream : Nat) (m : Memory) (pos : 0<d) (max : d≤9)
    (good : (parsed f d stream c m).valid=true) : (parsed f d stream c m).cursor≤c+70000 := by
  let w:=Encoding.lows d
  let ids:=CapSchedule.pending f d
  let low:=CheckCapLowMemory.fill stream w ids c m
  have span:=CheckCapLevelRead.load_bound f d max w (CheckCapRepair.width d pos max)
  have off:=CheckCapHeaders.cursor d low ids stream (c+w*ids.length) good
  change (CheckCapHeaders.result d low ids stream (c+w*ids.length)).cursor≤_
  rw [off];dsimp only [ids] at *;split <;> omega

private theorem boundary (o : Oracle) (f : Nat→Bool) (stream d c : Nat) (s u t : MachineState) (m : Memory)
    (pos : 0<d) (max : d≤9) (read : CheckCapLevelRead.Post f stream d c s u m)
    (post : CheckCapParents.Post o u t d (CheckCapScanData.W (parsed f d stream c m).cursor) (CheckCapMembership.used f d)
       (view (parsed f d stream c m).data)) :
    Boundary f stream (d-1) (parsed f d stream c m).cursor t := by
  have hi : 2^d≤1024:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : d≤10)
  have fr:=CheckCapFrames.parent (pairs d) (2^d) hi post.frame
  have rg:=post.kept
  refine ⟨post.ready,(rg _ (by decide)).trans read.radix,(rg _ (by decide)).trans read.magic,
    (rg _ (by decide)).trans read.proof,CheckCapFrames.data fr read.table,?_,?_⟩
  · intro nextPos
    have transported:=HonestSizeRows.carry read.rows (show pairs d≤256 from
      Nat.pow_le_pow_right (by decide : 0<2) (by omega : d-1≤8)) (fun k hk=>CheckCapFrames.parent_flag hi post.frame k hk)
    exact HonestSizeRows.descend transported (by omega) max
  · intro p lo high active
    have dst : d-1+1=d:=by omega
    rw [dst] at high
    exact post.canonical p lo high ((CheckCapLevelNodes.used_parent f d p pos max) ▸ active)

/-- Positive execution of one complete shared-cap level in the pinned checker, together with
the canonical values or rejection it actually observed and its exact active-parent query count. -/
theorem run (o : Oracle) (f : Nat→Bool) (stream : Nat) : Contract o f stream := by
  intro d c s pos max room old
  obtain ⟨k,u,m,time,read,st⟩:=CheckCapLevelRead.run o f stream d c s pos max room old
  let out:=parsed f d stream c m
  let children:=view out.data
  let active:=CheckCapMembership.used f d
  let log:=CheckCapParents.rows o d active children
  cases valid : out.valid with
  | false=>
    have pc : u.pc=addr 672:=by have h:=st.pc;change u.pc=addr (if out.valid then 598 else 672) at h;rw [valid] at h;exact h
    exact ⟨k,u,[],m,by change k≤56+322*pairs d;omega,Nat.zero_le _,read,st.frame,st.base,Or.inl ⟨valid,⟨pc,st.static.sp,st.static.fp⟩⟩⟩
  | true=>
    have pc : u.pc=addr 598:=by have h:=st.pc;change u.pc=addr (if out.valid then 598 else 672) at h;rw [valid] at h;exact h
    have input : CheckCapParents.Input u d (CheckCapScanData.W out.cursor):=
      ⟨pc,st.depth,st.firstParent,st.firstChild,st.marks,st.limit,st.head,st.static⟩
    have sm : 2^(d+1)≤1024:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : d+1≤10)
    have kids : CheckParentLoop.children u children active (pairs d) (2^d):=by
      intro p lo hi on
      have l:=(CheckCapLevelNodes.bounds d p pos lo hi false).2.trans_le sm
      have r:=(CheckCapLevelNodes.bounds d p pos lo hi true).2.trans_le sm
      exact ⟨st.cells (2*p) l,st.cells (2*p+1) r⟩
    have canon (p : Nat) (lo : pairs d≤p) (hi : p<2^d) (on : active p=true) :
        Canonical d (children (2*p)) ∧ Canonical d (children (2*p+1)) :=
      ⟨CheckCapLevelNodes.source o f d stream c p s u m pos max lo hi false old st valid on,
       CheckCapLevelNodes.source o f d stream c p s u m pos max lo hi true old st valid on⟩
    obtain ⟨n,t,bound,body,post⟩:=CheckCapParents.run o d pos max active children u _ input st.table.constants
      (CheckCapLevelNodes.flags f d u pos max st.rows) kids canon
    have hiD : 2^d≤1024:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : d≤10)
    have outer:=CheckCapFrames.trans st.frame (CheckCapFrames.parent (pairs d) (2^d) hiD post.frame)
    refine ⟨k+n,t,log,m,by change n≤10+194*pairs d at bound;change k+n≤56+322*pairs d;omega,
      (CheckCapQuery.level o f d pos max children).le,compose read body,outer,st.base,Or.inr ⟨valid,
      boundary o f stream d c s u t m pos max st post,cursorBound f d c stream m pos max valid,?_,?_⟩⟩
    · intro p lo hi yes;exact (post.stored p lo hi).1 yes
    · intro p lo hi side live
      have on:=(CheckCapLevelNodes.known f d p pos lo hi side live).1
      have eq:=CheckCapLevelNodes.unchanged f d stream c p s u m side pos max lo hi st live
      have edge:=post.edges p lo hi on side
      change Nonempty (CheckPath.Edge o log (d-1) side (children (2*p+side.toNat)) (node t p)) at edge
      change children (2*p+side.toNat)=node s (2*p+side.toNat) at eq
      rwa [eq] at edge

end CommitGolfCandidate.Reconstruction.CheckCapLevel
