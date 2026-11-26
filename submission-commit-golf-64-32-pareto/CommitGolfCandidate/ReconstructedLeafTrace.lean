import CommitGolfCandidate.ReconstructedLeafCarry
import CommitGolfCandidate.ReconstructedLeafLatch

namespace CommitGolfCandidate.Reconstruction.LeafTrace
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open LeafCode LeafModel LeafMacros CommitWindows LeafSpill LeafContent LeafPrelude Generator LeafLane LeafSource
open LeafDigest LeafPreserve LeafCarry CommitBlocks CommitSetup

/-- Absolute instruction count at the beginning of a slot, including completed tile back edges. -/
def tick (i : Index) := 52997*(tileOf i).val+start (slot i)

structure AtLeaf (o : Oracle) (k : Key) (msg : Message) (i : Index) (s : MachineState) (m : Model) : Prop where
  fits : Fits s m
  pc : s.pc = addr (start (slot i))
  enter : Enter m i
  pre : Prefix o k msg i.val m.mem
  guard : Guard m i
  scratch : Scratch o k m i
  tiles : m.reg .x20 = BitVec.ofNat 64 (4096-(tileOf i).val)

theorem AtLeaf.ready {o k msg i s m} (h : AtLeaf o k msg i s m) : Ready o m k msg i :=
  ⟨h.enter,h.pre,guard_counter _ _ h.guard,h.scratch⟩

private theorem end_slot (i : Index) : start (slot i)+(body (slot i)).length =
    if slot i+1=4096 then 53012 else start (slot i+1) := by
  have q := body_verified ⟨slot i,by unfold slot; omega⟩
  change goodLane (slot i)=true at q
  simp only [goodLane,Bool.and_eq_true,decide_eq_true_eq] at q
  exact q.2

private theorem count_result (o : Oracle) (m : Model) (i : Index) : (result o m i).reg .x20 = m.reg .x20 := by
  rw [result_read _ _ _ _ (by decide) (by decide) (by decide) (by decide),
    staged_read _ _ _ _ (by decide) (by decide) (by decide) (by decide)]

private theorem count_lower (i : Index) : 19 ≤ tick i := by
  dsimp only [tick,start]
  omega

theorem next (o : Oracle) (k : Key) (msg : Message) (i j : Index) (succ : j.val=i.val+1)
    (s : MachineState) (m : Model) (h : AtLeaf o k msg i s m) :
    ∃ t n, CommitExact.Segment o im (tick j-tick i) s t ∧ AtLeaf o k msg j t n ∧ tick i ≤ tick j := by
  obtain ⟨u,trace,hu,loc⟩ := machine_lane o m i h.enter s h.fits h.pc
  have endAt := end_slot i
  have pre : Prefix o k msg j.val (result o m i).mem := succ ▸ advance o m k msg i h.ready
  have guard := next_guard o m k msg i j succ h.ready h.guard
  have scratch := next_scratch o m k msg i j h.ready succ
  have tileBound : (tileOf i).val < 4096 := (tileOf i).isLt
  have ilt : i.val<2^24 := i.isLt
  have jlt : j.val<2^24 := j.isLt
  by_cases last : slot i+1=4096
  · rw [if_pos last] at endAt loc
    have sj : slot j=0 := by unfold slot at *; omega
    have tj : (tileOf j).val=(tileOf i).val+1 := by change j.val/4096=i.val/4096+1; unfold slot at last; omega
    have live : LeafLatch.left i≠0 := by have := (tileOf j).isLt; unfold LeafLatch.left; omega
    have anchor := (result_read o m i .x19 (by decide) (by decide) (by decide) (by decide)).trans (center_staged _ _ _ h.enter)
    obtain ⟨v,done,hv,back⟩ := LeafLatch.run o _ i u loc hu anchor ((count_result ..).trans h.tiles)
    rw [if_neg live] at done back
    let n := LeafLatch.nextModel (result o m i) i
    have sz : tick j = tick i+(body (slot i)).length+4 := by
      unfold tick; rw [tj,sj,show start 0=19 by rfl]; omega
    refine ⟨v,n,?_,?_,by omega⟩
    · have steps := CommitExact.compose trace done
      rwa [show tick j-tick i=(body (slot i)).length+4 by omega]
    · refine ⟨hv,by simpa only [sj,show start 0=19 by rfl] using back,?_,pre,?_,?_,?_⟩
      · have fixed := result_fixed o m i h.enter.toFixed
        exact ⟨⟨fixed.mode,fixed.base,fixed.len,fixed.kind,fixed.ones⟩,
          (result_ptr ..).trans (continuity i j succ),congrArg wordAddress (anchor_tile i j succ last)⟩
      · exact guard
      · have first : (laneOf j).val=0 := by change slot j%12=0; rw [sj]
        exact ⟨fun nz => False.elim (nz first),fun nz => False.elim (nz first)⟩
      · change BitVec.ofNat 64 (LeafLatch.left i) = _
        apply congrArg (BitVec.ofNat 64); unfold LeafLatch.left; omega
  · rw [if_neg last] at endAt loc
    have slotLimit : slot i<4096 := Nat.mod_lt _ (by decide)
    have sj : slot j=slot i+1 := by unfold slot at *; omega
    have tj : (tileOf j).val=(tileOf i).val := by change j.val/4096=i.val/4096; unfold slot at sj; omega
    have sz : tick j = tick i+(body (slot i)).length := by unfold tick; rw [sj,tj,←endAt]; omega
    refine ⟨u,result o m i,?_,⟨hu,by rwa [sj],next_enter o m i j h.enter succ (by omega),pre,guard,scratch,?_⟩,by omega⟩
    · rwa [show tick j-tick i=(body (slot i)).length by omega]
    · rw [count_result,h.tiles,tj]

def startState (msg : Message) (r : BitVec 192) := CommitKey.tileStart (Artifact.submission.initialState .commit msg) r
def view (s : MachineState) : Model := ⟨s.getReg,memoryView s⟩

def first : Index := ⟨0,by decide⟩

theorem initial (o : Oracle) (msg : Message) (r : BitVec 192) :
    AtLeaf o (CommitKey.key r) msg first (startState msg r) (view (startState msg r)) := by
  let s := Artifact.submission.initialState .commit msg
  let d := CommitKey.afterDraw s r
  have loc : d.pc=addr 7 := by
    change (seedState s 6).pc+4=_
    rw [seed_syscall_pc]; rfl
  obtain ⟨mode,base,ptr,len,kind,ones,anchor,tiles⟩ := CommitTile.registers d (CommitKey.base s r)
  refine ⟨⟨fun _ => rfl,fun _ _ => rfl⟩,CommitTile.pc_before d loc 12 (by decide),
    ⟨⟨mode,base,len,kind,ones⟩,ptr,anchor⟩,LeafContent.initial o r msg,?_,?_,tiles⟩
  · intro h; exact False.elim ((by decide : ¬((laneOf first).val ≠ 0 ∨ (groupOf first).val%16≠0)) h)
  · exact ⟨fun h => False.elim (h rfl),fun h => False.elim (h rfl)⟩

theorem reach (o : Oracle) (msg : Message) (r : BitVec 192) (j : Index) :
    ∃ s m, CommitExact.Segment o im (tick j-19) (startState msg r) s ∧ AtLeaf o (CommitKey.key r) msg j s m := by
  have go (n : Nat) (hn : n<LENGTH) :
      let i : Index := ⟨n,hn⟩
      ∃ s m, CommitExact.Segment o im (tick i-19) (startState msg r) s ∧ AtLeaf o (CommitKey.key r) msg i s m := by
    induction n with
    | zero =>
      dsimp only
      rw [show (⟨0,hn⟩:Index)=first from rfl,show tick first-19=0 by decide]
      exact ⟨_,_,CommitExact.empty ..,initial o msg r⟩
    | succ n ih =>
      let i : Index := ⟨n,by omega⟩
      let j : Index := ⟨n+1,hn⟩
      obtain ⟨s,m,run,h⟩ := ih (by omega)
      obtain ⟨t,m',step,post,mon⟩ := next o (CommitKey.key r) msg i j rfl s m h
      refine ⟨t,m',?_,post⟩
      have budget : tick j-19=tick i-19+(tick j-tick i) := by have := count_lower i; omega
      rw [budget]; exact CommitExact.compose run step
  exact go j.val j.isLt

end CommitGolfCandidate.Reconstruction.LeafTrace
