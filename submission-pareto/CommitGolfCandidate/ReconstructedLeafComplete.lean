import CommitGolfCandidate.ReconstructedLeafTrace

namespace CommitGolfCandidate.Reconstruction.LeafTrace
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafModel LeafContent LeafLane LeafPrelude LeafPreserve Generator CommitBlocks CommitSetup

set_option maxRecDepth 8192
set_option maxHeartbeats 1400000

def lastIndex : Index := ⟨16777215,by decide⟩

private theorem lastSlot : slot lastIndex+1=4096 := by decide +kernel
private theorem lastLeft : LeafLatch.left lastIndex=0 := by decide +kernel
private theorem lastLength : tick lastIndex-19 + (LeafCode.body (slot lastIndex)).length + 3 = 217075711 := by decide +kernel
private theorem lastCount : lastIndex.val+1 = LENGTH := by decide +kernel

/-- The actual commitment executes all 16,777,216 pinned leaves from the sampled key,
and enters the parent loop with every leaf, parent work area and key word accounted for. -/
theorem leaves (o : Oracle) (msg : Message) (r : BitVec 192) :
    ∃ s m, CommitExact.Segment o im 217075711 (startState msg r) s ∧ Fits s m ∧
      s.pc=addr 53016 ∧ s.getReg .x5=0 ∧ s.getReg .x20=0 ∧
      Prefix o (CommitKey.key r) msg LENGTH m.mem := by
  let i := lastIndex
  obtain ⟨s,m,history,h⟩ := reach o msg r i
  obtain ⟨u,one,hu,pc⟩ := machine_lane o m i h.enter s h.fits h.pc
  have tail : slot i+1=4096 := lastSlot
  have pcu : u.pc=addr 53012 := by rwa [if_pos tail] at pc
  have centerReg := (result_read o m i .x19 (by decide) (by decide) (by decide) (by decide)).trans (center_staged _ _ _ h.enter)
  have remaining : (result o m i).reg .x20 = BitVec.ofNat 64 (4096-(tileOf i).val) := by
    rw [result_read _ _ _ _ (by decide) (by decide) (by decide) (by decide),
      staged_read _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact h.tiles
  obtain ⟨v,latch,hv,loc⟩ := LeafLatch.run o _ i u pcu hu centerReg remaining
  have endOfTile : LeafLatch.left i=0 := lastLeft
  rw [if_pos endOfTile] at latch loc
  have full := CommitExact.compose (CommitExact.compose history one) latch
  have exactLength : tick i-19 + (LeafCode.body (slot i)).length + 3 = 217075711 := lastLength
  rw [exactLength] at full
  have guard := advance o m (CommitKey.key r) msg i h.ready
  rw [show i.val+1=LENGTH from lastCount] at guard
  refine ⟨v,LeafLatch.nextModel (result o m i) i,full,hv,loc,(hv.registers _).trans ?_,(hv.registers _).trans ?_,guard⟩
  · rw [LeafLatch.next_reg _ _ _ (by decide) (by decide)]
    exact (result_fixed _ _ _ h.enter.toFixed).mode
  · change BitVec.ofNat 64 (LeafLatch.left i)=0; rw [endOfTile]; rfl

end CommitGolfCandidate.Reconstruction.LeafTrace
