import CommitGolfCandidate.ReconstructedCapEvidence
import CommitGolfCandidate.ReconstructedHonestSizeAdvance
import CommitGolfCandidate.ReconstructedCapScanMemory

namespace CommitGolfCandidate.Reconstruction.HonestDepthPair
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapPlan HonestCapState HonestSizeSchedule HonestCapStages
open TwoPermutationPrototype.RV64
open HonestCapTables (w scratch)
open HonestCapOperands (children)
open HonestCapRam (activeBase)
open HonestFlagState (atByte code)
open HonestSizeRows (Rows inSpan)
open CommitBlocks (addr)
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

def ids (f : Nat→Bool) (d j : Nat) := CapOrder.ids (2^d) (row f (9-d)) 0 j

structure Data (f : Nat→Bool) (d j : Nat) (s : MachineState) (trap : CommitStorage.Trapdoor)
    (ps : Positions) (fs : List Wire.Field) : Prop where
  rows : Rows f d j s
  slots : CapSlots.Contains (memoryView s) (ids f d j)
  global : CapGlobal.Common s trap ps
  buffer : CapEvidence.Buffer s fs

structure Ptr (d j : Nat) (s : MachineState) : Prop where
  child : holds s (children (pairs d+j))
  parent : s.getReg .x24=w (activeBase+(pairs d+j))

theorem size (f : Nat→Bool) (d j : Nat) : prefixCount f d j≤j := tally_le _ _

private theorem scanned {d j p p' : Nat} {s : MachineState} (h : Matches ⟨d,.scanGuard j p⟩ s)
    (actual : s.getReg .x20=w p') : Matches ⟨d,.scanGuard j p'⟩ s := by
  refine ⟨h.atPc,h.base,?_⟩
  have f := h.fields
  simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at f ⊢
  exact ⟨f.1,actual,f.2.2⟩

theorem pair (o : Oracle) (f : Nat→Bool) (d j : Nat) (pos : 0<d) (small : d≤9) (active : j<pairs d)
    (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions) (fs : List Wire.Field)
    (start : Matches ⟨d,.scan j (prefixCount f d j)⟩ s) (ptr : Ptr d j s) (data : Data f d j s trap ps fs) :
    ∃ k t, k≤17 ∧ CommitExact.Segment o image k s t ∧ Matches ⟨d,.scanGuard (j+1) (prefixCount f d (j+1))⟩ t ∧
      Ptr d (j+1) t ∧ Data f d (j+1) t trap ps fs := by
  have width := width_bound d small
  have cnt := size f d j
  let p : Fin 257 := ⟨prefixCount f d j,by omega⟩
  let l := row f (9-d) (2*j)
  let r := row f (9-d) (2*j+1)
  have child := ptr.child
  simp only [children,holds_cons,holds_nil,and_true] at child
  have ctr := start.fields
  simp only [localFacts,scanFacts,holds_cons,holds_nil,and_true] at ctr
  have unit : s.getReg .x11=1 := start.base.2.2
  have scratchPtr : s.getReg .x9=w scratch := data.global.regs _ _ (by decide)
  have left : HonestRanges.Contains HonestCapSpan.flags (s.getReg .x23) := by
    rw [child.1];exact inSpan (by omega)
  have right : HonestRanges.Contains HonestCapSpan.flags (s.getReg .x16) := by
    rw [child.2];change HonestRanges.Contains HonestCapSpan.flags (w ((activeBase+2*(pairs d+j))+1))
    rw [Nat.add_assoc];exact inSpan (by omega)
  have parent : HonestRanges.Contains HonestCapSpan.flags (s.getReg .x24) := by
    rw [ptr.parent];exact inSpan (by omega)
  obtain ⟨k,fee,t,time,path,walk⟩ := HonestScanForward.run s true start.atPc p left right parent scratchPtr ctr.2.1
  have run : CommitExact.Segment o image k s t := ⟨fee,0,fun fuel => by rw [walk,bind_pure_comp,fixed_oracle_run_map]⟩
  have lo : s.getByte (s.getReg .x23)=code l := by
    rw [child.1];change atByte s (2*(pairs d+j))=_
    rw [show 2*(pairs d+j)=2*pairs d+2*j by omega];exact data.rows.child _ (by omega)
  have hi : s.getByte (s.getReg .x16)=code r := by
    rw [child.2];change atByte s (2*(pairs d+j)+1)=_
    rw [show 2*(pairs d+j)+1=2*pairs d+(2*j+1) by omega];exact data.rows.child _ (by omega)
  have regs := HonestScanBytes.execute s t true start.atPc path p l r lo hi unit ctr.2.1 scratchPtr
  have legal0 : legal ⟨d,.scan j p.val⟩ := ⟨⟨pos,small⟩,active,cnt⟩
  have newCtr : t.getReg .x20=w (prefixCount f d (j+1)) := regs.1
  obtain ⟨v,edge,matched⟩ := HonestCapScan.scan d j p.val s t true legal0 start path
  have next : Matches ⟨d,.scanGuard (j+1) (prefixCount f d (j+1))⟩ t := by
    simp only [HonestCapPlan.next,List.mem_cons,List.not_mem_nil,or_false] at edge
    rcases edge with rfl|rfl <;> exact scanned matched newCtr
  have pointers : Ptr d (j+1) t := by
    have i : pairs d+j<512 := by omega
    have ch := (applyTable (HonestCapOperands.children_next ⟨_,i⟩) start.atPc ptr.child path).2
    have par := (applyTable (HonestCapMetadata.pair_next ⟨_,i⟩) start.atPc
      (by simp only [holds_cons,holds_nil,and_true];exact ptr.parent) path).2
    refine ⟨?_,?_⟩
    · simpa only [Nat.add_assoc] using ch
    · simp only [holds_cons,holds_nil,and_true] at par
      simpa only [Nat.add_assoc] using par
  have index : s.getReg .x21=w (2^d+2*j) := by
    rw [ctr.2.2.1,(powers d pos).1];unfold scanIndex;congr 1;omega
  have effect := CapScanMemory.exact s t true start.atPc path p (2^d+2*j) l r lo hi unit ctr.2.1 scratchPtr index
  have inside : (s.getReg .x24).toNat<2^24 := by have mx := parent.2;change _≤4260863 at mx;omega
  have slots := CapScanMemory.ordered s t _ inside (row f (9-d)) (2^d) j p (CapOrder.prefix_length f d j) data.slots effect
  have same := CapFrame.scan s t _ parent p (2^d+2*j) l r effect
  have common := CapGlobal.transferred (.scan j p.val) s t trap ps data.global (by simp) (by simp) start.atPc path
    (fun q h c _ => same q h c)
  have cursor := HonestCapMetadata.frame 1470 17 (by decide) s t true start.atPc path .x7 (by decide)
  have buffer := CapEvidence.direct s t fs data.buffer cursor (fun k lim =>
    same (OpeningPut.base+k) (by unfold OpeningPut.base;unfold OpeningPut.capacity at lim;omega)
      (by unfold CapFrame.clear OpeningPut.base;unfold OpeningPut.capacity at lim;omega))
  refine ⟨k,t,time,run,next,pointers,⟨?_,slots,common,buffer⟩⟩
  apply HonestSizeRows.scanned_pair data.rows width active
  intro a small
  have delta := regs.2 _ (inSpan small)
  simp only [ptr.parent,HonestSizeRows.addr_eq small (show pairs d+j<1024 by omega)] at delta
  exact delta

end CommitGolfCandidate.Reconstruction.HonestDepthPair
