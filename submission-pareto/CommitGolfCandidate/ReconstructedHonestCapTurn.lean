import CommitGolfCandidate.ReconstructedCapLevelContract
import CommitGolfCandidate.ReconstructedHonestCapGroups

namespace CommitGolfCandidate.Reconstruction.HonestCapTurn
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestCapStages
open TwoPermutationPrototype.RV64
open HonestSizeRows (Rows)
open HonestCapTables (w)
open CommitBlocks (addr)
attribute [local irreducible] ArtifactEncoding.decode execute
set_option maxRecDepth 16384

theorem entry (o : Oracle) (s : MachineState) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (fs : List Wire.Field) (ready : CapEntry.Ready s trap ps fs) :
    ∃ n t, n≤19 ∧ CommitExact.Segment o image n s t ∧ Matches ⟨9,.level⟩ t ∧ CapGlobal.Common t trap ps ∧
      Rows (CapEntry.flags ps) 9 0 t ∧ CapEvidence.Buffer t fs := by
  have start : Matches ⟨9,.enter⟩ s := ⟨ready.location,ready.frame,holds_nil _⟩
  obtain ⟨n,t,bound,path,run⟩ := CapControlForward.forward o s 1429 19 [] (CapControlForward.arithmetic _ _ (by decide))
    ready.location (holds_nil _)
  obtain ⟨v,member,atLevel⟩ := HonestCapScan.enter 9 s t true (by simp [legal,allowed]) start path
  simp only [next,List.mem_singleton] at member;subst v
  have mem := CapControlMemory.actual 1429 19 (by decide) s t true ready.location path
  have metadata := HonestCapMetadata.frame 1429 19 (by decide) s t true ready.location path
  have src := CapFrame.transfer s t trap ps ready.toSource (metadata .x2 (by decide))
    (atLevel.base.1.trans ready.frame.symm) (CapFrame.stored s t mem)
  have regs := (applyTable CapGlobal.init_table ready.location
    (by simp only [holds_cons,holds_nil,and_true];exact ⟨rfl,ready.frame⟩) path).2
  have rows : Rows (CapEntry.flags ps) 9 0 s := HonestSizeRows.init ready.occupancy (by simp)
  exact ⟨n,t,bound,run,atLevel,⟨src,regs⟩,
    CapEvidence.rows_of_outside s t _ 9 0 (by decide) rows (fun q _ _ => CapScanMemory.read_congr mem q),
    CapEvidence.direct s t fs ⟨ready.cursor,ready.output⟩ (metadata .x7 (by decide)) (fun q _ => CapScanMemory.read_congr mem _)⟩

theorem next_level (o : Oracle) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9) (s : MachineState)
    (trap : CommitStorage.Trapdoor) (ps : Positions) (fs : List Wire.Field)
    (known : Matches ⟨d,.finish⟩ s) (common : CapGlobal.Common s trap ps) (rows : Rows f d (pairs d) s)
    (buf : CapEvidence.Buffer s fs) :
    ∃ n t, n≤2 ∧ CommitExact.Segment o image n s t ∧
      Matches (if d=1 then ⟨0,.returned⟩ else ⟨d-1,.level⟩) t ∧ CapGlobal.Common t trap ps ∧
      Rows f d (pairs d) t ∧ CapEvidence.Buffer t fs := by
  obtain ⟨n,t,bound,path,run⟩ := CapControlForward.forward o s 1449 2 [] (CapControlForward.arithmetic _ _ (by decide))
    known.atPc (holds_nil _)
  have ok : legal ⟨d,.finish⟩ := ⟨⟨pos,small⟩,trivial⟩
  obtain ⟨v,edge,matchT⟩ := HonestCapGroups.finish d s t true ok known path
  simp only [next,List.mem_singleton] at edge;subst v
  have mem := CapControlMemory.actual 1449 2 (by decide) s t true known.atPc path
  have cursor := HonestCapMetadata.frame 1449 2 (by decide) s t true known.atPc path .x7 (by decide)
  exact ⟨n,t,bound,run,matchT,
    CapGlobal.transferred .finish s t trap ps common (by simp) (by simp) known.atPc path (CapFrame.stored s t mem),
    CapEvidence.rows_of_outside s t f d (pairs d) (width_bound d small) rows (fun q _ _ => CapScanMemory.read_congr mem q),
    CapEvidence.direct s t fs buf cursor (fun q _ => CapScanMemory.read_congr mem _)⟩

end CommitGolfCandidate.Reconstruction.HonestCapTurn
