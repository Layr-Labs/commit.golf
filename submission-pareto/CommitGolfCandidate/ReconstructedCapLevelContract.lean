import CommitGolfCandidate.ReconstructedCapEvidence

namespace CommitGolfCandidate.Reconstruction.CapLevel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan
open CapSchedule (pending low headers rest)
set_option maxRecDepth 14000

def fields (tree : Encoding.Tree) (f : Nat→Bool) (d : Nat) :=
  (pending f d).flatMap (low tree d) ++ headers tree d (pending f d)

def cost (f : Nat→Bool) (d : Nat) := 14+18*pairs d+26+60*(pending f d).length+16+43*(pending f d).length

def Contract (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions) :=
  ∀ (f : Nat→Bool) (d : Nat), 0<d → d≤9 →
  ∀ (s : MachineState) (fs : List Wire.Field), HonestCapState.Matches ⟨d,.level⟩ s → CapGlobal.Common s trap ps →
  HonestSizeRows.Rows f d 0 s → CapEvidence.Buffer s fs →
  Wire.bits (fs++rest (LeafTree.tree o key msg) f d)+192<OpeningPut.capacity*64 →
  ∃ n t, n≤cost f d ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ HonestCapState.Matches ⟨d,.finish⟩ t ∧
    CapGlobal.Common t trap ps ∧ HonestSizeRows.Rows f d (pairs d) t ∧
    CapEvidence.Buffer t (fs++fields (LeafTree.tree o key msg) f d)

end CommitGolfCandidate.Reconstruction.CapLevel
