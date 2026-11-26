import CommitGolfCandidate.ReconstructedHonestSortedTraversal
import CommitGolfCandidate.ReconstructedHonestCapObserve

namespace CommitGolfCandidate.Reconstruction.HonestSegmentFlags
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestSortedTraversal HonestObserve
open HonestCapState (image)
open CommitBlocks (addr)

attribute [local irreducible] ArtifactEncoding.decode execute
set_option maxRecDepth 16384

def Goal (ps : Positions) (s : MachineState) :=
  HonestProtected.Holds HonestWideMemory.context HonestWideMemory.finish s ∧ indices ps s ∧
  HonestSortedFlags.current (Frontier.flags (ps.sort (·≤·))) s

theorem observed (ps : Positions) (i : Nat) (hi : i<ps.card) (s : MachineState)
    (ready : HonestAllRecords.Ready ps.card i s) (seen : Seen ps i s) : At image s (addr 1429) (Goal ps) := by
  suffices all : ∀ n i, ps.card-i=n → i<ps.card → ∀ s, HonestAllRecords.Ready ps.card i s → Seen ps i s →
      At image s (addr 1429) (Goal ps) from all _ i rfl hi s ready seen
  intro n
  induction n with
  | zero => intro i h hi;omega
  | succ n ih =>
    intro i h hi s ready seen
    refine cuts image s HonestRecordCost.cut (addr 1429) (Goal ps) (by decide) ?_ ?_
    · intro eq
      exact False.elim ((by decide : addr 143≠addr 1429) (ready.pc.symm.trans eq))
    · intro t path
      obtain ⟨next,seen'⟩ := one ps i hi s t ready seen path
      by_cases more : i+1<ps.card
      · rw [ite_eq_left more] at next; exact ih (i+1) (by omega) more t next seen'
      · rw [ite_eq_right more] at next
        rw [show i+1=ps.card by omega] at seen'
        intro f r hr live hit
        rw [HonestCapObserve.only t next.1 next.2 f r hr live hit]
        exact ⟨next.2,HonestSortedTraversal.finish ps t seen'⟩

/-- The fixed-oracle record executor may provide a single composed positive
segment from the first record. The final physical cap flags and preserved sorted
indices follow directly at its endpoint, for every opening cardinality. -/
theorem from_first (o : Oracle) (trap : HonestInputs.Trapdoor) (ps : Positions) (pos : 0<ps.card)
    (n : Nat) (t : MachineState) (prefixRun : CommitExact.Segment o image n (HonestInputs.first trap ps) t)
    (pc : t.pc=addr 1429) : Goal ps t :=
  segment prefixRun (observed ps 0 pos _ (HonestAllRecords.first trap ps pos) (HonestSortedTraversal.first trap ps pos)) pc

end CommitGolfCandidate.Reconstruction.HonestSegmentFlags
