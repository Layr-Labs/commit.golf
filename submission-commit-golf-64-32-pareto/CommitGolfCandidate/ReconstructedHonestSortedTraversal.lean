import CommitGolfCandidate.ReconstructedHonestAllOpening
import CommitGolfCandidate.ReconstructedHonestSortedFlags

namespace CommitGolfCandidate.Reconstruction.HonestSortedTraversal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestAllRecords HonestSortedFlags HonestFinishes
open HonestRecordMemory (W idx)
open HonestWideKernel (image)
open CommitBlocks (addr)

attribute [local irreducible] ArtifactEncoding.decode execute
set_option maxRecDepth 16384

def indices (ps : Positions) (s : MachineState) := ∀ j (hj : j<ps.card),
    s.getMem (W (idx+8*j))=W ((ps.sort (·≤·))[j]'(by simpa using hj)).val

structure Seen (ps : Positions) (i : Nat) (s : MachineState) : Prop where
  positions : indices ps s
  flags : current (prefixFlags ps i) s

theorem first (trap : HonestInputs.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    Seen ps 0 (HonestInputs.first trap ps) :=
  ⟨fun j hj => HonestInputs.first_index trap ps j hj,HonestSortedFlags.first trap ps pos⟩

theorem one (ps : Positions) (i : Nat) (hi : i<ps.card) (s t : MachineState) (ready : Ready ps.card i s)
    (seen : Seen ps i s) (path : HonestCuts.Reaches image true HonestRecordCost.cut s t) :
    (if i+1<ps.card then Ready ps.card (i+1) t else t.pc=addr 1429 ∧
      HonestProtected.Holds HonestWideMemory.context HonestWideMemory.finish t) ∧ Seen ps (i+1) t := by
  have limit := HonestWideMemory.cardinality ps
  obtain ⟨next,marked,frame⟩ := iteration HonestWideKernel.all_checked HonestNameKernel.all_checked
    ps.card i hi limit s t ready path
  exact ⟨next,⟨fun j hj => (frame _ (index_in j (by omega))).trans (seen.positions j hj),
    advance ps i hi (values ps.card i s) (seen.positions i hi) seen.flags marked⟩⟩

/-- At the cap entry, all 512 physical leaf bytes equal the score profile's flags
for the complete sorted opening. All physical bytes for the 511 internal nodes
are still zero, and the ABI position table retains its initial sorted contents. -/
theorem finish (ps : Positions) (s : MachineState) (seen : Seen ps ps.card s) :
    indices ps s ∧ current (Frontier.flags (ps.sort (·≤·))) s := ⟨seen.positions,HonestSortedFlags.finish ps s seen.flags⟩

/-- One may continue a successful submitted opening from its actual cap state
with the exact, rather than cardinality-bounded, reference physical flag table. -/
theorem records (ps : Positions) (i : Nat) (hi : i<ps.card) {good : MachineState→Prop}
    (s : MachineState) (ready : Ready ps.card i s) (seen : Seen ps i s)
    (after : ∀ t, t.pc=addr 1429 → HonestProtected.Holds HonestWideMemory.context HonestWideMemory.finish t →
      indices ps t → current (Frontier.flags (ps.sort (·≤·))) t → SuccessPost image true good t) :
    SuccessPost image true good s := by
  suffices all : ∀ n i, ps.card-i=n → i<ps.card → ∀ s, Ready ps.card i s → Seen ps i s →
      SuccessPost image true good s from all _ i rfl hi s ready seen
  intro n
  induction n with
  | zero => intro i h hi; omega
  | succ n ih =>
    intro i h hi s ready seen
    refine HonestRecordCost.record_success (good:=good) s ready.pc true ?_
    intro t path
    obtain ⟨next,seen'⟩ := one ps i hi s t ready seen path
    by_cases more : i+1<ps.card
    · rw [ite_eq_left more] at next; exact ih (i+1) (by omega) more t next seen'
    · rw [ite_eq_right more] at next
      rw [show i+1=ps.card by omega] at seen'
      have done_ := finish ps t seen'
      exact after t next.1 next.2 done_.1 done_.2

end CommitGolfCandidate.Reconstruction.HonestSortedTraversal
