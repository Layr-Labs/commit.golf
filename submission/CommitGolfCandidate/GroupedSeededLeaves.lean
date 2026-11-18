import CommitGolfCandidate.GroupedSeed
import CommitGolfCandidate.K3CBQuad

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer scan fixedScan readyState
def seededLeaves (o : Oracle) (m : Message) (k : Key) :=
  fixedScan o N 0 (readyState (K1Artifact.submission.initialState .commit m) k)

private theorem fixed_supported (o : Oracle) (s : MachineState) (n j : Nat) (b : j+n≤N) :
    fixedScan o n j s∈support (scan n j s) := by
  let z : MachineState × Nat := (fixedScan o n j s,Q (j+n)-Q j)
  have hit : z∈support (o.run (scan n j s)) := by
    rw [fixed_scan_run o n j s b,support_pure,Set.mem_singleton_iff]
  exact writer_support (o.world.withAddCost Oracle.callCost) (scan n j s) z hit

private theorem seeded_summary (o : Oracle) (m : Message) (k : Key) (s : MachineState) (n : Nat) (bound : n≤N)
    (start : Live s 0) (good : Good o k m s.getReg (memoryView s) 0) :
    Live (fixedScan o n 0 s) n ∧ Good o k m (fixedScan o n 0 s).getReg (memoryView (fixedScan o n 0 s)) n := by
  have b : 0+n≤N := by omega
  have live := scan_post n 0 s (fixedScan o n 0 s) b start (fixed_supported o s n 0 b)
  have endGood := scan_content o k m n 0 s b start good
  simpa only [Nat.zero_add] using And.intro live endGood

theorem seeded_content (o : Oracle) (m : Message) (k : Key) :
    Live (seededLeaves o m k) N ∧ Good o k m (seededLeaves o m k).getReg (memoryView (seededLeaves o m k)) N := by
  unfold seededLeaves
  exact seeded_summary o m k _ N le_rfl (ready_live _ ⟨rfl,rfl,rfl,rfl⟩ k) (initially_good o k m)

attribute [local semireducible] readyState

/-- What the body hands to the upper stage (CU's `TailReady`). -/
theorem seeded_tail_ready (o : Oracle) (m : Message) (k : Key) :
    TailReady o (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (chainSalts o k)) k
      (memoryView (seededLeaves o m k)) := by
  have good := (seeded_content o m k).2
  constructor
  · intro g hg
    rw [reply_word_eq,good.cells.replies g (by show 4*g+4≤16777216;omega),quartet_reply_model]
  · intro i hi ov t ht
    have c := congrFun (good.cells.children ⟨i,hi⟩ hi (by unfold overwritten at ov;show ¬(i%4=3 ∧ i/4%2=0);omega)) ⟨t,ht⟩
    have a : leafWord i=qLeaf i := by unfold leafWord cellFirst qLeaf qSource;omega
    rw [a];simp only [window] at c;rw [c]
    unfold digestOf value Quartet.leafAt;rw [dif_pos (show i<LENGTH from hi)]
  · intro j
    have kk := good.msgs.key (1+j.val) (by omega) (by have := j.isLt;omega)
    unfold keyWord;unfold qSalt at kk
    rw [show 1140851205+j.val=1140851204+2*0+(1+j.val) by omega,kk]
    unfold keyBlock;congr 1;omega

end TwoPermutationPrototype.Grouped
