import CommitGolfCandidate.ReconstructedCommitMachine

namespace CommitGolfCandidate.Reconstruction.CommitMachine
open CommitGolf CommitGolf.Riscv OracleComp Generator
attribute [local irreducible] Riscv.execute ArtifactEncoding.decode Artifact.submission followingDraw
set_option maxRecDepth 12000
local instance discreteOutput {α : Type} : MeasurableSpace α := ⊤

/-- Any continuation depending on the ABI root and the stored tree can average
directly over the uniform three-word key drawn by this actual machine. -/
theorem key_average {α : Type} (o : Oracle) (msg : Message) (next : Execution → ProbComp α)
    (reference : Key → ProbComp α) (matching : ∀ k e, Completed o k msg e → next e=reference k) :
    𝒟[(fixedOracleRun o (Artifact.submission.run .commit msg)) >>= next] = 𝒟[($ᵗ Key) >>= reference] := by
  refine Eq.trans ?_ (CommitKey.key_distribution reference)
  apply congrArg (fun g : ProbComp α => 𝒟[g])
  rw [sampled,bind_assoc]
  apply bind_congr
  intro r
  obtain ⟨e,atKey,h⟩ := one_key o msg r
  rw [atKey,pure_bind,pure_bind]
  exact matching _ _ (h.charge 10 0)

theorem counted_output (o : Oracle) (msg : Message) (r : Execution × Nat)
    (hr : r ∈ support (o.run (Artifact.submission.run .commit msg))) :
    (∃ k, Completed o k msg r.1) ∧ r.1.cycles≤1489523308 ∧ r.2≤56030463 := by
  have observed : r.1 ∈ support (fixedOracleRun o (Artifact.submission.run .commit msg)) := by
    change r.1 ∈ support (Prod.fst <$> o.run _)
    rw [support_map]
    exact ⟨r,hr,rfl⟩
  obtain ⟨r',hh⟩ := supported o msg r.1 observed
  have bound := CommitTrace.counted o msg r hr
  exact ⟨⟨_,hh⟩,bound.1,bound.2.1⟩

theorem succeeds (o : Oracle) (msg : Message) :
    Pr{let r ← o.run (Artifact.submission.run .commit msg)}[r.1.exit=.success ∧ r.2≤56030463] = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr
  obtain ⟨⟨k,hh⟩,_,q⟩ := counted_output o msg r hr
  exact ⟨hh.success,q⟩

end CommitGolfCandidate.Reconstruction.CommitMachine
