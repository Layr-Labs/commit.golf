import CommitGolfCandidate.ReconstructedCommitStorage
import CommitGolfCandidate.ReconstructedCommitParents
import CommitGolfCandidate.ReconstructedCommitScored

namespace CommitGolfCandidate.Reconstruction.CommitMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open LeafContent LeafModel Generator CommitStorage
attribute [local irreducible] ArtifactEncoding.decode execute readBuffer
set_option maxRecDepth 14000
local instance discrete {α : Type} : MeasurableSpace α := ⊤

structure Completed (o : Oracle) (k : Key) (msg : Message) (e : Execution) : Prop where
  success : e.exit = .success
  output : (Artifact.submission.readCommit e).1 = Binding.pack (LeafTree.tree o k msg 0 1)
  contents : Stored o k msg (Artifact.submission.readCommit e).2

theorem Completed.charge {o k msg n} (h : Completed o k msg n) (c q : Nat) :
    Completed o k msg (n.charge c q) := ⟨h.success,h.output,h.contents⟩

def followingDraw (o : Oracle) (msg : Message) (r : BitVec 192) :=
  fixedOracleRun o (execute CommitSetup.im 1073741817
    (CommitKey.afterDraw (Artifact.submission.initialState .commit msg) r) true)

/-- For every possible private draw the submitted commitment runs to a successful
HALT and returns the reference root and the opener's serialized trapdoor. -/
theorem one_key (o : Oracle) (msg : Message) (r : BitVec 192) :
    ∃ e : Execution, followingDraw o msg r = (Pure.pure e : ProbComp Execution) ∧ Completed o (CommitKey.key r) msg e := by
  let k := CommitKey.key r
  let initial := Artifact.submission.initialState .commit msg
  obtain ⟨c₀,q₀,setup⟩ := CommitKey.setup o initial rfl r
  obtain ⟨s,m,⟨c₁,q₁,leaves⟩,fits,pc,zero,_,pre⟩ := LeafTrace.leaves o msg r
  have heap := LeafTree.snapshot o k msg s m fits pre
  obtain ⟨t,c,q,out,last⟩ := CommitParents.certified o (LeafTree.values o k msg) (LeafTree.canonical o k msg) s pc zero heap
  have stored := matches_state o k msg s t m fits pre out.root out.heap
    (fun a n hi lo => out.frame a n hi (.inr lo))
  let final : Execution := ⟨.success,t,c,q⟩
  have good : Completed o k msg final := ⟨rfl,out.commitment,stored⟩
  refine ⟨(final.charge c₁ q₁).charge c₀ q₀,?_,(good.charge _ _).charge _ _⟩
  change fixedOracleRun o (execute CommitSetup.im (12+(217075711+(108073566+748592528))) _ true) = _
  rw [setup]
  change (fun x : Execution => x.charge c₀ q₀) <$> fixedOracleRun o
    (execute CommitSetup.im (217075711+(108073566+748592528)) (LeafTrace.startState msg r) true) = _
  rw [leaves,last, map_pure, map_pure]

private theorem coins (o : Oracle) {α : Type} (x : ProbComp α) :
    fixedOracleRun o (liftM x : OracleComp World α) = x := by
  rw [fixedOracleRun,oracle_run_coins,Functor.map_map]
  exact id_map x

private theorem actual (s : Submission) (m : Message) : s.run .commit m =
    execute (s.image .commit) (s.steps .commit) (s.initialState .commit m) true := rfl

private theorem abi (m : Message) : Artifact.submission.run .commit m =
    execute CommitSetup.im (7+1073741817) (Artifact.submission.initialState .commit m) true := actual _ _

/-- Distributional execution includes the actual uniform 192-bit RANDOM instruction. -/
theorem sampled (o : Oracle) (msg : Message) :
    fixedOracleRun o (Artifact.submission.run .commit msg) =
      (do let r ← ($ᵗ BitVec 192 : ProbComp _)
          let e ← followingDraw o msg r
          return e.charge 10 0) := by
  rw [abi,CommitKey.draw _ rfl,fixed_oracle_run_bind,coins]
  apply bind_congr
  intro r
  rw [fixed_oracle_run_bind]
  simp only [fixed_oracle_run_pure,followingDraw]

theorem supported (o : Oracle) (msg : Message) (e : Execution)
    (member : e ∈ support (fixedOracleRun o (Artifact.submission.run .commit msg))) :
    ∃ r : BitVec 192, Completed o (CommitKey.key r) msg e := by
  rw [sampled] at member
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at member
  obtain ⟨r,_,x,inRun,eq⟩ := member
  obtain ⟨t,run,good⟩ := one_key o msg r
  rw [run] at inRun
  have same : x=t := by simpa only [support_pure,Set.mem_singleton_iff] using inRun
  exact ⟨r,eq ▸ same ▸ good.charge 10 0⟩

end CommitGolfCandidate.Reconstruction.CommitMachine
