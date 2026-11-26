import CommitGolfCandidate.TruncReplayChildren
import CommitGolfCandidate.BindingReplay
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 55000
attribute [local irreducible] lowerHash climb storeNode pathInputs

private theorem parentReply (H : Compression) (n : Nat) (ch : Children) (slot : Digest) :
    (pure ((if ch.left.isNone && ch.right.isNone then slot else storeNode n (H (padInput ((ch.right.getD slot) ++ (ch.left.getD slot))))),41) : ProbComp (Digest × Nat)) =
      pure (parentFrom H n ch slot,41) := by
  rcases ch with ⟨l,r⟩;cases l <;> cases r <;> rfl

def queryParent (input : CheckInput) (p : Nat) : OracleComp World Digest := do
  let ch ← queryChildren input p
  let slot := supplied input p
  let d ← liftM (World.query (.inr (.inl (padInput ((ch.right.getD slot) ++ (ch.left.getD slot))))))
  return if ch.left.isNone && ch.right.isNone then slot else storeNode (128+p) d

theorem parentRun (o : Oracle) (input : CheckInput) (p : Nat) :
    o.run (queryParent input p) = pure (parentAt o.compression input p,41) := by
  simp only [queryParent, oracle_run_bind,childrenRun,pure_bind]
  erw [oracle_run_public_bind]
  simp only [oracle_run_pure,pure_bind]
  exact parentReply o.compression (128+p) (childrenAt o.compression input p) (supplied input p)

theorem parentBound (input : CheckInput) (p : Nat) : IsTotalQueryBound (queryParent input p) 41 := by
  unfold queryParent
  change IsTotalQueryBound (_ >>= _) (40+1)
  apply isTotalQueryBound_bind (childrenBound _ _)
  intro ch
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide,fun _ => trivial⟩

end CommitGolfCandidate.Trunc
