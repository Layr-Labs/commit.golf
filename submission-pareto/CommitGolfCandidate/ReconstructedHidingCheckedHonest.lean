import CommitGolfCandidate.ReconstructedHidingCheckedPrefix
import CommitGolfCandidate.NonceChainView

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64 HidingTraffic
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false

def honestFirst (m : Message) (i : Index) : Reply := packBuffer (pinnedFirstInput (messageWords m i))

def honestSecond (p : BiPermutation Block) (m : Message) (r : CompleteSaltTape) (i : Index) : Reply :=
  packBuffer (pinnedSecondInput i (saltWords (r i)) (replyWords (p.forward (honestFirst m i))) (messageWords m i))

def honestPermit (allow : Reply → Reply → Bool) (p : BiPermutation Block) (m : Message) (r : CompleteSaltTape) : Prop :=
  ∀ i, allow (honestFirst m i) (p.forward (honestFirst m i))=true ∧
    allow (honestSecond p m r i) (p.forward (honestSecond p m r i))=true

theorem checked_salted_digest (o : Oracle) (allow : Reply → Reply → Bool) (m : Message)
    (r : CompleteSaltTape) (i : Index) (flag : Bool)
    (pass : honestPermit allow (BiPermutation.equiv Block o.permutation) m r) :
    fixedOracleRun o (checkedQueries allow (querySaltedDigest m r i) flag) =
      pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r i,flag) := by
  obtain ⟨first,second⟩ := pass i
  let p := BiPermutation.equiv Block o.permutation
  let x := honestFirst m i
  let y := honestSecond p m r i
  unfold querySaltedDigest
  rw [checked_query,fixed_oracle_run_public,checked_query,fixed_oracle_run_public,checked_pure,fixed_oracle_run_pure]
  change pure (pinnedFullLeafDigests p m r i,(flag && allow x (p.forward x)) && allow y (p.forward y)) = _
  rw [first,second,Bool.and_true,Bool.and_true]

theorem checked_list_run {I A : Type} (o : Oracle) (allow : Reply → Reply → Bool)
    (op : I → OracleComp World A) (value : I → A) (xs : List I) (flag : Bool)
    (run : ∀ i ∈ xs, ∀ f, fixedOracleRun o (checkedQueries allow (op i) f)=pure (value i,f)) :
    fixedOracleRun o (checkedQueries allow (CommitGolfCandidate.queryList op xs) flag)=pure (xs.map value,flag) := by
  induction xs generalizing flag with
  | nil => exact fixed_oracle_run_pure _ _
  | cons head tail ih =>
    rw [CommitGolfCandidate.queryList,checked_bind,fixed_oracle_run_bind,run head List.mem_cons_self,pure_bind]
    rw [checked_bind,fixed_oracle_run_bind,ih flag (fun i mem => run i (List.mem_cons_of_mem _ mem)),pure_bind,
      checked_pure,fixed_oracle_run_pure,List.map_cons]

attribute [local irreducible] querySaltedDigest CommitGolfCandidate.queryList List.finRange

theorem checked_honest_digests (o : Oracle) (allow : Reply → Reply → Bool) (m : Message)
    (r : CompleteSaltTape) (flag : Bool)
    (pass : honestPermit allow (BiPermutation.equiv Block o.permutation) m r) :
    fixedOracleRun o (checkedQueries allow (queryDigests m r) flag)=
      pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r,flag) := by
  let ds := pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r
  rw [queryDigests,checked_bind,fixed_oracle_run_bind,checked_list_run o allow _ ds _ flag
    (fun i _ f => checked_salted_digest o allow m r i f pass),pure_bind,checked_pure,fixed_oracle_run_pure]
  apply congrArg (fun f : DigestTape => (pure (f,flag) : ProbComp _))
  funext i
  rw [List.getElem?_eq_getElem (by simp [i.isLt])]
  simp [ds]

end CommitGolfCandidate.Reconstruction.HidingTape
