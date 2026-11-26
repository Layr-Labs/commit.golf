import CommitGolfCandidate.ReconstructedHidingCheckedHonest
import CommitGolfCandidate.ReconstructedHidingJointRows

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false

def leafFlag (allow : Reply → Reply → Bool) (p : BiPermutation Block) (m : Message) (r : CompleteSaltTape) (i : Index) : Bool :=
  allow (honestFirst m i) (p.forward (honestFirst m i)) && allow (honestSecond p m r i) (p.forward (honestSecond p m r i))

def allLeafFlags (allow : Reply → Reply → Bool) (p : BiPermutation Block) (m : Message) (r : CompleteSaltTape) :=
  (List.finRange LENGTH).all (leafFlag allow p m r)

theorem checked_salted_flags (o : Oracle) (allow : Reply → Reply → Bool) (m : Message) (r : CompleteSaltTape)
    (i : Index) (b : Bool) :
    let p := BiPermutation.equiv Block o.permutation
    fixedOracleRun o (checkedQueries allow (querySaltedDigest m r i) b) =
      pure (pinnedFullLeafDigests p m r i,b && leafFlag allow p m r i) := by
  unfold querySaltedDigest
  rw [checked_query,fixed_oracle_run_public,checked_query,fixed_oracle_run_public,checked_pure,fixed_oracle_run_pure]
  exact congrArg (fun x => pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r i,x))
    (Bool.and_assoc b _ _)

theorem checked_list_flags {I A : Type} (o : Oracle) (allow : Reply → Reply → Bool)
    (f : I → OracleComp World A) (value : I → A) (valid : I → Bool) (xs : List I) (b : Bool)
    (run : ∀ i ∈ xs, ∀ start, fixedOracleRun o (checkedQueries allow (f i) start)=pure (value i,start && valid i)) :
    fixedOracleRun o (checkedQueries allow (queryList f xs) b) = pure (xs.map value,b && xs.all valid) := by
  induction xs generalizing b with
  | nil => simp only [List.map_nil,List.all_nil,Bool.and_true]; exact fixed_oracle_run_pure _ _
  | cons x xs ih =>
    rw [queryList,checked_bind,fixed_oracle_run_bind,run x List.mem_cons_self,pure_bind]
    rw [checked_bind,fixed_oracle_run_bind,ih (b && valid x) (fun i h => run i (List.mem_cons_of_mem _ h)),
      pure_bind,checked_pure,fixed_oracle_run_pure,List.map_cons,List.all_cons,Bool.and_assoc]

attribute [local irreducible] querySaltedDigest queryList List.finRange

theorem checked_digests_flags (o : Oracle) (allow : Reply → Reply → Bool) (m : Message) (r : CompleteSaltTape) (b : Bool) :
    let p := BiPermutation.equiv Block o.permutation
    fixedOracleRun o (checkedQueries allow (queryDigests m r) b)=
      pure (pinnedFullLeafDigests p m r,b && allLeafFlags allow p m r) := by
  let p := BiPermutation.equiv Block o.permutation
  let ds := pinnedFullLeafDigests p m r
  rw [queryDigests,checked_bind,fixed_oracle_run_bind,checked_list_flags o allow _ ds (leafFlag allow p m r) _ b
    (fun i _ f => checked_salted_flags o allow m r i f),pure_bind,checked_pure,fixed_oracle_run_pure]
  apply congrArg (fun f : DigestTape => (pure (f,b && allLeafFlags allow p m r) : ProbComp _))
  funext i
  rw [List.getElem?_eq_getElem (by simp [i.isLt])]
  simp [ds,p]

attribute [local irreducible] packedAddress

theorem second_avoids_generator (p : BiPermutation Block) (m : Message) (r : CompleteSaltTape)
    (i : Index) (k : Key) (j : Fin groupCount) : packedAddress k j ≠ honestSecond p m r i := by
  intro same
  obtain ⟨t,g,words⟩ := address_key_hit k j
  have first := words 0 (by decide)
  rw [zero_before t g k 0 (by unfold marker; omega)] at first
  have tag := pinned_second_tag i (saltWords (r i)) (p.forward (honestFirst m i)) (messageWords m i)
  change (honestSecond p m r i).extractLsb' 0 64 = pinnedPositionTag i at tag
  rw [same] at first
  have z := congrArg BitVec.toNat ((show (0:BitVec 64)=(honestSecond p m r i).extractLsb' 0 64 from first).trans tag)
  change 0 = (4152+256*i.val)%2^64 at z
  have cap : i.val < 2^24 := i.isLt
  omega

end CommitGolfCandidate.Reconstruction.HidingTape
