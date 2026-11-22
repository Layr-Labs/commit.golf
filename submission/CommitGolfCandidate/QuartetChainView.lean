import CommitGolfCandidate.NoncePairOracle
import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.PublicQueryList

/-! Adapted from submission c28dd9ca (dadon), `NonceChainView`, for Quartet. The honest public
computation now also queries the 2^22 quartet permutation nodes, so its budget is
`t + 2·LENGTH + 2^22 + t`. The builder reads its quartet lookup only at the 2^22 payloads of the
leaf tape, so the queried answers can stand in for the permutation. -/
namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NoncePair (Key actualNonces blocks)
local instance quartetChainViewDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-! ### The builder depends on the quartet lookup only at the tape's payloads -/

theorem reference_heap_congr (compress : Compression) (leafCount : Nat) (leaf leaf' : Nat → Digest)
    (same : ∀ g < leafCount, leaf g = leaf' g) (node : Nat) :
    referenceHeap compress leafCount leaf node = referenceHeap compress leafCount leaf' node := by
  conv_lhs => rw [referenceHeap]
  conv_rhs => rw [referenceHeap]
  by_cases branch : 0 < node ∧ node < leafCount
  · rw [dif_pos branch, dif_pos branch,
      reference_heap_congr compress leafCount leaf leaf' same (2*node),
      reference_heap_congr compress leafCount leaf leaf' same (2*node+1)]
  · rw [dif_neg branch, dif_neg branch]
    by_cases low : leafCount ≤ node ∧ node < 2*leafCount
    · rw [if_pos low, if_pos low]
      exact same _ (by omega)
    · rw [if_neg low, if_neg low]
termination_by 2*leafCount - node
decreasing_by all_goals omega

/-- `builder` with the 2^22 quartet digests supplied directly. -/
def builderFrom (quads : Nat → BitVec 256) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) : Commitment × Proof :=
  let heap := referenceHeap (projectInternal true compress) 4194304 quads
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let records := ordered.flatMap (fun i => openingRecord leaves heap i.val (salts i))
  (heap 1, records ++ frontierProof true heap (ordered.map (capGroup ∘ Subtype.val)))

theorem builder_eq_from (lookup : BitVec 1024 → BitVec 256) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) :
    builder lookup compress positions salts leaves =
      builderFrom (fun g => lookup (quartetPayload leaves g)) compress positions salts leaves := rfl

theorem builder_from_congr (quads quads' : Nat → BitVec 256) (same : ∀ g < 4194304, quads g = quads' g)
    (compress : Compression) (positions : Positions) (salts : OpenedSalts positions) (leaves : DigestTape) :
    builderFrom quads compress positions salts leaves = builderFrom quads' compress positions salts leaves := by
  have heap : referenceHeap (projectInternal true compress) 4194304 quads =
      referenceHeap (projectInternal true compress) 4194304 quads' :=
    funext (reference_heap_congr _ _ _ _ same)
  unfold builderFrom
  rw [heap]

/-! ### Honest public queries -/

def querySaltedDigest (m : Message) (r : CompleteSaltTape) (i : Index) :
    OracleComp World (BitVec 256) := do
  let a ← World.query (.inr (.inr (.inl (RV64.packBuffer (pinnedFirstInput (messageWords m i))))))
  let b ← World.query (.inr (.inr (.inl (RV64.packBuffer (pinnedSecondInput i (saltWords (r i)) (RV64.replyWords a) (messageWords m i))))))
  return outputDigest b

theorem query_salted_bound (m : Message) (r : CompleteSaltTape) (i : Index) :
    PublicQueryBound (querySaltedDigest m r i) 2 := by
  unfold querySaltedDigest
  exact ⟨(by change 1 ≤ 2;omega),fun a => ⟨(by change 1 ≤ 2-1;omega),fun b => trivial⟩⟩

theorem query_salted_run (o : Oracle) (m : Message) (r : CompleteSaltTape) (i : Index) :
    fixedOracleRun o (querySaltedDigest m r i) =
      pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r i) := by
  rw [querySaltedDigest,fixed_oracle_run_public,fixed_oracle_run_public,fixed_oracle_run_pure]
  rfl

def queryDigests (m : Message) (r : CompleteSaltTape) : OracleComp World DigestTape := do
  let ds ← queryList (querySaltedDigest m r) (List.finRange LENGTH)
  return fun i => ds[i.val]?.getD 0

def quartetQuery (payload : BitVec 1024) : OracleComp World (BitVec 256) := do
  let y ← World.query (.inr (.inr (.inl (payload ++ (0 : BitVec 576)))))
  return pinnedOutputDigest y

theorem quartet_query_bound (payload : BitVec 1024) : PublicQueryBound (quartetQuery payload) 1 := by
  unfold quartetQuery
  exact ⟨(by change 1 ≤ 1;omega),fun _ => trivial⟩

theorem quartet_query_run (o : Oracle) (payload : BitVec 1024) :
    fixedOracleRun o (quartetQuery payload) =
      pure (quartetLookup (BiPermutation.equiv Block o.permutation) payload) := by
  rw [quartetQuery,fixed_oracle_run_public,fixed_oracle_run_pure]
  rfl

def queryQuartets (ds : DigestTape) : OracleComp World (List (BitVec 256)) :=
  queryList (fun g => quartetQuery (quartetPayload ds g)) (List.range 4194304)

attribute [local irreducible] List.finRange queryList querySaltedDigest quartetQuery

theorem query_digests_bound (m : Message) (r : CompleteSaltTape) :
    PublicQueryBound (queryDigests m r) (2*LENGTH) := by
  have h := public_query_bound_bind (query_list_bound _ 2 (query_salted_bound m r) (List.finRange LENGTH))
    (fun ds => show PublicQueryBound (pure (fun i : Index => ds[i.val]?.getD 0) : OracleComp World _) 0 from trivial)
  simpa only [queryDigests,List.length_finRange,Nat.add_zero,Nat.mul_comm] using h

theorem query_digests_run (o : Oracle) (m : Message) (r : CompleteSaltTape) :
    fixedOracleRun o (queryDigests m r) = pure (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m r) := by
  rw [queryDigests,fixed_oracle_run_bind,query_list_reference o _ _ _ (fun i _ => query_salted_run o m r i),
    pure_bind,fixed_oracle_run_pure]
  apply congrArg pure
  funext i
  rw [List.getElem?_eq_getElem (by simp [i.isLt])]
  simp

theorem query_quartets_bound (ds : DigestTape) : PublicQueryBound (queryQuartets ds) 4194304 := by
  have h := query_list_bound _ 1 (fun g => quartet_query_bound (quartetPayload ds g)) (List.range 4194304)
  simpa only [queryQuartets,List.length_range,Nat.mul_one] using h

theorem query_quartets_run (o : Oracle) (ds : DigestTape) :
    fixedOracleRun o (queryQuartets ds) =
      pure ((List.range 4194304).map (fun g => quartetLookup (BiPermutation.equiv Block o.permutation) (quartetPayload ds g))) :=
  query_list_reference o _ _ _ (fun g _ => quartet_query_run o (quartetPayload ds g))

theorem queried_quartets (p : BiPermutation Block) (ds : DigestTape) (g : Nat) (inside : g < 4194304) :
    ((List.range 4194304).map (fun g => quartetLookup p (quartetPayload ds g))).getD g 0 =
      quartetLookup p (quartetPayload ds g) := by
  rw [List.getD_eq_getElem _ _ (by simp [inside])]
  simp

noncomputable def guardedView {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (t : Nat)
    (aux : S) (root : Commitment) (proof : Proof) : OracleComp World O :=
  @ite _ (∀ root proof, PublicQueryBound (a.observe aux root proof) t) (Classical.propDecidable _)
    (a.observe aux root proof) (pure (support_nonempty (a.observe aux root proof)).some)

theorem guarded_view_bound {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (t : Nat)
    (aux : S) (root : Commitment) (proof : Proof) : PublicQueryBound (guardedView a t aux root proof) t := by
  unfold guardedView
  split
  · rename_i h
    exact h _ _
  · trivial

theorem reached_view {S O : Type} {n t : Nat} (o : Oracle) (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (ch : Hiding.HidingChallenge S n)
    (reached : ch ∈ support (fixedOracleRun o a.choose)) (root : Commitment) (proof : Proof) :
    guardedView a t ch.aux root proof = a.observe ch.aux root proof := by
  have possible : ch ∈ support a.choose := by
    rw [fixed_run_eq_simulate] at reached
    exact (support_simulateQ_subset _ _) reached
  have instrumented : ch ∈ support (Prod.fst <$> Hiding.counted a.choose) := by
    rw [show Prod.fst <$> Hiding.counted a.choose = a.choose from fst_map_costDist a.choose ⟨Oracle.callCost⟩]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨other,calls⟩,hit,eq⟩ := instrumented
  change other = ch at eq
  subst other
  have guard (root : Commitment) (proof : Proof) := (hiding_observe_query_bound a h (ch,calls) hit root proof).mono (Nat.sub_le _ _)
  exact if_pos guard

/-- Stage one, the honest leaf and quartet queries on the salt array `r`, then stage two. -/
noncomputable def chainPublicComp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (c : Compression) (b : Bool) (r : CompleteSaltTape) : OracleComp World O := do
  let ch ← a.choose
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let qs ← queryQuartets ds
  let view := builderFrom (fun g => qs.getD g 0) c ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] queryDigests queryQuartets guardedView

theorem chain_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (c : Compression) (b : Bool) (r : CompleteSaltTape) :
    PublicQueryBound (chainPublicComp a t c b r) (t + (2*LENGTH + (4194304 + t))) := by
  unfold chainPublicComp
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (query_digests_bound _ _)
  intro ds
  apply public_query_bound_bind (query_quartets_bound ds)
  intro qs
  exact guarded_view_bound a t ch.aux _ _

theorem chain_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (chainPublicComp a t o.compression b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (honestView builder) o.compression ch b (BiPermutation.equiv Block o.permutation) r) := by
  rw [chainPublicComp,fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind,query_digests_run,pure_bind,fixed_oracle_run_bind,query_quartets_run,pure_bind,
    reached_view o a h ch hit]
  let p := BiPermutation.equiv Block o.permutation
  let message := if b then ch.message₁ else ch.message₀
  let ds := pinnedFullLeafDigests p message r
  have same := builder_from_congr
    (fun g => ((List.range 4194304).map (fun g => quartetLookup p (quartetPayload ds g))).getD g 0)
    (fun g => quartetLookup p (quartetPayload ds g)) (fun g inside => queried_quartets p ds g inside)
    o.compression ch.positions (fun i => r i.val) ds
  simp only [observeTranscriptView,honestView,fixedOracle,Equiv.symm_apply_apply,builder_eq_from]
  rw [same]

end TwoPermutationPrototype.Sampling.Quartet
