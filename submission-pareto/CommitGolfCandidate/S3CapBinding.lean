import CommitGolfCandidate.Probability
import CommitGolfCandidate.CapProbeCache

/-! Stage-3 binding core, independent of the checker image. A winning claim is
assumed to give, for the fixed oracle, a compression reply collision in a paid
claim probe or a collision among the replayed permutation leaves. Two budgeted
searches follow the same query-limited adversary: the compression search is
bounded by the lazy compression birthday argument for every fixed permutation,
the leaf search by the leaf collision bound for every fixed compression. The
leaf bound enters as a hypothesis with the exact statement of
`s3_leaf_collision_bound`. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling
set_option autoImplicit false

/-- The statement of `s3_leaf_collision_bound` (leaf binding for any fixed
compression function and a uniform permutation with inverse queries). -/
def S3LeafCollisionBound : Prop :=
  ∀ (compression : Compression)
    (first : OracleComp World (Option (List (BitVec 256 × Entry)))) (budget extra : Nat),
    PublicQueryBound first budget → budget ≤ 2 ^ 120 → extra ≤ 2 ^ 26 →
    prEvent (LeafCollision <$> (($ᵗ Perm) >>= fun permutation =>
        fixedOracleRun ⟨compression, permutation⟩ (s3LeafSearch first extra))) ≤
      ((budget : ENNReal) + 2 * extra) ^ 2 / 2 ^ 256 + (budget : ENNReal) / 2 ^ 127

/-! ### Accepted batches: deterministic extraction -/

theorem cap_check_replay_trace_unique (oracle : Oracle)
    (computation : OracleComp World (Option (List (BitVec 512))))
    (inputs inputs' : List (BitVec 512)) (calls calls' : Nat)
    (first : oracle.run computation=pure (some inputs,calls))
    (second : oracle.run computation=pure (some inputs',calls')) :
    inputs=inputs' := by
  have reachable : (some inputs,calls) ∈ support (oracle.run computation) := by
    rw [first]
    simp
  rw [second] at reachable
  have same := eq_of_mem_support_pure (some inputs',calls') reachable
  exact Option.some.inj (congrArg Prod.fst same)

theorem cap_check_witness_trace_length (compress : Compression) {height : Nat}
    {view : CapView height} {proof rest : List Digest} {root : Digest}
    {inputs : List (BitVec 512)}
    (witness : CapDecodeWitness compress view proof root rest inputs) :
    inputs.length=capCalls view := by
  induction witness with
  | unknown view root rest unoccupied =>
    cases view <;> simp only [List.length_nil,capCalls,unoccupied,
      Bool.false_eq_true,↓reduceIte]
  | known value proof => rfl
  | node left right proof rest rest' lroot rroot leftInputs rightInputs occupied
      leftDecoded rightDecoded ihLeft ihRight =>
    simp only [List.length_append,List.length_cons,List.length_nil,
      capCalls,occupied,↓reduceIte,ihLeft,ihRight]

/-- An accepted batch admits a complete paid replay whose recorded compression
trace fits the probe's syntactic guard. -/
theorem cap_accepted_replay (oracle : Oracle) (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) (roots : CapRootMap)
    (lower : capLowerBatchRoots oracle.compression oracle.permutation records
      (fun _ => none) = some roots)
    (cap : capDecode oracle.compression (capKnownView roots 8 0) proof = some (root, [])) :
    ∃ inputs calls,
      oracle.run (capReplayBatch records proof root) = pure (some inputs, calls) ∧
      inputs.length ≤ 24 * records.length + 255 := by
  obtain ⟨capInputs, witness⟩ := cap_decode_witness oracle.compression
    (capKnownView roots 8 0) proof [] root cap
  have capRun := cap_replay_witness_run oracle witness
  refine ⟨capLowerBatchInputs oracle.compression oracle.permutation records ++ capInputs,
    18 * records.length + capInputs.length, ?_, ?_⟩
  · simp only [capReplayBatch]
    erw [oracle_run_bind, cap_replay_lower_batch_run oracle records _ roots lower]
    simp only [pure_bind]
    erw [oracle_run_bind, capRun]
    simp [oracle_run_pure]
  · rw [List.length_append, cap_lower_batch_inputs_length,
      cap_check_witness_trace_length _ witness]
    have bound := cap_calls_full_bound (capKnownView roots 8 0)
    norm_num at bound
    omega

/-- Two accepted batches with conflicting values at one index: the paid pair
probe returns a compression reply collision, or two replayed leaves collide. -/
theorem cap_accepted_pair_collision (oracle : Oracle)
    (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (leftRoots rightRoots : CapRootMap)
    (leftLower : capLowerBatchRoots oracle.compression oracle.permutation leftRecords
      (fun _ => none) = some leftRoots)
    (rightLower : capLowerBatchRoots oracle.compression oracle.permutation rightRecords
      (fun _ => none) = some rightRoots)
    (leftCap : capDecode oracle.compression (capKnownView leftRoots 8 0) leftProof =
      some (root, []))
    (rightCap : capDecode oracle.compression (capKnownView rightRoots 8 0) rightProof =
      some (root, []))
    (leftRecord rightRecord : CapLowerRecord)
    (leftMember : leftRecord ∈ leftRecords) (rightMember : rightRecord ∈ rightRecords)
    (sameIndex : leftRecord.index = rightRecord.index)
    (different : leftRecord.value ≠ rightRecord.value) :
    (∃ replies calls,
      oracle.run (capProbePair leftRecords rightRecords leftProof rightProof root) =
        pure (replies, calls) ∧ ReplyCollision replies) ∨
    LeafCollision (s3LeafReplies oracle.permutation
      (capRecordLeaves leftRecords ++ capRecordLeaves rightRecords)) := by
  obtain ⟨leftCapInputs, rightCapInputs, leftRun, rightRun, outcome⟩ :=
    cap_batch_collision oracle leftRecords rightRecords leftProof rightProof root
      leftRoots rightRoots leftLower rightLower leftCap rightCap
      leftRecord rightRecord leftMember rightMember sameIndex different
  rcases outcome with leaves | collision
  · exact Or.inr leaves
  · obtain ⟨leftInputs, leftCalls, leftAccepted, leftBound⟩ :=
      cap_accepted_replay oracle leftRecords leftProof root leftRoots leftLower leftCap
    obtain ⟨rightInputs, rightCalls, rightAccepted, rightBound⟩ :=
      cap_accepted_replay oracle rightRecords rightProof root rightRoots rightLower rightCap
    have leftSame := cap_check_replay_trace_unique oracle _ _ leftInputs _ leftCalls
      leftRun leftAccepted
    have rightSame := cap_check_replay_trace_unique oracle _ _ rightInputs _ rightCalls
      rightRun rightAccepted
    left
    apply cap_probe_pair_collision oracle _ _ _ _ _ _ _ _ _ leftRun rightRun
    · rw [leftSame]
      exact leftBound
    · rw [rightSame]
      exact rightBound
    · exact collision

/-! ### The two budgeted searches -/

/-- Run the query-limited adversary, then the paid compression probe of its claim. -/
noncomputable def s3BoundedCollisionSearch
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (adversary : Scheme.Adversary) (budget : Nat) : OracleComp World CompressionReplies := do
  let outcome ← limitPublicQueries adversary budget
  match outcome with
  | none => pure []
  | some claim => probe claim

/-- Replay cap for the leaf search: both openings together have at most `2 * LENGTH` records. -/
def s3LeafExtra : Nat := 2 ^ 25

/-- Run the query-limited adversary, then replay the leaves of its claim. -/
noncomputable def s3BoundedLeafSearch (leaves : Scheme.Claim → List (BitVec 256 × Entry))
    (adversary : Scheme.Adversary) (budget : Nat) : OracleComp World LeafReplies :=
  s3LeafSearch (Option.map leaves <$> limitPublicQueries adversary budget) s3LeafExtra

theorem s3_bounded_collision_search_bound
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (probeBound : ∀ claim, (probe claim).IsTotalQueryBound (2*capReplayCeiling))
    (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (s3BoundedCollisionSearch probe adversary budget)
      (budget+2*capReplayCeiling) := by
  unfold s3BoundedCollisionSearch
  apply public_query_bound_bind (limit_public_bound _ _)
  intro outcome
  cases outcome with
  | none => trivial
  | some claim => exact public_query_bound_of_total (probeBound claim)

theorem s3_search_reply_collision_in_cache (permutation : Perm)
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (probeCache : ∀ (claim : Scheme.Claim) (cache : CompressionCache)
      (result : CompressionReplies × CompressionCache),
      result ∈ support (compressionRun permutation (probe claim) cache) →
      ∀ reply ∈ result.1, result.2 reply.1=some reply.2)
    (adversary : Scheme.Adversary) (budget : Nat)
    (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation
      (s3BoundedCollisionSearch probe adversary budget) ∅))
    (collision : ReplyCollision result.1) : CacheHasCollision result.2 := by
  rw [s3BoundedCollisionSearch,compression_run_bind] at reached
  obtain ⟨⟨outcome,cache⟩,_,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
  cases outcome with
  | none =>
    dsimp only at tail
    rw [compression_run_pure] at tail
    have same := eq_of_mem_support_pure ([],cache) tail
    subst result
    obtain ⟨_,impossible,_⟩ := collision
    simp at impossible
  | some claim =>
    dsimp only at tail
    have stored := probeCache claim cache result tail
    obtain ⟨first,firstMember,second,secondMember,different,equal⟩ := collision
    exact ⟨first.1,second.1,first.2,second.2,different,
      stored first firstMember,stored second secondMember,heq_of_eq equal⟩

/-- Bound the compression detector for every fixed permutation; its inverse
remains available, as do unrestricted private coins. -/
theorem s3_fixed_permutation_search_bound (permutation : Perm)
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (probeBound : ∀ claim, (probe claim).IsTotalQueryBound (2*capReplayCeiling))
    (probeCache : ∀ (permutation : Perm) (claim : Scheme.Claim) (cache : CompressionCache)
      (result : CompressionReplies × CompressionCache),
      result ∈ support (compressionRun permutation (probe claim) cache) →
      ∀ reply ∈ result.1, result.2 reply.1=some reply.2)
    (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((ReplyCollision) <$> ((($ᵗ Compression) >>= fun compression =>
      fixedOracleRun ⟨compression, permutation⟩
        (s3BoundedCollisionSearch probe adversary budget))))) ≤
      ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 / 2 ^ 256 := by
  have equivalence := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty permutation
      (s3BoundedCollisionSearch probe adversary budget))).prEvent_eq ReplyCollision
  simp only [prEvent_map, Function.comp_def] at equivalence
  rw [← equivalence]
  have detected : (prEvent ((fun result => ReplyCollision result.1) <$> (compressionRun permutation (s3BoundedCollisionSearch probe adversary budget) ∅))) ≤
      (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation (s3BoundedCollisionSearch probe adversary budget) ∅))) :=
    prEvent_mono_of_support _ _ _ fun result reached collision =>
      s3_search_reply_collision_in_cache permutation probe (probeCache permutation)
        adversary budget result reached collision
  have birthday := compression_collision_bound permutation
    (s3BoundedCollisionSearch probe adversary budget)
    (budget + (2*capReplayCeiling))
    (s3_bounded_collision_search_bound probe probeBound adversary budget)
  have loose : (((budget + (2*capReplayCeiling)) * (budget + (2*capReplayCeiling) - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) ≤
      ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 / 2 ^ 256 := by
    apply ENNReal.div_le_div
    · have product : (budget + (2*capReplayCeiling)) * (budget + (2*capReplayCeiling) - 1) ≤ (budget + (2*capReplayCeiling)) ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast product
    · calc (2 : ENNReal) ^ 256 ≤ 2 ^ 256 + 2 ^ 256 := le_self_add
           _ = 2 * 2 ^ 256 := (two_mul _).symm
  exact detected.trans (birthday.trans loose)

/-- Averaging over the independently sampled permutation preserves the bound. -/
theorem s3_sampled_search_bound
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (probeBound : ∀ claim, (probe claim).IsTotalQueryBound (2*capReplayCeiling))
    (probeCache : ∀ (permutation : Perm) (claim : Scheme.Claim) (cache : CompressionCache)
      (result : CompressionReplies × CompressionCache),
      result ∈ support (compressionRun permutation (probe claim) cache) →
      ∀ reply ∈ result.1, result.2 reply.1=some reply.2)
    (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
      fixedOracleRun oracle (s3BoundedCollisionSearch probe adversary budget))))) ≤
      ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 / 2 ^ 256 := by
  have swapped := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
    (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩
      (s3BoundedCollisionSearch probe adversary budget))
  have probabilities := (EvalDistEq.of_evalDist_eq swapped).prEvent_eq ReplyCollision
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rw [probabilities]
  apply prEvent_bind_le_of_forall_le_of_support
  intro permutation _
  exact s3_fixed_permutation_search_bound permutation probe probeBound probeCache adversary budget

/-- The leaf search's first stage is the query-limited adversary itself. -/
theorem s3_leaf_first_bound (leaves : Scheme.Claim → List (BitVec 256 × Entry))
    (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (Option.map leaves <$> limitPublicQueries adversary budget) budget := by
  simpa only [PublicQueryBound, isQueryBound_map_iff] using limit_public_bound adversary budget

/-- The leaf bound for every fixed compression function survives averaging over
the independently sampled compression function. -/
theorem s3_sampled_leaf_search_bound (leafBound : S3LeafCollisionBound)
    (leaves : Scheme.Claim → List (BitVec 256 × Entry))
    (adversary : Scheme.Adversary) (budget : Nat) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent (LeafCollision <$> (Oracle.sample >>= fun oracle =>
      fixedOracleRun oracle (s3BoundedLeafSearch leaves adversary budget)))) ≤
      ((budget : ENNReal) + 2 * (s3LeafExtra : ENNReal)) ^ 2 / 2 ^ 256 +
        (budget : ENNReal) / 2 ^ 127 := by
  simp only [Oracle.sample, bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support
  intro compression _
  exact leafBound compression _ budget s3LeafExtra (s3_leaf_first_bound leaves adversary budget)
    (by simpa [BINDING_SECURITY_BITS] using small) (by norm_num [s3LeafExtra])

/-! ### Arithmetic: both detectors fit the 120-bit target -/

theorem s3_detector_arithmetic (q : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) :
    (q + 2*capReplayCeiling)^2 + ((q + 2*s3LeafExtra)^2 + q*2^129) ≤ q*2^136 := by
  have square := Nat.mul_le_mul_left q small
  norm_num [capReplayCeiling, s3LeafExtra, LENGTH, LOG_LENGTH] at *
  nlinarith

theorem s3_binding_sum_le_target (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 / 2 ^ 256 +
      (((budget : ENNReal) + 2 * (s3LeafExtra : ENNReal)) ^ 2 / 2 ^ 256 +
        (budget : ENNReal) / 2 ^ 127) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have arithmetic := s3_detector_arithmetic budget positive
    (by simpa [BINDING_SECURITY_BITS] using small)
  have castBound : ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 +
      (((budget : ENNReal) + 2 * (s3LeafExtra : ENNReal)) ^ 2 + (budget : ENNReal) * 2 ^ 129) ≤
      (budget : ENNReal) * 2 ^ 136 := by
    exact_mod_cast arithmetic
  have unary : (budget : ENNReal) / 2 ^ 127 = (budget : ENNReal) * 2 ^ 129 / 2 ^ 256 := by
    rw [show (2 : ENNReal) ^ 256 = 2 ^ 127 * 2 ^ 129 by rw [← pow_add]]
    exact (ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)).symm
  rw [unary, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  calc
    _ ≤ (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 := ENNReal.div_le_div_right castBound _
    _ = _ := by
      change (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 = (budget : ENNReal) / 2 ^ 120
      rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-! ### Fixed oracle: a win is caught by one of the two searches -/

theorem s3_binding_fixed_le_search (wins : Oracle → Scheme.Claim → Prop)
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (leaves : Scheme.Claim → List (BitVec 256 × Entry))
    (leavesShort : ∀ claim, (leaves claim).length ≤ s3LeafExtra)
    (oracle : Oracle)
    (extract : ∀ claim, wins oracle claim →
      (∃ replies calls, oracle.run (probe claim) = pure (replies, calls) ∧
        ReplyCollision replies) ∨
      LeafCollision (s3LeafReplies oracle.permutation (leaves claim)))
    (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => wins oracle result.1 ∧
      result.2≤budget) <$> oracle.run adversary)) ≤
    (prEvent (ReplyCollision <$> fixedOracleRun oracle
      (s3BoundedCollisionSearch probe adversary budget))) +
    (prEvent (LeafCollision <$> fixedOracleRun oracle
      (s3BoundedLeafSearch leaves adversary budget))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (wins oracle)]
  simp only [fixedOracleRun,prEvent_map,Function.comp_def,s3BoundedCollisionSearch,
    s3BoundedLeafSearch,s3LeafSearch,bind_map_left,oracle_run_bind]
  rw [OracleComp.prEvent_bind_eq_tsum,OracleComp.prEvent_bind_eq_tsum,
    OracleComp.prEvent_eq_tsum_ite,← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  rintro ⟨outcome,calls⟩
  cases outcome with
  | none => simp [oracle_run_pure,prEvent_pure]
  | some claim =>
    by_cases winning : wins oracle claim
    · rcases extract claim winning with ⟨replies,probeCalls,run,collision⟩ | collision
      · refine le_trans ?_ le_self_add
        rw [run]
        simp [prEvent_pure,winning,collision]
      · have leafRun : oracle.run (probeLeaves ((leaves claim).take s3LeafExtra)) =
            pure (s3LeafReplies oracle.permutation (leaves claim), 2 * (leaves claim).length) := by
          rw [List.take_of_length_le (leavesShort claim), probe_leaves_run]
          rfl
        refine le_trans ?_ le_add_self
        simp only [Option.map_some]
        rw [leafRun]
        simp [prEvent_pure,winning,collision]
    · simp [winning]

/-! ### Binding from the fixed-oracle extraction -/

/-- Binding for any scheme whose winning claims are caught, for every fixed
oracle, by the compression probe or by a collision among the replayed leaves. -/
theorem s3_cap_scheme_binding (scheme : Scheme)
    (probe : Scheme.Claim → OracleComp World CompressionReplies)
    (leaves : Scheme.Claim → List (BitVec 256 × Entry))
    (probeBound : ∀ claim, (probe claim).IsTotalQueryBound (2*capReplayCeiling))
    (probeCache : ∀ (permutation : Perm) (claim : Scheme.Claim) (cache : CompressionCache)
      (result : CompressionReplies × CompressionCache),
      result ∈ support (compressionRun permutation (probe claim) cache) →
      ∀ reply ∈ result.1, result.2 reply.1=some reply.2)
    (leavesShort : ∀ claim, (leaves claim).length ≤ s3LeafExtra)
    (extract : ∀ oracle claim, scheme.Breaks oracle claim →
      (∃ replies calls, oracle.run (probe claim) = pure (replies, calls) ∧
        ReplyCollision replies) ∨
      LeafCollision (s3LeafReplies oracle.permutation (leaves claim)))
    (leafBound : S3LeafCollisionBound) : scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · apply le_trans (prEvent_le_one _)
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
      (Or.inl (by finiteness))).mpr
    simpa using (show ((2^BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ budget from
      Nat.cast_le.mpr large)
  · have reduction :
        (prEvent ((fun (oracle, claim, calls) => scheme.Breaks oracle claim ∧ calls ≤ budget) <$> (Scheme.bindingGame adversary))) ≤
        (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (s3BoundedCollisionSearch probe adversary budget))))) +
        (prEvent (LeafCollision <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (s3BoundedLeafSearch leaves adversary budget)))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum,
        OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro oracle
      rw [← mul_add]
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using
        s3_binding_fixed_le_search scheme.Breaks probe leaves leavesShort oracle
          (extract oracle) adversary budget
    exact reduction.trans ((add_le_add
      (s3_sampled_search_bound probe probeBound probeCache adversary budget)
      (s3_sampled_leaf_search_bound leafBound leaves adversary budget (by omega))).trans
      (s3_binding_sum_le_target budget positive (by omega)))

/-- Both openings of a claim replay at most `2 * LENGTH = s3LeafExtra` leaves. -/
theorem s3_pair_leaves_short (leftRecords rightRecords : List CapLowerRecord)
    (leftBound : leftRecords.length ≤ LENGTH) (rightBound : rightRecords.length ≤ LENGTH) :
    (capRecordLeaves leftRecords ++ capRecordLeaves rightRecords).length ≤ s3LeafExtra := by
  rw [List.length_append, cap_record_leaves_length, cap_record_leaves_length]
  have size : 2 * LENGTH = s3LeafExtra := by norm_num [s3LeafExtra, LENGTH, LOG_LENGTH]
  omega

/-- The cap instance: the probe is the paid pair probe of the two parsed batches
and the replayed leaves are the (salt, value) pairs of all their records. -/
theorem s3_cap_pair_binding (scheme : Scheme)
    (leftRecords rightRecords : Scheme.Claim → List CapLowerRecord)
    (leftProof rightProof : Scheme.Claim → List Digest)
    (leftBound : ∀ claim, (leftRecords claim).length ≤ LENGTH)
    (rightBound : ∀ claim, (rightRecords claim).length ≤ LENGTH)
    (extract : ∀ oracle claim, scheme.Breaks oracle claim →
      (∃ replies calls,
        oracle.run (capProbePair (leftRecords claim) (rightRecords claim)
          (leftProof claim) (rightProof claim) claim.root) = pure (replies, calls) ∧
        ReplyCollision replies) ∨
      LeafCollision (s3LeafReplies oracle.permutation
        (capRecordLeaves (leftRecords claim) ++ capRecordLeaves (rightRecords claim))))
    (leafBound : S3LeafCollisionBound) : scheme.Binding :=
  s3_cap_scheme_binding scheme
    (fun claim => capProbePair (leftRecords claim) (rightRecords claim)
      (leftProof claim) (rightProof claim) claim.root)
    (fun claim => capRecordLeaves (leftRecords claim) ++ capRecordLeaves (rightRecords claim))
    (fun claim => cap_probe_pair_ceiling _ _ _ _ _ (leftBound claim) (rightBound claim))
    (fun permutation _ cache result reached =>
      cap_probe_pair_cache permutation _ _ _ _ _ cache result reached)
    (fun claim => s3_pair_leaves_short _ _ (leftBound claim) (rightBound claim))
    extract leafBound

end CommitGolfCandidate
