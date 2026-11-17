import CommitGolfCandidate.NonceEncoding
import CommitGolfCandidate.HidingLeaf

/-! Hiding of the padded nonce through the actual eight-compression reference leaf.
Prior cached cells and all adaptive continuation queries are charged explicitly. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleComp.DeferredSampling
local instance noncePrivacyDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
theorem nonce_guess_probability (guess : Digest) :
    prEvent ((fun nonce : Nonce192 => expandNonce192 nonce=guess) <$> ($ᵗ Nonce192)) ≤
      1/(2^192 : ENNReal) := by
  by_cases present : ∃ nonce, expandNonce192 nonce=guess
  · obtain ⟨nonce,equal⟩ := present
    have predicate : (fun candidate : Nonce192 => expandNonce192 candidate=guess)=
        (fun candidate => candidate=nonce) := by
      funext candidate
      exact propext ⟨fun same => expand_nonce_injective (same.trans equal.symm),fun same => by subst candidate;exact equal⟩
    rw [predicate,SampleableType.prEvent_uniformSample_eq_singleton]
    norm_num
  · have predicate : (fun nonce : Nonce192 => expandNonce192 nonce=guess)=(fun _ => False) := by
      funext nonce
      exact propext ⟨fun same => present ⟨nonce,same⟩,False.elim⟩
    rw [predicate]
    simp

theorem nonce_trace_hit_probability (trace : List (BitVec 512)) :
    prEvent ((fun nonce : Nonce192 =>
      trace.any (fun input => decide (input.extractLsb' 0 256=expandNonce192 nonce))=true) <$> ($ᵗ Nonce192)) ≤
      (trace.length : ENNReal)/2^192 := by
  classical
  have event : (fun nonce : Nonce192 =>
      trace.any (fun input => decide (input.extractLsb' 0 256=expandNonce192 nonce))=true)=
      (fun nonce => ∃ input∈trace.toFinset,expandNonce192 nonce=input.extractLsb' 0 256) := by
    funext nonce
    apply propext
    constructor
    · intro hit
      obtain ⟨input,member,equal⟩ := List.any_eq_true.mp hit
      exact ⟨input,List.mem_toFinset.mpr member,(of_decide_eq_true equal).symm⟩
    · rintro ⟨input,member,equal⟩
      exact List.any_eq_true.mpr ⟨input,List.mem_toFinset.mp member,decide_eq_true equal.symm⟩
  rw [event]
  have union := prEvent_exists_finset_le trace.toFinset ($ᵗ Nonce192)
    (fun input nonce => expandNonce192 nonce=input.extractLsb' 0 256)
  refine union.trans ?_
  calc
    _ ≤ ∑ input∈trace.toFinset, (1/(2^192 : ENNReal)) := by
      apply Finset.sum_le_sum
      intro input member
      exact nonce_guess_probability _
    _ = (trace.toFinset.card : ENNReal)/2^192 := by
      simp [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
    _ ≤ _ := ENNReal.div_le_div_right (Nat.cast_le.mpr (List.toFinset_card_le trace)) _

theorem nonce_query_hit_bound (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    prEvent ((fun result : α × Unit × Bool => result.2.2=true) <$>
      (($ᵗ Nonce192) >>= fun nonce => flaggedRun oracle (marksSalt (expandNonce192 nonce)) computation)) ≤
      (budget : ENNReal)/2^192 := by
  letI : MeasurableSpace (α × Unit × Bool) := ⊤
  have reordered :
      𝒟[($ᵗ Nonce192) >>= fun nonce => flaggedRun oracle (marksSalt (expandNonce192 nonce)) computation]=
      𝒟[do let traced ← fixedOracleRun oracle (traceCompression computation)
           let nonce ← $ᵗ Nonce192
           pure (traced.1,(),traced.2.any (fun input => decide (input.extractLsb' 0 256=expandNonce192 nonce)))] := by
    simp only [flagged_run_trace,Bool.false_or,map_eq_bind_pure_comp]
    exact distribution_bind_comm ($ᵗ Nonce192) (fixedOracleRun oracle (traceCompression computation)) _
  have probability := (EvalDistEq.of_evalDist_eq reordered).prEvent_eq (fun result => result.2.2=true)
  rw [probability]
  apply prEvent_bind_le_of_forall_le_of_support
  intro traced reached
  rw [bind_pure_comp,prEvent_map]
  refine (nonce_trace_hit_probability traced.2).trans ?_
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr
    (trace_run_length oracle computation budget bounded traced reached)) _

theorem nonce_reprogram_distance (oracle : Oracle) (block answer : Digest)
    {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    measureTVDist
      (($ᵗ Nonce192) >>= fun _ => fixedOracleRun oracle computation)
      (($ᵗ Nonce192) >>= fun nonce =>
        fixedOracleRun (programCompression oracle (block ++ expandNonce192 nonce) answer) computation) ≤
      ((budget : ENNReal)/2^192).toReal := by
  have distance := distance_bind_le_averaged_bad ($ᵗ Nonce192)
    (fun _ => fixedOracleRun oracle computation)
    (fun nonce => fixedOracleRun (programCompression oracle (block ++ expandNonce192 nonce) answer) computation)
    (fun nonce => flaggedRun oracle (marksSalt (expandNonce192 nonce)) computation) (fun nonce => by
      have result := reprogram_compression_distance oracle (block ++ expandNonce192 nonce) answer computation
      simpa only [BitVec.extractLsb'_append_eq_right] using result)
  exact distance.trans (ENNReal.toReal_mono (by finiteness)
    (nonce_query_hit_bound oracle computation budget bounded))

/-! The first compression produces a full256-bit oracle reply; only its initial nonce has192 bits. -/
theorem nonce_compression_programming (permutation : Perm) (block : Digest)
    {α : Type} (next : Digest → OracleComp World α) :
    𝒟[do let salt ← $ᵗ Nonce192
         let answer ← $ᵗ Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ expandNonce192 salt) answer)
           (next answer)] =
    𝒟[do let table ← $ᵗ Compression
         let salt ← $ᵗ Nonce192
         fixedOracleRun ⟨table, permutation⟩ (next (combine table (expandNonce192 salt) block))] := by
  trans 𝒟[do let salt ← $ᵗ Nonce192
              let table ← $ᵗ Compression
              fixedOracleRun ⟨table, permutation⟩ (next (combine table (expandNonce192 salt) block))]
  · exact _root_.evalDist_bind_congr _ _ _ (fun salt =>
      compression_answer_programming permutation (block ++ expandNonce192 salt) next)
  · exact distribution_bind_comm _ _ _

/-- A salted compression output hides its block against a bounded adaptive
continuation, at cost q/2^192. The salt is private; the output is public. -/
theorem nonce_compression_distance (permutation : Perm) (block : Digest)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Nonce192
          fixedOracleRun ⟨table, permutation⟩ (next (combine table (expandNonce192 salt) block)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next answer)) ≤
      ((budget : ENNReal) / 2^192).toReal := by
  let ideal : ProbComp α := do
    let answer ← $ᵗ Digest
    let table ← $ᵗ Compression
    let _salt ← $ᵗ Nonce192
    fixedOracleRun ⟨table, permutation⟩ (next answer)
  let programmed : ProbComp α := do
    let answer ← $ᵗ Digest
    let table ← $ᵗ Compression
    let salt ← $ᵗ Nonce192
    fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ expandNonce192 salt) answer)
      (next answer)
  have distance : measureTVDist ideal programmed ≤ ((budget : ENNReal) / 2^192).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Digest) _ _ (by positivity)
    intro answer
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    exact nonce_reprogram_distance ⟨table, permutation⟩ block answer (next answer)
      budget (bounded answer)
  have ideal_eq : 𝒟[ideal] =
      𝒟[do let table ← $ᵗ Compression
           let answer ← $ᵗ Digest
           fixedOracleRun ⟨table, permutation⟩ (next answer)] := by
    unfold ideal
    trans 𝒟[do let answer ← $ᵗ Digest
                let table ← $ᵗ Compression
                fixedOracleRun ⟨table, permutation⟩ (next answer)]
    · apply _root_.evalDist_bind_congr
      intro answer
      apply _root_.evalDist_bind_congr
      intro table
      exact OracleComp.evalDist_bind_const _ _
    · exact distribution_bind_comm _ _ _
  have programmed_eq : 𝒟[programmed] =
      𝒟[do let table ← $ᵗ Compression
           let salt ← $ᵗ Nonce192
           fixedOracleRun ⟨table, permutation⟩ (next (combine table (expandNonce192 salt) block))] := by
    unfold programmed
    trans 𝒟[do let salt ← $ᵗ Nonce192
                let answer ← $ᵗ Digest
                let table ← $ᵗ Compression
                fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ expandNonce192 salt) answer)
                  (next answer)]
    · trans 𝒟[do let answer ← $ᵗ Digest
                  let salt ← $ᵗ Nonce192
                  let table ← $ᵗ Compression
                  fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ expandNonce192 salt) answer)
                    (next answer)]
      · exact _root_.evalDist_bind_congr _ _ _ (fun _ => distribution_bind_comm _ _ _)
      · exact distribution_bind_comm _ _ _
    · exact nonce_compression_programming permutation block next
  rw [measureTVDist_comm] at distance
  simpa only [measureTVDist, ideal_eq, programmed_eq] using distance


theorem nonce_cached_hit_bound (cache : CompressionCache) (keys : Finset (BitVec 512))
    (covered : ∀ input, cache input ≠ none → input ∈ keys) (block : Digest) :
    (prEvent ((fun salt : Nonce192 => cache (block ++ expandNonce192 salt) ≠ none) <$> (($ᵗ Nonce192)))) ≤
      (keys.card : ENNReal) / 2^192 := by
  have included :
      (prEvent ((fun salt : Nonce192 => cache (block ++ expandNonce192 salt) ≠ none) <$> (($ᵗ Nonce192)))) ≤
      (prEvent ((fun salt : Nonce192 => keys.toList.any
        (fun input => decide (input.extractLsb' 0 256 = expandNonce192 salt)) = true) <$> (($ᵗ Nonce192)))) := by
    apply prEvent_mono_of_support
    intro salt _ hit
    apply List.any_eq_true.mpr
    exact ⟨block ++ expandNonce192 salt, Finset.mem_toList.mpr (covered _ hit),
      decide_eq_true (BitVec.extractLsb'_append_eq_right)⟩
  exact included.trans (by simpa only [Finset.length_toList] using
    nonce_trace_hit_probability keys.toList)

/-- The single-compression hiding step remains valid after fixing a prior cache.
Its loss is the continuation's query budget plus the number of cached inputs,
all divided by 2^192. Thus prior queries are charged rather than ignored. -/
theorem nonce_cached_compression_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec 512)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (block : Digest) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Nonce192
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (combine oracle.compression (expandNonce192 salt) block)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)) ≤
      ((keys.card + budget : Nat) : ℝ) / 2^192 := by
  let intermediate : ProbComp α := do
    let table ← $ᵗ Compression
    let salt ← $ᵗ Nonce192
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (combine table (expandNonce192 salt) block))
  have prior : measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Nonce192
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (combine oracle.compression (expandNonce192 salt) block)))
      intermediate ≤ ((keys.card : ENNReal) / 2^192).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ Nonce192) _ _
      (fun salt => cache (block ++ expandNonce192 salt) ≠ none) ?_).trans ?_
    · intro salt unqueried
      have empty : cache (block ++ expandNonce192 salt) = none := Classical.not_not.mp unqueried
      have same : combine (tableExtending cache table) (expandNonce192 salt) block = combine table (expandNonce192 salt) block := by
        change (cache (block ++ expandNonce192 salt)).getD (table (block ++ expandNonce192 salt)) = table (block ++ expandNonce192 salt)
        rw [empty]
        rfl
      dsimp only
      rw [same]
    · exact ENNReal.toReal_mono (by finiteness) (nonce_cached_hit_bound cache keys covered block)
  have after := nonce_compression_distance permutation block
    (fun answer => cacheAnswers cache (next answer)) budget
    (fun answer => cache_answers_bound cache (next answer) budget (bounded answer))
  simp only [fixed_cache_answers] at after
  refine ((measureTVDist_triangle _ intermediate _).trans (add_le_add prior after)).trans ?_
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Nat.cast_add]
  exact le_of_eq (add_div _ _ _).symm


theorem nonce_cached_chain_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec 512)) (covered : ∀ input,cache input≠none → input∈keys)
    (first : Digest) (rest : List Digest) {α : Type}
    (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer,PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨tableExtending cache table,permutation⟩
            (next ((first::rest).foldl
              (fun state block => combine (tableExtending cache table) state block) (expandNonce192 nonce))))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table,permutation⟩ (next answer)) ≤
      ((rest.length+1 : Nat) : ℝ) * ((keys.card+budget+rest.length+1 : Nat) : ℝ)/2^192 := by
  let continuation : Digest → OracleComp World α := fun state => hashBlocks rest state >>= next
  have continued : ∀ state,PublicQueryBound (continuation state) (rest.length+budget) :=
    fun state => public_query_bound_bind (hash_blocks_bound rest state) bounded
  have firstBound := nonce_cached_compression_distance permutation cache keys covered
    first continuation (rest.length+budget) continued
  simp only [continuation,fixed_hash_blocks] at firstBound
  have restBound := cached_salted_chain_distance permutation cache keys covered rest next budget bounded
  have relaxed := restBound.trans (show
      (rest.length : ℝ)*((keys.card+budget+rest.length : Nat) : ℝ)/2^256 ≤
      (rest.length : ℝ)*((keys.card+budget+rest.length : Nat) : ℝ)/2^192 by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    norm_num)
  have triangle := measureTVDist_triangle (m := ProbComp)
      (do let table ← $ᵗ Compression
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨tableExtending cache table,permutation⟩
            (next ((first::rest).foldl
              (fun state block => combine (tableExtending cache table) state block) (expandNonce192 nonce))))
      (do let table ← $ᵗ Compression
          let state ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table,permutation⟩
            (next (rest.foldl (fun state block => combine (tableExtending cache table) state block) state)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table,permutation⟩ (next answer))
  simp only [List.foldl_cons] at triangle ⊢
  have combined := triangle.trans (add_le_add firstBound relaxed)
  refine combined.trans ?_
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [Nat.cast_add,Nat.cast_one]
  have nonnegative : (0 : ℝ)≤rest.length := Nat.cast_nonneg _
  nlinarith

theorem nonce_cached_leaf_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec 512)) (covered : ∀ input,cache input≠none → input∈keys)
    (value : Entry) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer,PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let nonce ← $ᵗ Nonce192
          fixedOracleRun ⟨tableExtending cache table,permutation⟩
            (next (leafDigest (tableExtending cache table) (expandNonce192 nonce) value)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table,permutation⟩ (next answer)) ≤
      8*((keys.card+budget+8 : Nat) : ℝ)/2^192 := by
  have run := nonce_cached_chain_distance permutation cache keys covered
    (value.extractLsb' 0 256)
    ((List.range 7).map fun block => value.extractLsb' (256*(block+1)) 256) next budget bounded
  have blocks : (List.range 8).map (fun block => value.extractLsb' (256*block) 256)=
      value.extractLsb' 0 256 ::
        (List.range 7).map (fun block => value.extractLsb' (256*(block+1)) 256) := by rfl
  simpa only [leafDigest,←List.foldl_map,blocks,List.length_map,List.length_range,Nat.add_assoc,Nat.reduceAdd,Nat.cast_ofNat] using run

theorem nonce_leaf_indistinguishable (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec 512)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Entry) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Nonce192
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (leafDigest (tableExtending cache table) (expandNonce192 salt) left)))
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Nonce192
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (leafDigest (tableExtending cache table) (expandNonce192 salt) right))) ≤
      16 * ((keys.card + budget + 8 : Nat) : ℝ) / 2^192 := by
  have leftBound := nonce_cached_leaf_distance permutation cache keys covered left next budget bounded
  have rightBound := nonce_cached_leaf_distance permutation cache keys covered right next budget bounded
  rw [measureTVDist_comm] at rightBound
  have triangle := measureTVDist_triangle (m := ProbComp)
    (do let table ← $ᵗ Compression
        let salt ← $ᵗ Nonce192
        fixedOracleRun ⟨tableExtending cache table, permutation⟩
          (next (leafDigest (tableExtending cache table) (expandNonce192 salt) left)))
    (do let table ← $ᵗ Compression
        let answer ← $ᵗ Digest
        fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer))
    (do let table ← $ᵗ Compression
        let salt ← $ᵗ Nonce192
        fixedOracleRun ⟨tableExtending cache table, permutation⟩
          (next (leafDigest (tableExtending cache table) (expandNonce192 salt) right)))
  refine (triangle.trans (add_le_add leftBound rightBound)).trans ?_
  exact le_of_eq (by ring)



end CommitGolfCandidate
