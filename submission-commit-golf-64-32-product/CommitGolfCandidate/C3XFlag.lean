import CommitGolfCandidate.C3XLog
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.TwoPermutationBindingBridge

/-! # The compression side of the cross-oracle event

The permutation is fixed and the compression function is sampled lazily (`compressionRun`,
CompressionROM). The flag of `scan` is raised by a compression call whose reply was not seen
before and is already the `t3` field of an input returned by an inverse call.

A reply that repeats a cached answer was seen, so only a fresh draw can raise the flag, and it
does so for at most one value per earlier inverse call. Summing over the calls of the program
gives `Q (Q - 1) / 2 / 2^256` for `Q` public calls (`flag_bound`). The induction is that of
`compression_collision_bound_from_cache`, with the list of targets in place of the cached keys;
the marker calls of the marked run are permutation calls and cost nothing here. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp OracleSpec OracleComp.DeferredSampling

set_option autoImplicit false
set_option maxRecDepth 8192

theorem compression_run_map (permutation : Perm) {α β : Type} (f : α → β)
    (computation : OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation (f <$> computation) cache =
      (fun result : α × CompressionCache => (f result.1, result.2)) <$>
        compressionRun permutation computation cache := by
  simp [compressionRun, simulateQ_map, StateT.run_map]

theorem compression_run_compress_some (permutation : Perm) {α : Type}
    (input : CompressionSpec.Domain) (next : CompressionSpec.Range input → OracleComp World α)
    (cache : CompressionCache) (answer : CompressionSpec.Range input)
    (stored : cache input = some answer) :
    compressionRun permutation
        ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= next) cache =
      compressionRun permutation (next answer) cache := by
  rw [compression_run_compress, stored]

theorem compression_run_compress_none (permutation : Perm) {α : Type}
    (input : CompressionSpec.Domain) (next : CompressionSpec.Range input → OracleComp World α)
    (cache : CompressionCache) (missing : cache input = none) :
    compressionRun permutation
        ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= next) cache =
      (($ᵗ CompressionSpec.Range input) >>= fun answer =>
        compressionRun permutation (next answer) (cache.cacheQuery input answer)) := by
  rw [compression_run_compress, missing]

/-- A uniform 256-bit value is one of `n` listed values with probability at most `n / 2^256`. -/
theorem fresh_target_bound (targets : List (BitVec 256)) :
    Pr{let answer ← $ᵗ (BitVec 256)}[answer ∈ targets] ≤ (targets.length : ENNReal) / 2 ^ 256 := by
  rw [SampleableType.prEvent_uniformSample]
  have cardinal : Fintype.card (BitVec 256) = 2 ^ 256 := by simp
  rw [cardinal]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  have count : (Finset.univ.filter fun answer : BitVec 256 => answer ∈ targets).card ≤
      targets.length :=
    (Finset.card_le_card fun answer hit =>
      List.mem_toFinset.2 (Finset.mem_filter.1 hit).2).trans (List.toFinset_card_le targets)
  exact_mod_cast count

/-- The sum of the per-call charges: the current call pays for the targets known now, the later
calls for at most one more each. -/
theorem flag_budget_split (budget known : Nat) (positive : 1 ≤ budget) :
    (known : ENNReal) / 2 ^ 256 +
        ∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256 =
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 := by
  conv_rhs => rw [show budget = (budget - 1) + 1 from by omega]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro step _
  rw [show known + 1 + step = known + (step + 1) from by omega]

/-- **The flag is rarely raised**, for every fixed permutation. `known` bounds the targets of the
starting state; every cached answer of the starting cache counts as seen. -/
theorem flag_bound_from_cache (permutation : Perm) {α : Type} (program : OracleComp World α)
    (budget known : Nat) (bounded : PublicQueryBound program budget)
    (cache : CompressionCache) (state : ScanState) (clear : ¬ state.flag)
    (cached : ∀ input reply, cache input = some reply → reply ∈ state.seen)
    (size : state.targets.length ≤ known) :
    Pr{let result ← compressionRun permutation (markedRows program) cache}[
        (scan state result.1.2).flag] ≤
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 := by
  induction program using OracleComp.inductionOn generalizing budget known cache state with
  | pure value =>
    rw [marked_rows_pure, compression_run_pure]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ ?_) zero_le
    intro result reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact clear
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [marked_rows_coins, compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro answer _
      exact ih answer budget known
        (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache state clear cached size
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have split := flag_budget_split budget known positive
      have later : ∑ step ∈ Finset.range (budget - 1),
            ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256 ≤
          ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 :=
        le_of_le_of_eq le_add_self split
      rcases publicQuery with input | permQuery
      · rw [marked_rows_compress]
        rcases stored : cache input with _ | answer
        · rw [compression_run_compress_none permutation input _ cache stored]
          have fresh : Pr{let answer ← $ᵗ (CompressionSpec.Range input)}[
              answer ∈ state.targets] ≤ (known : ENNReal) / 2 ^ 256 :=
            (fresh_target_bound state.targets).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ answer ∈ state.targets →
              Pr{let result ← compressionRun permutation
                  ((liftM (World.query (.inr (.inr (.inl (c3Marker answer))))) :
                      OracleComp World _) >>= fun mark =>
                    (fun result : α × List MarkedRow =>
                      (result.1, MarkedRow.compression input answer mark :: result.2)) <$>
                        markedRows (next answer))
                  (cache.cacheQuery input answer)}[(scan state result.1.2).flag] ≤
                ∑ step ∈ Finset.range (budget - 1),
                  ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256 := by
            intro answer _ safe
            rw [compression_run_permute, compression_run_map, prEvent_map]
            refine ih answer (budget - 1) (known + 1) (tails answer)
              (cache.cacheQuery input answer)
              (scanStep state (.compression input answer (permutation (c3Marker answer))))
              ?_ ?_ ?_
            · rintro (raised | ⟨-, hit⟩)
              · exact clear raised
              · exact safe hit
            · intro key reply present
              by_cases same : key = input
              · subst same
                rw [QueryCache.cacheQuery_self] at present
                cases present
                exact List.mem_cons_self
              · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
                exact List.mem_cons_of_mem _ (cached key reply present)
            · exact size.trans (Nat.le_succ _)
          have combined := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation
              ((liftM (World.query (.inr (.inr (.inl (c3Marker answer))))) :
                  OracleComp World _) >>= fun mark =>
                (fun result : α × List MarkedRow =>
                  (result.1, MarkedRow.compression input answer mark :: result.2)) <$>
                    markedRows (next answer))
              (cache.cacheQuery input answer))
            (fun answer => answer ∈ state.targets)
            (fun result => (scan state result.1.2).flag) continuation).trans
              (add_le_add fresh le_rfl)
          exact combined.trans_eq split
        · rw [compression_run_compress_some permutation input _ cache answer stored,
            compression_run_permute, compression_run_map, prEvent_map]
          refine (ih answer (budget - 1) (known + 1) (tails answer) cache
            (scanStep state (.compression input answer (permutation (c3Marker answer))))
            ?_ ?_ ?_).trans later
          · rintro (raised | ⟨unseen, -⟩)
            · exact clear raised
            · exact unseen (cached input answer stored)
          · intro key reply present
            exact List.mem_cons_of_mem _ (cached key reply present)
          · exact size.trans (Nat.le_succ _)
      · rcases permQuery with input | output
        · rw [marked_rows_permute, compression_run_permute, compression_run_map, prEvent_map]
          exact (ih (permutation input) (budget - 1) (known + 1) (tails _) cache
            (scanStep state (.forward input (permutation input))) clear cached
            (size.trans (Nat.le_succ _))).trans later
        · rw [marked_rows_inverse, compression_run_inverse, compression_run_map, prEvent_map]
          exact (ih (permutation.symm output) (budget - 1) (known + 1) (tails _) cache
            (scanStep state (.inverse (permutation.symm output) output)) clear cached
            (Nat.succ_le_succ size)).trans later

/-- From the empty cache: at most `Q (Q - 1) / (2 · 2^256)` for a program with `Q` public calls. -/
theorem flag_bound (permutation : Perm) {α : Type} (program : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound program budget) :
    Pr{let result ← compressionRun permutation (markedRows program) ∅}[
        (scan ScanState.init result.1.2).flag] ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) := by
  have estimate := flag_bound_from_cache permutation program budget 0 bounded ∅ ScanState.init
    (fun raised => raised)
    (fun input reply present => by
      change (none : Option (BitVec 256)) = some reply at present
      cases present)
    (Nat.le_refl 0)
  simp only [Nat.zero_add, div_eq_mul_inv] at estimate
  exact estimate.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 256))

/-- The same bound in the contract's model: a uniformly sampled compression function, any fixed
permutation. -/
theorem fixed_permutation_flag_bound {α : Type} (p : Perm) (program : OracleComp World α)
    (calls : Nat) (bounded : PublicQueryBound program calls) :
    Pr{let result ← (do let compress ← $ᵗ Compression
                        fixedOracleRun ⟨compress, p⟩ (markedRows program))}[
      (scan ScanState.init result.2).flag] ≤
      ((calls * (calls - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) := by
  have equivalent := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty p (markedRows program))).prEvent_eq
      (fun result => (scan ScanState.init result.2).flag)
  rw [← equivalent, prEvent_map]
  exact flag_bound p program calls bounded

end TwoPermutationPrototype.Sampling
