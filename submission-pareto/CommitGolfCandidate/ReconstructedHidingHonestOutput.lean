import CommitGolfCandidate.ReconstructedHidingForwardOnly
import CommitGolfCandidate.ReconstructedHidingHonestFlag
import CommitGolfCandidate.ReconstructedHidingRetainedGame

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic TwoPermutationPrototype.Sampling CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (accept)
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local irreducible] toStrat checkedQueries queryDigests cacheTrace Trace.ext

noncomputable def generatorOutputs (y : GenReplies) : Finset Reply := Finset.univ.image y

theorem generator_outputs_mem (y : GenReplies) (b : Reply) : b∈generatorOutputs y ↔ ∃ i, y i=b := by
  simp [generatorOutputs]

noncomputable def outputPermit (y : GenReplies) : Reply → Reply → Bool :=
  permitSets (fun _ : Unit => ∅) (fun _ => generatorOutputs y) ()

private theorem permit_sets_iff {K : Type} (ins outs : K → Finset Reply) (i : K) (x b : Reply) :
    permitSets ins outs i x b = true ↔ ¬touches ins outs i x b := by
  classical
  exact decide_eq_true_iff

theorem permit_by_output (k : Key) (y : GenReplies) (input result : Reply) (free : ∀ j, packedAddress k j ≠ input) :
    genPermit k y input result = outputPermit y input result := by
  apply Bool.eq_iff_iff.mpr
  rw [gen_permit_iff]
  unfold outputPermit
  rw [permit_sets_iff]
  unfold touches
  rw [generator_outputs_mem]
  exact ⟨fun h hit => hit.elim (Finset.notMem_empty _) (fun ⟨j,eq⟩ => h.2 j eq),
    fun h => ⟨free,fun j eq => h (Or.inr ⟨j,eq⟩)⟩⟩

theorem honest_flags_by_output (m : Message) (r : CompleteSaltTape) (p : BiPermutation Block)
    (k : Key) (y : GenReplies) (raw : ∀ i, ¬keyHit (honestFirst m i) k) :
    allLeafFlags (genPermit k y) p m r = allLeafFlags (outputPermit y) p m r := by
  have same : leafFlag (genPermit k y) p m r = leafFlag (outputPermit y) p m r := by
    funext i
    unfold leafFlag
    exact congrArg₂ Bool.and
      (permit_by_output k y (honestFirst m i) (p.forward (honestFirst m i)) (fun j eq => raw i (eq ▸ address_key_hit k j)))
      (permit_by_output k y (honestSecond p m r i) (p.forward (honestSecond p m r i)) (second_avoids_generator p m r i k))
  exact congrArg (List.all (List.finRange LENGTH)) same

theorem cached_output_free (table : Cache) (k : Key) (y : GenReplies) (clean : cacheAllow (genPermit k y) table=true) :
    ∀ x b, containsPair (cacheTrace table) x b → b∉generatorOutputs y := by
  intro x b known inside
  obtain ⟨j,found⟩ := (generator_outputs_mem y b).mp inside
  have good := List.all_eq_true.mp clean (x,b) ((cache_pair table x b).mp known)
  exact ((gen_permit_iff k y x b).mp good).2 j found

theorem honest_output_loss (table : Cache) (c : Compression) (m : Message) (r : CompleteSaltTape)
    (k : Key) (y : GenReplies) (clean : cacheAllow (genPermit k y) table=true)
    (raw : ∀ i, ¬keyHit (honestFirst m i) k) (room : table.entries.length+2*LENGTH ≤ 2^122) :
    (Pr{let p ← table.sample}[allLeafFlags (genPermit k y) p.val m r=false]).toReal ≤
      (2*LENGTH:ℝ)*(groupCount/((2:ℝ)^1600-2^122)) := by
  classical
  let g := queryDigests m r
  let t : Trace Reply := cacheTrace table
  let st : PState Reply := ⟨t,t.length⟩
  let ins := fun _ : Unit => (∅:Finset Reply)
  let outs := fun _ : Unit => generatorOutputs y
  let next (π : Perm) := fixedOracleRun ⟨c,π⟩ (checkedQueries (outputPermit y) g true)
  let fail := fun (v : DigestTape × Bool) => v.2=false
  have equal (p : Completion table.entries) : next ((BiPermutation.equiv Block).symm p.val) =
      pure (pinnedFullLeafDigests p.val m r,allLeafFlags (genPermit k y) p.val m r) := by
    have result := checked_digests_flags (fixedOracle c p.val) (outputPermit y) m r true
    simp only [fixedOracle,Equiv.apply_symm_apply,Bool.true_and] at result
    rw [honest_flags_by_output m r p.val k y raw]
    exact result
  have measured := cache_bind_mean table next fail
  have shift : (table.sample >>= fun p => next ((BiPermutation.equiv Block).symm p.val)) =
      ((fun p : Completion table.entries => (pinnedFullLeafDigests p.val m r,allLeafFlags (genPermit k y) p.val m r)) <$> table.sample) := by
    simp_rw [equal]
    exact bind_pure_comp _ _
  rw [shift,prEvent_map] at measured
  simp only [fail] at measured
  calc
    _ = avg (cacheTrace table).ext (fun π => (Pr{let a ← next π}[fail a]).toReal) := measured
    _ ≤ _ := by
      have per (π : Perm) : (Pr{let v ← next π}[fail v]).toReal =
          (stopOnHit ins outs () (toStrat c g)).eager π st (fun b _ => accept b) := by
        unfold next
        rw [fixed_run_prob c π _ fail st]
        exact (ENNReal.toReal_ofReal (Strat.eager_nonneg π (fun x _ => ind_nonneg (fail x)) _ st)).trans
          (marked_failure ins outs () c π g st)
      rw [avg_congr (fun π _ => per π)]
      have average : avg t.ext (fun π => (stopOnHit ins outs () (toStrat c g)).eager π st (fun b _ => accept b)) =
          hitProb ins outs () (toStrat c g) t := by
        change (∑ π ∈ st.trace.ext, (stopOnHit ins outs () (toStrat c g)).eager π st (fun b _ => accept b)) / t.ext.card = _
        rw [(stopOnHit ins outs () (toStrat c g)).sum_eager st (cache_well table) _]
        have nz : (t.ext.card:ℝ)≠0 := by exact_mod_cast (cache_has_completion table).card_ne_zero
        exact (mul_div_cancel_left₀ ((stopOnHit ins outs () (toStrat c g)).exp st (fun b _ => accept b)) nz).trans
          (stop_exp ins outs () (toStrat c g) st)
      refine average.le.trans ?_
      have size : (generatorOutputs y).card ≤ groupCount := by
        exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin _))
      have card : Fintype.card Reply = 2^1600 := by change Fintype.card (BitVec 1600) = _; rw [←FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
      have bound := forward_output_bound (S := Reply) t (cache_well table) (generatorOutputs y) groupCount (2^122) size
        (cached_output_free table k y clean) (by rw [card]; decide) (toStrat c g) (2*LENGTH)
        (to_strat_QB c (query_digests_bound m r)) (only_digests c m r)
        (by have fits := cache_length table; change (cacheTrace table).length+2*LENGTH≤2^122; omega)
      simpa only [ins,outs,card,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] using bound

end CommitGolfCandidate.Reconstruction.HidingTape
