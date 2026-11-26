import CommitGolfCandidate.MoonImage
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.Execution

/-! Complete 238-bit adaptive position-binding reduction for the pure-binary tree.
Rather than re-implementing a proof parser for deduplicated cap openings, the collision detector
directly executes the submitted deterministic `check` image on both conflicting claims while
recording every `(input, answer)` compression query in `traceCompressionReplies`.
With per-level truncation down to at least 238 bits, the exact survival-product birthday bound
in the lazy compression ROM yields `Pr[Breaks ∧ calls ≤ q] ≤ q / 2^120` for every
`1 ≤ q ≤ 2^120` with `M = q + 2^39` total compression queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### Witness Paths and Pure 238-bit Structural Collision Extraction -/

structure WitnessPath where
  index : Index
  value : Entry
  salt : Salt121
  binSib : Nat → Digest

def WitnessPath.evalLevel (c : Comp96) (w : WitnessPath) : Nat → Digest
  | 0 => maskLevel 0 (leafDigest c w.index w.salt w.value)
  | l + 1 =>
      let cur := w.evalLevel c l
      let idx := w.index.val >>> l
      let inp := if idx % 2 = 0 then binaryInput cur (w.binSib l)
                 else binaryInput (w.binSib l) cur
      maskLevel (l + 1) (c inp)

def WitnessPath.evalRoot (c : Comp96) (w : WitnessPath) : Digest :=
  w.evalLevel c 24

def WitnessPath.leafInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  let i0 := leafCall0Input w.index w.salt w.value
  let cv0 := c i0
  let i1 := leafCall1Input cv0 w.value
  let cv1 := c i1
  let i2 := leafCall2Input cv1 w.value
  let cv2 := c i2
  let i3 := leafCall3Input cv2 w.value
  [i0, i1, i2, i3]

def WitnessPath.levelInput (c : Comp96) (w : WitnessPath) (l : Nat) : BitVec 768 :=
  let cur := w.evalLevel c l
  let idx := w.index.val >>> l
  if idx % 2 = 0 then binaryInput cur (w.binSib l) else binaryInput (w.binSib l) cur

def WitnessPath.pathInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  w.leafInputs c ++ (List.range 24).map (w.levelInput c)

def HasCollision238 (c : Comp96) (inputs : List (BitVec 768)) : Prop :=
  ∃ x ∈ inputs, ∃ y ∈ inputs, x ≠ y ∧ low238 (c x) = low238 (c y)

private theorem mem_pathInputs_leaf (c : Comp96) (w : WitnessPath) (x : BitVec 768)
    (hx : x ∈ w.leafInputs c) : x ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs
  exact List.mem_append_left _ hx

private theorem mem_pathInputs_level (c : Comp96) (w : WitnessPath) (l : Nat) (hl : l < 24) :
    w.levelInput c l ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩

private theorem bv_append_inj {m n : Nat} {a1 a2 : BitVec m} {b1 b2 : BitVec n}
    (h : a1 ++ b1 = a2 ++ b2) : a1 = a2 ∧ b1 = b2 := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit := congrArg (fun v : BitVec (m + n) => v.getLsbD (n + i)) h
    simp only [BitVec.getLsbD_append, show ¬ (n + i < n) by omega, decide_false,
      Bool.false_eq_true, ite_false, show n + i - n = i by omega] at hbit
    exact hbit
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hbit := congrArg (fun v : BitVec (m + n) => v.getLsbD i) h
    simp only [BitVec.getLsbD_append, hi, decide_true, ite_true] at hbit
    exact hbit

private theorem leaf_collision238 (c : Comp96) (w1 w2 : WitnessPath)
    (_hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hdig : w1.evalLevel c 0 = w2.evalLevel c 0) :
    HasCollision238 c (w1.pathInputs c ++ w2.pathInputs c) := by
  set i0₁ := leafCall0Input w1.index w1.salt w1.value
  set i0₂ := leafCall0Input w2.index w2.salt w2.value
  set cv0₁ := c i0₁; set cv0₂ := c i0₂
  set i1₁ := leafCall1Input cv0₁ w1.value; set i1₂ := leafCall1Input cv0₂ w2.value
  set cv1₁ := c i1₁; set cv1₂ := c i1₂
  set i2₁ := leafCall2Input cv1₁ w1.value; set i2₂ := leafCall2Input cv1₂ w2.value
  set cv2₁ := c i2₁; set cv2₂ := c i2₂
  set i3₁ := leafCall3Input cv2₁ w1.value; set i3₂ := leafCall3Input cv2₂ w2.value
  have hmem1 : ∀ x ∈ w1.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_left _ (mem_pathInputs_leaf c w1 x hx)
  have hmem2 : ∀ x ∈ w2.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_right _ (mem_pathInputs_leaf c w2 x hx)
  by_cases h3 : i3₁ ≠ i3₂
  · have hlow3 : low238 (c i3₁) = low238 (c i3₂) := by
      have h := congrArg low238 hdig
      rw [WitnessPath.evalLevel, WitnessPath.evalLevel, low238_maskLevel, low238_maskLevel] at h
      exact h
    exact ⟨i3₁, hmem1 _ (by simp [WitnessPath.leafInputs, i3₁, cv2₁, i2₁, cv1₁, i1₁, cv0₁, i0₁]),
      i3₂, hmem2 _ (by simp [WitnessPath.leafInputs, i3₂, cv2₂, i2₂, cv1₂, i1₂, cv0₂, i0₂]),
      h3, hlow3⟩
  · push_neg at h3
    obtain ⟨hv3, hcv2⟩ := bv_append_inj (show w1.value.extractLsb' 1536 512 ++ cv2₁ =
      w2.value.extractLsb' 1536 512 ++ cv2₂ from h3)
    by_cases h2 : i2₁ ≠ i2₂
    · exact ⟨i2₁, hmem1 _ (by simp [WitnessPath.leafInputs, i2₁, cv1₁, i1₁, cv0₁, i0₁]),
        i2₂, hmem2 _ (by simp [WitnessPath.leafInputs, i2₂, cv1₂, i1₂, cv0₂, i0₂]),
        h2, congrArg low238 hcv2⟩
    · push_neg at h2
      obtain ⟨hv2, hcv1⟩ := bv_append_inj (show w1.value.extractLsb' 1088 512 ++ cv1₁ =
        w2.value.extractLsb' 1088 512 ++ cv1₂ from h2)
      by_cases h1 : i1₁ ≠ i1₂
      · exact ⟨i1₁, hmem1 _ (by simp [WitnessPath.leafInputs, i1₁, cv0₁, i0₁]),
          i1₂, hmem2 _ (by simp [WitnessPath.leafInputs, i1₂, cv0₂, i0₂]),
          h1, congrArg low238 hcv1⟩
      · push_neg at h1
        obtain ⟨hv1, hcv0⟩ := bv_append_inj (show w1.value.extractLsb' 576 512 ++ cv0₁ =
          w2.value.extractLsb' 576 512 ++ cv0₂ from h1)
        by_cases h0 : i0₁ ≠ i0₂
        · exact ⟨i0₁, hmem1 _ (by simp [WitnessPath.leafInputs, i0₁]),
            i0₂, hmem2 _ (by simp [WitnessPath.leafInputs, i0₂]),
            h0, congrArg low238 hcv0⟩
        · push_neg at h0
          obtain ⟨_, _, hv0⟩ := leafCall0Input_inj h0
          exact (hne (entry_eq_of_slices w1.value w2.value hv0 hv1 hv2 hv3)).elim

private theorem bin_step_collision238 (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (l : Nat) (hl : l < 24)
    (heq : w1.evalLevel c (l + 1) = w2.evalLevel c (l + 1)) :
    w1.evalLevel c l = w2.evalLevel c l ∨
    HasCollision238 c (w1.pathInputs c ++ w2.pathInputs c) := by
  set inp1 := w1.levelInput c l
  set inp2 := w2.levelInput c l
  have h1 : w1.evalLevel c (l + 1) = maskLevel (l + 1) (c inp1) := rfl
  have h2 : w2.evalLevel c (l + 1) = maskLevel (l + 1) (c inp2) := rfl
  rw [h1, h2] at heq
  by_cases hne : inp1 ≠ inp2
  · right
    have hlow : low238 (c inp1) = low238 (c inp2) := by
      have h := congrArg low238 heq
      simpa only [low238_maskLevel] using h
    exact ⟨inp1, List.mem_append_left _ (mem_pathInputs_level c w1 l hl),
      inp2, List.mem_append_right _ (mem_pathInputs_level c w2 l hl),
      hne, hlow⟩
  · left
    push_neg at hne
    dsimp only [inp1, inp2, WitnessPath.levelInput] at hne
    rw [hidx] at hne
    by_cases heven : (w2.index.val >>> l) % 2 = 0
    · simp only [heven, ite_true] at hne
      have := congrArg (fun v : BitVec 768 => v.extractLsb' 0 256) hne
      simpa [binaryInput_left] using this
    · simp only [heven, ite_false] at hne
      have := congrArg (fun v : BitVec 768 => v.extractLsb' 256 256) hne
      simpa [binaryInput_right] using this

/-- Two conflicting witness paths reaching the same root MUST witness a 238-bit compression collision. -/
theorem collision238_of_paths (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hroot : w1.evalRoot c = w2.evalRoot c) :
    HasCollision238 c (w1.pathInputs c ++ w2.pathInputs c) := by
  have descend : ∀ k ≤ 24,
      w1.evalLevel c (24 - k) = w2.evalLevel c (24 - k) ∨
      HasCollision238 c (w1.pathInputs c ++ w2.pathInputs c) := by
    intro k hk
    induction k with
    | zero => left; exact hroot
    | succ k ih =>
      rcases ih (by omega) with heq | hcol
      · have hstep : 24 - k = (24 - (k + 1)) + 1 := by omega
        rw [hstep] at heq
        exact bin_step_collision238 c w1 w2 hidx (24 - (k + 1)) (by omega) heq
      · exact Or.inr hcol
  rcases descend 24 (by omega) with hl0 | hcol
  · exact leaf_collision238 c w1 w2 hidx hne hl0
  · exact hcol

/-! ### 238-bit Lazy Compression ROM Exact Survival-Product Birthday Bound -/

def CacheHasCollision238 (cache : CompressionCache) : Prop :=
  ∃ (x y : BitVec COMPRESSION_INPUT_LENGTH) (vx vy : Digest),
    x ≠ y ∧ cache x = some vx ∧ cache y = some vy ∧ low238 vx = low238 vy

private theorem card_low238_preimage (targets : Finset (BitVec 238))
    [DecidablePred (fun ans : Digest => low238 ans ∈ targets)] :
    (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets)).card ≤ 2 ^ 18 * targets.card := by
  have hinj : Set.InjOn (fun ans : Digest => (ans.extractLsb' 238 18, low238 ans))
      (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets) : Set Digest) := by
    intro a _ b _ h
    have hhi : a.extractLsb' 238 18 = b.extractLsb' 238 18 := congrArg Prod.fst h
    have hlo : low238 a = low238 b := congrArg Prod.snd h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h238 : i < 238
    · have := congrArg (fun v : BitVec 238 => v.getLsbD i) hlo
      simpa only [low238, BitVec.getLsbD_extractLsb', h238, decide_true, Bool.true_and, Nat.zero_add] using this
    · have hi18 : i - 238 < 18 := by omega
      have := congrArg (fun v : BitVec 18 => v.getLsbD (i - 238)) hhi
      simpa only [BitVec.getLsbD_extractLsb', hi18, decide_true, Bool.true_and,
        show 238 + (i - 238) = i by omega] using this
  have hmaps : Set.MapsTo (fun ans : Digest => (ans.extractLsb' 238 18, low238 ans))
      (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets) : Set Digest)
      ((Finset.univ ×ˢ targets : Finset (BitVec 18 × BitVec 238)) : Set (BitVec 18 × BitVec 238)) := by
    intro ans hans
    rw [Finset.mem_coe, Finset.mem_filter] at hans
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_univ _, hans.2⟩
  calc
    (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets)).card
      ≤ (Finset.univ ×ˢ targets : Finset (BitVec 18 × BitVec 238)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ : Finset (BitVec 18)).card * targets.card := Finset.card_product _ _
    _ = 2 ^ 18 * targets.card := by rw [Finset.card_univ, Fintype.card_bitVec]

noncomputable def survFactor (k : Nat) : ENNReal :=
  ((2 ^ 238 - k : Nat) : ENNReal) / 2 ^ 238

private theorem survFactor_le_one (k : Nat) : survFactor k ≤ 1 := by
  unfold survFactor
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (by finiteness)), one_mul]
  exact_mod_cast Nat.sub_le (2 ^ 238) k

private theorem survFactor_anti {a b : Nat} (h : a ≤ b) : survFactor b ≤ survFactor a := by
  unfold survFactor
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.sub_le_sub_left h _)) _

private theorem one_le_survFactor_add (k : Nat) (hk : k ≤ 2 ^ 238) :
    (1 : ENNReal) ≤ survFactor k + (k : ENNReal) / 2 ^ 238 := by
  unfold survFactor
  rw [← ENNReal.add_div, ← Nat.cast_add, Nat.sub_add_cancel hk, Nat.cast_pow, Nat.cast_ofNat]
  exact (ENNReal.div_self (by positivity) (by finiteness)).ge

theorem fresh_noCollision238_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCol : ¬ CacheHasCollision238 cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    survFactor keys.card ≤
      prEvent ((fun ans => ¬ CacheHasCollision238 (cache.cacheQuery input ans)) <$>
        ($ᵗ CompressionSpec.Range input)) := by
  classical
  let targets : Finset (BitVec 238) :=
    keys.biUnion (fun k => match cache k with | some v => {low238 v} | none => ∅)
  have htargets_card : targets.card ≤ keys.card := by
    calc
      targets.card ≤ ∑ k ∈ keys, (match cache k with | some v => ({low238 v} : Finset (BitVec 238)) | none => ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ keys, 1 := by
        apply Finset.sum_le_sum
        intro k _
        cases cache k <;> simp
      _ = keys.card := by simp
  have hsub : (Finset.univ.filter (fun ans : Digest => CacheHasCollision238 (cache.cacheQuery input ans))) ⊆
      Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets) := by
    intro ans hans
    rw [Finset.mem_filter] at hans ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨x, y, vx, vy, hne, hx, hy, hlow⟩ := hans.2
    by_cases hxi : x = input
    · subst hxi
      have hyne : y ≠ x := Ne.symm hne
      erw [QueryCache.cacheQuery_self cache x ans] at hx
      erw [QueryCache.cacheQuery_of_ne cache ans hyne] at hy
      cases hx
      have hy' : cache y = some vy := hy
      have hyk : y ∈ keys := covers y (by intro hnone; rw [hnone] at hy'; cases hy')
      exact Finset.mem_biUnion.mpr ⟨y, hyk, by simp [hy', hlow]⟩
    · by_cases hyi : y = input
      · subst hyi
        erw [QueryCache.cacheQuery_of_ne cache ans hxi] at hx
        erw [QueryCache.cacheQuery_self cache y ans] at hy
        cases hy
        have hx' : cache x = some vx := hx
        have hxk : x ∈ keys := covers x (by intro hnone; rw [hnone] at hx'; cases hx')
        exact Finset.mem_biUnion.mpr ⟨x, hxk, by simp [hx', hlow]⟩
      · erw [QueryCache.cacheQuery_of_ne cache ans hxi] at hx
        erw [QueryCache.cacheQuery_of_ne cache ans hyi] at hy
        exact (noCol ⟨x, y, vx, vy, hne, hx, hy, hlow⟩).elim
  have hbad : (Finset.univ.filter (fun ans : Digest => CacheHasCollision238 (cache.cacheQuery input ans))).card ≤
      2 ^ 18 * keys.card :=
    (Finset.card_le_card hsub).trans ((card_low238_preimage targets).trans (Nat.mul_le_mul_left _ htargets_card))
  have hpart :
      (Finset.univ.filter (fun ans : Digest => CacheHasCollision238 (cache.cacheQuery input ans))).card +
      (Finset.univ.filter (fun ans : Digest => ¬ CacheHasCollision238 (cache.cacheQuery input ans))).card =
      (Finset.univ : Finset Digest).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine congrArg Finset.card ?_
      ext ans
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Classical.em _
    · rw [Finset.disjoint_left]; intro a ha1 ha2
      exact (Finset.mem_filter.mp ha2).2 (Finset.mem_filter.mp ha1).2
  have huniv : (Finset.univ : Finset Digest).card = 2 ^ 256 := by
    rw [Finset.card_univ, Fintype.card_bitVec]
  have hgood : 2 ^ 18 * (2 ^ 238 - keys.card) ≤
      (Finset.univ.filter (fun ans : Digest => ¬ CacheHasCollision238 (cache.cacheQuery input ans))).card := by
    have hmul : 2 ^ 18 * (2 ^ 238 - keys.card) = 2 ^ 256 - 2 ^ 18 * keys.card := by
      rw [Nat.mul_sub_left_distrib, show 2 ^ 18 * 2 ^ 238 = 2 ^ 256 by decide]
    omega
  change survFactor keys.card ≤
    prEvent ((fun ans : Digest => ¬ CacheHasCollision238 (cache.cacheQuery input ans)) <$> ($ᵗ Digest))
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ 256 := Fintype.card_bitVec 256
  rw [hcard]
  calc
    survFactor keys.card
      = ((2 ^ 18 * (2 ^ 238 - keys.card) : Nat) : ENNReal) / (2 ^ 256 : Nat) := by
        unfold survFactor
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 256 = 2 ^ 18 * 2 ^ 238 by rw [← pow_add]]
        exact (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
    _ ≤ ((Finset.univ.filter (fun ans : Digest =>
          ¬ CacheHasCollision238 (cache.cacheQuery input ans))).card : ENNReal) / (2 ^ 256 : Nat) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hgood) _

private theorem prEvent_mul_le_prEvent_bind_of_support {α β : Type}
    (mx : ProbComp α) (f : α → ProbComp β) (p : α → Prop) (q : β → Prop) (r : ENNReal)
    (h : ∀ a ∈ support mx, p a → r ≤ prEvent (q <$> f a)) :
    prEvent (p <$> mx) * r ≤ prEvent (q <$> (mx >>= f)) := by
  classical
  rw [bind_eq_attach_bind mx f]
  have hmap : prEvent (p <$> mx) =
      prEvent ((fun a => p a.1) <$> MonadAttach.attach mx) := by
    conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
    rw [Functor.map_map]
  rw [hmap, prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hp : p a.1
  · simp only [hp, ite_true]
    exact mul_le_mul' le_rfl (h a.1 a.2 hp)
  · simp only [hp, ite_false, zero_mul]
    exact zero_le

theorem compression_noCollision238_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCol : ¬ CacheHasCollision238 cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    (∏ step ∈ Finset.range budget, survFactor (known + step)) ≤
      prEvent ((fun result => ¬ CacheHasCollision238 result.2) <$> (compressionRun permutation computation cache)) := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, noCol, not_false_eq_true, ite_true]
    exact Finset.prod_le_one (fun _ _ => survFactor_le_one _)
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _)
      intro answer _
      exact ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCol covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have smaller : (∏ step ∈ Finset.range budget, survFactor (known + step)) ≤
          ∏ step ∈ Finset.range (budget - 1), survFactor (known + step) := by
        conv_lhs => rw [show budget = (budget - 1) + 1 from by omega]
        rw [Finset.prod_range_succ]
        exact mul_le_of_le_one_right zero_le (survFactor_le_one _)
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact smaller.trans (ih answer (budget - 1) known (tails answer) cache noCol covered)
        | none =>
          have fresh : survFactor known ≤
              prEvent ((fun answer => ¬ CacheHasCollision238 (cache.cacheQuery input answer)) <$>
                ($ᵗ CompressionSpec.Range input)) := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (survFactor_anti size).trans (fresh_noCollision238_bound cache input keys noCol covers)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHasCollision238 (cache.cacheQuery input answer) →
              (∏ step ∈ Finset.range (budget - 1), survFactor (known + 1 + step)) ≤
                prEvent ((fun result => ¬ CacheHasCollision238 result.2) <$>
                  (compressionRun permutation (next answer) (cache.cacheQuery input answer))) := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have hprod : (∏ step ∈ Finset.range budget, survFactor (known + step)) =
              survFactor known * (∏ step ∈ Finset.range (budget - 1), survFactor (known + 1 + step)) := by
            conv_lhs => rw [show budget = (budget - 1) + 1 from by omega]
            rw [Finset.prod_range_succ']
            simp only [Nat.add_zero]
            rw [mul_comm]
            congr 1
            apply Finset.prod_congr rfl
            intro step _
            rw [show known + 1 + step = known + (step + 1) from by omega]
          rw [hprod]
          exact (mul_le_mul' fresh le_rfl).trans
            (prEvent_mul_le_prEvent_bind_of_support
              ($ᵗ CompressionSpec.Range input)
              (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
              (fun answer => ¬ CacheHasCollision238 (cache.cacheQuery input answer))
              (fun result => ¬ CacheHasCollision238 result.2) _ continuation)
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact smaller.trans (ih _ (budget - 1) known (tails _) cache noCol covered)
        · rw [compression_run_inverse]
          exact smaller.trans (ih _ (budget - 1) known (tails _) cache noCol covered)

theorem compression_noCollision238_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    (∏ i ∈ Finset.range budget, survFactor i) ≤
      prEvent ((fun result => ¬ CacheHasCollision238 result.2) <$> (compressionRun permutation computation ∅)) := by
  have est := compression_noCollision238_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, imp, _, _⟩; simp at imp)
    ⟨∅, by simp, fun _ p => (p rfl).elim⟩
  simpa only [Nat.zero_add] using est

/-! ### Query-Answer Tracing and Direct Checker Binding Reduction -/

abbrev CompressionReplies := List (BitVec COMPRESSION_INPUT_LENGTH × Digest)

def ReplyCollision238 (replies : CompressionReplies) : Prop :=
  ∃ a ∈ replies, ∃ b ∈ replies, a.1 ≠ b.1 ∧ low238 a.2 = low238 b.2

def traceCompressionReplies {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × CompressionReplies) :=
  OracleComp.recOn computation
    (fun value => pure (value, []))
    (fun query _ next =>
      match query, next with
      | .inr (.inl input), next => do
          let answer ← (liftM (World.query (.inr (.inl input))) : OracleComp World _)
          let (value, trace) ← next answer
          pure (value, (input, answer) :: trace)
      | q, next => do
          let answer ← (liftM (World.query q) : OracleComp World _)
          next answer)

private theorem public_query_bound_pure {α : Type} (x : α) (n : Nat) :
    PublicQueryBound (pure x : OracleComp World α) n := trivial

private theorem public_query_bound_coins {α : Type} (coins : ProbComp α) :
    PublicQueryBound (liftM coins : OracleComp World α) 0 := by
  induction coins using OracleComp.inductionOn with
  | pure _ => exact public_query_bound_pure _ 0
  | query_bind query _ ih =>
    exact ⟨Nat.zero_le _, fun answer => ih answer⟩

theorem traceReplies_bound {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    PublicQueryBound (traceCompressionReplies computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure _ => exact public_query_bound_pure _ _
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    · rcases publicQuery with input | permQuery
      · refine ⟨bounded.1, fun answer => ?_⟩
        have htail := ih answer (budget - 1) (bounded.2 answer)
        refine (public_query_bound_bind (second := 0) htail
          (fun p => public_query_bound_pure (p.1, (input, answer) :: p.2) 0)).mono ?_
        change budget - 1 + 0 ≤ budget - 1
        omega
      · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

theorem traceReplies_compressionRun_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (cache : CompressionCache)
    (result : (α × CompressionReplies) × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (traceCompressionReplies computation) cache)) :
    (∀ k v, cache k = some v → result.2 k = some v) ∧
    (∀ pair ∈ result.1.2, result.2 pair.1 = some pair.2) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    change result ∈ support (compressionRun permutation (pure (value, [])) cache) at reached
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ _ h => h, by simp⟩
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · change result ∈ support (compressionRun permutation
        ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
          traceCompressionReplies (next answer)) cache) at reached
      rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer cache result reached
    · rcases publicQuery with input | permQuery
      · change result ∈ support (compressionRun permutation
          ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer) >>= fun (value, trace) =>
              pure (value, (input, answer) :: trace)) cache) at reached
        rw [compression_run_compress] at reached
        cases hcached : cache input with
        | some answer =>
          rw [hcached] at reached
          dsimp only at reached
          rw [compression_run_bind] at reached
          obtain ⟨⟨⟨v, tr⟩, c'⟩, hreach, hrest⟩ := (mem_support_bind_iff _ _ _).mp reached
          dsimp only at hrest
          rw [compression_run_pure] at hrest
          erw [support_pure, Set.mem_singleton_iff] at hrest
          subst result
          obtain ⟨hpres, hmem⟩ := ih answer cache ((v, tr), c') hreach
          refine ⟨hpres, ?_⟩
          intro pair hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hpres input answer hcached
          · exact hmem pair hp
        | none =>
          rw [hcached] at reached
          dsimp only at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          rw [compression_run_bind] at reached
          obtain ⟨⟨⟨v, tr⟩, c'⟩, hreach, hrest⟩ := (mem_support_bind_iff _ _ _).mp reached
          dsimp only at hrest
          rw [compression_run_pure] at hrest
          erw [support_pure, Set.mem_singleton_iff] at hrest
          subst result
          obtain ⟨hpres, hmem⟩ := ih answer (cache.cacheQuery input answer) ((v, tr), c') hreach
          refine ⟨?_, ?_⟩
          · intro k v' hkv
            apply hpres
            by_cases hk : k = input
            · subst hk; rw [hcached] at hkv; cases hkv
            · erw [QueryCache.cacheQuery_of_ne cache answer hk]; exact hkv
          · intro pair hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hpres input answer (QueryCache.cacheQuery_self cache input answer)
            · exact hmem pair hp
      · rcases permQuery with input | input
        · change result ∈ support (compressionRun permutation
            ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= fun answer =>
              traceCompressionReplies (next answer)) cache) at reached
          rw [compression_run_permute] at reached
          exact ih _ cache result reached
        · change result ∈ support (compressionRun permutation
            ((liftM (World.query (.inr (.inr (.inr input)))) : OracleComp World _) >>= fun answer =>
              traceCompressionReplies (next answer)) cache) at reached
          rw [compression_run_inverse] at reached
          exact ih _ cache result reached

theorem execute_public_query_bound (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool) :
    PublicQueryBound (execute image steps state allowCoins) steps := by
  induction steps generalizing state with
  | zero => exact public_query_bound_pure _ _
  | succ steps ih =>
    simp only [execute]
    split
    · exact public_query_bound_pure _ _
    · split
      · split
        · exact public_query_bound_pure _ _
        · change Oracle.callCost (.inr _) ≤ steps + 1 ∧ _
          refine ⟨by change 1 ≤ steps + 1; omega, fun answer => ?_⟩
          refine (public_query_bound_bind (second := 0) (ih _)
            (fun _ => public_query_bound_pure _ 0)).mono ?_
          change steps + 0 ≤ steps + 1 - 1
          omega
      · split
        · exact public_query_bound_pure _ _
        · split
          · have hcoins := public_query_bound_coins ($ᵗ BitVec (8 * (state.getReg .x11).toNat))
            refine (public_query_bound_bind (first := 0) (second := steps + 1) hcoins (fun answer =>
              (public_query_bound_bind (second := 0)
                (ih (writeBits state (state.getReg .x10) answer))
                (fun _ => public_query_bound_pure _ 0)).mono (by omega))).mono (by omega)
          · exact public_query_bound_pure _ _
    · split
      · exact public_query_bound_pure _ _
      · refine (public_query_bound_bind (second := 0) (ih _)
          (fun _ => public_query_bound_pure _ 0)).mono (by omega)

theorem run_check_public_query_bound (input : CheckInput) :
    PublicQueryBound (submission.run .check input) (submission.steps .check) := by
  unfold Submission.run
  dsimp only
  split
  · exact execute_public_query_bound _ _ _ _
  · trivial

/-- Soundness contract satisfied by our submitted deterministic `check` image (proved in `MoonCheckRef`). -/
def CheckSound (h768 : COMPRESSION_INPUT_LENGTH = 768) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true →
    ∃ exec trace,
      fixedOracleRun oracle (traceCompressionReplies (submission.run .check input)) = pure (exec, trace) ∧
      ∀ (i : Index) (hi : i ∈ input.positions),
        ∃ w : WitnessPath,
          w.index = i ∧
          w.value = input.values ⟨i, hi⟩ ∧
          w.evalRoot (fun x => oracle.compression (x.cast h768.symm)) = input.commitment ∧
          ∀ x ∈ w.pathInputs (fun x => oracle.compression (x.cast h768.symm)),
            (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ trace

def boundedCollisionSearch (adversary : Scheme.Adversary) (budget : Nat) :
    OracleComp World CompressionReplies := do
  let res ← limitPublicQueries adversary budget
  match res with
  | none => pure []
  | some claim => do
      let (_, t0) ← traceCompressionReplies
        (submission.run .check ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩)
      let (_, t1) ← traceCompressionReplies
        (submission.run .check ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩)
      pure (t0 ++ t1)

theorem boundedCollisionSearch_bound (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (boundedCollisionSearch adversary budget) (budget + 2 ^ 39) := by
  unfold boundedCollisionSearch
  apply public_query_bound_bind (limit_public_bound adversary budget)
  intro res
  cases res with
  | none => trivial
  | some claim =>
    have hstep : submission.steps .check + submission.steps .check = 2 ^ 39 := by
      change 274877906944 + 274877906944 = 2 ^ 39; decide
    rw [← hstep]
    apply public_query_bound_bind (traceReplies_bound _ _ (run_check_public_query_bound _))
    intro _
    have h2 := traceReplies_bound _ _ (run_check_public_query_bound
      ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩)
    simpa only [Nat.add_zero] using public_query_bound_bind (second := 0) h2 (fun _ => public_query_bound_pure _ 0)

theorem search_replyCollision_in_cache (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))
    (hcol : ReplyCollision238 result.1) :
    CacheHasCollision238 result.2 := by
  unfold boundedCollisionSearch at reached
  rw [compression_run_bind] at reached
  obtain ⟨⟨res, c1⟩, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
  dsimp only at reached
  cases res with
  | none =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    obtain ⟨_, himp, _⟩ := hcol
    simp at himp
  | some claim =>
    rw [compression_run_bind] at reached
    obtain ⟨⟨⟨_, t0⟩, c2⟩, hreach0, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
    dsimp only at reached
    rw [compression_run_bind] at reached
    obtain ⟨⟨⟨_, t1⟩, c3⟩, hreach1, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
    dsimp only at reached
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    have h0 := (traceReplies_compressionRun_cache permutation _ c1 _ hreach0).2
    obtain ⟨hpres1, h1⟩ := traceReplies_compressionRun_cache permutation _ c2 _ hreach1
    have hboth : ∀ p ∈ t0 ++ t1, c3 p.1 = some p.2 := by
      intro p hp
      rcases List.mem_append.mp hp with hp0 | hp1
      · exact hpres1 p.1 p.2 (h0 p hp0)
      · exact h1 p hp1
    obtain ⟨a, ha, b, hb, hne, hlow⟩ := hcol
    exact ⟨a.1, b.1, a.2, b.2, hne, hboth a ha, hboth b hb, hlow⟩

/-! ### Elementary 5-Block Weierstrass Survival-Product Arithmetic (`238` bits) -/

private theorem one_le_prod_add_sum {ι : Type*} (s : Finset ι) (f g : ι → ENNReal)
    (hf : ∀ i ∈ s, f i ≤ 1) (hfg : ∀ i ∈ s, 1 ≤ f i + g i) :
    (1 : ENNReal) ≤ (∏ i ∈ s, f i) + (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≤ 1 := hf a (Finset.mem_insert_self a s)
    have h1a : 1 ≤ f a + g a := hfg a (Finset.mem_insert_self a s)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
                   (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    calc
      (1 : ENNReal) ≤ f a + g a := h1a
      _ = f a * 1 + g a := by rw [mul_one]
      _ ≤ f a * ((∏ i ∈ s, f i) + (∑ i ∈ s, g i)) + g a :=
        add_le_add (mul_le_mul' le_rfl hih) le_rfl
      _ = f a * (∏ i ∈ s, f i) + f a * (∑ i ∈ s, g i) + g a := by rw [mul_add, add_assoc]
      _ ≤ f a * (∏ i ∈ s, f i) + 1 * (∑ i ∈ s, g i) + g a :=
        add_le_add (add_le_add le_rfl (mul_le_mul' hfa le_rfl)) le_rfl
      _ = f a * (∏ i ∈ s, f i) + (g a + ∑ i ∈ s, g i) := by
        rw [one_mul]; ac_rfl

private theorem two_mul_sum_Ico_le (a b : Nat) (hab : a ≤ b) :
    2 * (∑ i ∈ Finset.Ico a b, i) + a ^ 2 ≤ b ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show a + (d + 1) = (a + d) + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    nlinarith

private theorem block_prod_lower (a b c v : Nat) (hab : a ≤ b) (hb : b ≤ 2 ^ 238)
    (hcv : c * v ^ 2 ≤ 2 ^ 20) (hbound : b ^ 2 ≤ a ^ 2 + c * v ^ 2 * 2 ^ 219) :
    (((2 ^ 20 - c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) ≤
      ∏ i ∈ Finset.Ico a b, survFactor i := by
  have hweier := one_le_prod_add_sum (Finset.Ico a b) survFactor (fun i => (i : ENNReal) / 2 ^ 238)
    (fun i _ => survFactor_le_one i)
    (fun i hi => one_le_survFactor_add i (by have := (Finset.mem_Ico.mp hi).2; exact (Nat.le_of_lt this).trans hb))
  have hsum_nat : 2 * (∑ i ∈ Finset.Ico a b, i) ≤ c * v ^ 2 * 2 ^ 219 := by
    have h2 := two_mul_sum_Ico_le a b hab
    exact Nat.le_of_add_le_add_right (h2.trans (by rw [add_comm]; exact hbound))
  have hsum : (∑ i ∈ Finset.Ico a b, (i : ENNReal) / 2 ^ 238) ≤ ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← div_eq_mul_inv]
    have hcast : ((2 * (∑ i ∈ Finset.Ico a b, i) : Nat) : ENNReal) ≤ ((c * v ^ 2 * 2 ^ 219 : Nat) : ENNReal) :=
      Nat.cast_le.mpr hsum_nat
    calc
      ((∑ i ∈ Finset.Ico a b, i : Nat) : ENNReal) / 2 ^ 238
        = ((2 : ENNReal) * ((∑ i ∈ Finset.Ico a b, i : Nat) : ENNReal)) / (2 * 2 ^ 238) :=
          (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
      _ ≤ ((c * v ^ 2 * 2 ^ 219 : Nat) : ENNReal) / (2 * 2 ^ 238) := by
          apply ENNReal.div_le_div_right
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast
      _ = ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 := by
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          rw [show (2 : ENNReal) * 2 ^ 238 = 2 ^ 20 * 2 ^ 219 by
            rw [← pow_succ', ← pow_add]]
          exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
  have h1 : (((2 ^ 20 - c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) + ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 = 1 := by
    rw [← ENNReal.add_div, ← Nat.cast_add, Nat.sub_add_cancel hcv, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_self (by positivity) (by finiteness)
  have hcomb : (((2 ^ 20 - c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) + ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 ≤
      (∏ i ∈ Finset.Ico a b, survFactor i) + ((c * v ^ 2 : Nat) : ENNReal) / 2 ^ 20 :=
    h1.le.trans (hweier.trans (add_le_add le_rfl hsum))
  exact (ENNReal.add_le_add_iff_right (by finiteness)).mp hcomb

private theorem prod_range_split5 (f : Nat → ENNReal) (m1 m2 m3 m4 M : Nat)
    (h1 : m1 ≤ m2) (h2 : m2 ≤ m3) (h3 : m3 ≤ m4) (h4 : m4 ≤ M) :
    ∏ i ∈ Finset.range M, f i =
      (∏ i ∈ Finset.Ico 0 m1, f i) *
      (∏ i ∈ Finset.Ico m1 m2, f i) *
      (∏ i ∈ Finset.Ico m2 m3, f i) *
      (∏ i ∈ Finset.Ico m3 m4, f i) *
      (∏ i ∈ Finset.Ico m4 M, f i) := by
  symm
  rw [Finset.prod_Ico_consecutive f (Nat.zero_le m1) h1,
      Finset.prod_Ico_consecutive f (Nat.zero_le m2) h2,
      Finset.prod_Ico_consecutive f (Nat.zero_le m3) h3,
      Finset.prod_Ico_consecutive f (Nat.zero_le m4) h4,
      Nat.Ico_zero_eq_range]

private def survivalGrid : List (Nat × Nat) :=
  [(16, 23), (23, 29), (29, 33), (33, 36), (36, 39), (39, 41), (41, 43), (43, 44),
   (44, 45), (45, 46), (46, 47), (47, 48), (48, 49), (49, 50), (50, 51), (51, 52),
   (52, 53), (53, 54), (54, 55), (55, 57), (57, 59), (59, 63), (63, 64)]

private def gridCellOk (p : Nat × Nat) : Bool :=
  let u := p.1
  let v := p.2
  decide (16 ≤ u ∧ u < v ∧ v ≤ 64 ∧
    (64 - u) * 2 ^ 94 ≤
      (2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
      (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
      (2 ^ 20 - 121 * v ^ 2))

private theorem survivalGrid_ok : survivalGrid.all gridCellOk = true := by decide

private theorem survivalGrid_covers :
    (List.range 48).all (fun i =>
      let k := i + 16
      survivalGrid.any (fun p => decide (p.1 ≤ k ∧ k + 1 ≤ p.2))) = true := by decide

private theorem five_block_nat_bound (M v coeff c : Nat)
    (hvlo : 17 ≤ v) (hvhi : v ≤ 64) (hM : M ≤ v * 2 ^ 114 + 2 ^ 39)
    (hcoeff : coeff ≤ 16) (hc : c = 8 * coeff + 1) :
    coeff * M ^ 2 + 98 * M + 49 ≤ 64 * c * (v ^ 2 * 2 ^ 219) := by
  have hM2 : M ^ 2 ≤ (v * 2 ^ 114 + 2 ^ 39) ^ 2 := Nat.pow_le_pow_left hM 2
  have hexp : (v * 2 ^ 114 + 2 ^ 39) ^ 2 =
      v ^ 2 * 2 ^ 228 + 2 * v * 2 ^ 153 + 2 ^ 78 := by ring
  have hmain : coeff * (v ^ 2 * 2 ^ 228) = 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) := by ring
  have hconst : 16 * (2 * 64 * 2 ^ 153 + 2 ^ 78) + 98 * (64 * 2 ^ 114 + 2 ^ 39) + 49 ≤
      64 * 17 ^ 2 * 2 ^ 219 := by decide
  have hv2 : 17 ^ 2 ≤ v ^ 2 := Nat.pow_le_pow_left hvlo 2
  have herr1 : coeff * (2 * v * 2 ^ 153 + 2 ^ 78) ≤ 16 * (2 * 64 * 2 ^ 153 + 2 ^ 78) :=
    Nat.mul_le_mul hcoeff (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hvhi)) _)
  have herr2 : 98 * M ≤ 98 * (64 * 2 ^ 114 + 2 ^ 39) :=
    Nat.mul_le_mul_left 98 (hM.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hvhi) _))
  have hrhs_err : 64 * 17 ^ 2 * 2 ^ 219 ≤ 64 * (v ^ 2 * 2 ^ 219) := by
    rw [show 64 * 17 ^ 2 * 2 ^ 219 = 64 * (17 ^ 2 * 2 ^ 219) by ring]
    exact Nat.mul_le_mul_left 64 (Nat.mul_le_mul_right _ hv2)
  have hsplit : 64 * c * (v ^ 2 * 2 ^ 219) =
      64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) + 64 * (v ^ 2 * 2 ^ 219) := by
    rw [hc]; ring
  have hcm : coeff * M ^ 2 ≤ coeff * (v ^ 2 * 2 ^ 228) + coeff * (2 * v * 2 ^ 153 + 2 ^ 78) := by
    calc
      coeff * M ^ 2 ≤ coeff * (v * 2 ^ 114 + 2 ^ 39) ^ 2 := Nat.mul_le_mul_left coeff hM2
      _ = coeff * (v ^ 2 * 2 ^ 228) + coeff * (2 * v * 2 ^ 153 + 2 ^ 78) := by rw [hexp]; ring
  calc
    coeff * M ^ 2 + 98 * M + 49
      ≤ (coeff * (v ^ 2 * 2 ^ 228) + coeff * (2 * v * 2 ^ 153 + 2 ^ 78)) +
        98 * (64 * 2 ^ 114 + 2 ^ 39) + 49 :=
          Nat.add_le_add_right (Nat.add_le_add hcm herr2) 49
    _ = 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) +
        (coeff * (2 * v * 2 ^ 153 + 2 ^ 78) + 98 * (64 * 2 ^ 114 + 2 ^ 39) + 49) := by
          rw [hmain]; ring
    _ ≤ 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) +
        (16 * (2 * 64 * 2 ^ 153 + 2 ^ 78) + 98 * (64 * 2 ^ 114 + 2 ^ 39) + 49) :=
          Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right herr1 _) 49) _
    _ ≤ 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) + 64 * 17 ^ 2 * 2 ^ 219 :=
          Nat.add_le_add_left hconst _
    _ ≤ 64 * (8 * coeff) * (v ^ 2 * 2 ^ 219) + 64 * (v ^ 2 * 2 ^ 219) :=
          Nat.add_le_add_left hrhs_err _
    _ = 64 * c * (v ^ 2 * 2 ^ 219) := hsplit.symm

private theorem five_block_sq_step (M R : Nat)
    (hnb0 : 16 * M ^ 2 + 98 * M + 49 ≤ 64 * 129 * R)
    (hnb1 : 9 * M ^ 2 + 98 * M + 49 ≤ 64 * 73 * R)
    (hnb2 : 11 * M ^ 2 + 98 * M + 49 ≤ 64 * 89 * R)
    (hnb3 : 13 * M ^ 2 + 98 * M + 49 ≤ 64 * 105 * R)
    (hnb4 : 15 * M ^ 2 + 98 * M + 49 ≤ 64 * 121 * R) :
    let m1 := M / 2
    let m2 := 5 * M / 8
    let m3 := 3 * M / 4
    let m4 := 7 * M / 8
    m1 ≤ m2 ∧ m2 ≤ m3 ∧ m3 ≤ m4 ∧ m4 ≤ M ∧
    m1 ^ 2 ≤ 0 ^ 2 + 129 * R ∧
    m2 ^ 2 ≤ m1 ^ 2 + 73 * R ∧
    m3 ^ 2 ≤ m2 ^ 2 + 89 * R ∧
    m4 ^ 2 ≤ m3 ^ 2 + 105 * R ∧
    M ^ 2 ≤ m4 ^ 2 + 121 * R := by
  dsimp only
  set m1 := M / 2 with hm1_def
  set m2 := 5 * M / 8 with hm2_def
  set m3 := 3 * M / 4 with hm3_def
  set m4 := 7 * M / 8 with hm4_def
  have hm1_le : 2 * m1 ≤ M := Nat.mul_div_le M 2
  have hm1_ge : M ≤ 2 * m1 + 1 := by
    have hlt := Nat.lt_div_mul_add (a := M) (b := 2) (by decide)
    rw [← hm1_def] at hlt
    linarith
  have hm2_le : 8 * m2 ≤ 5 * M := Nat.mul_div_le (5 * M) 8
  have hm2_ge : 5 * M ≤ 8 * m2 + 7 := by
    have hlt := Nat.lt_div_mul_add (a := 5 * M) (b := 8) (by decide)
    rw [← hm2_def] at hlt
    linarith
  have hm3_le : 4 * m3 ≤ 3 * M := Nat.mul_div_le (3 * M) 4
  have hm3_ge : 3 * M ≤ 4 * m3 + 3 := by
    have hlt := Nat.lt_div_mul_add (a := 3 * M) (b := 4) (by decide)
    rw [← hm3_def] at hlt
    linarith
  have hm4_le : 8 * m4 ≤ 7 * M := Nat.mul_div_le (7 * M) 8
  have hm4_ge : 7 * M ≤ 8 * m4 + 7 := by
    have hlt := Nat.lt_div_mul_add (a := 7 * M) (b := 8) (by decide)
    rw [← hm4_def] at hlt
    linarith
  have hm12 : m1 ≤ m2 := by rw [hm1_def, hm2_def]; omega
  have hm23 : m2 ≤ m3 := by rw [hm2_def, hm3_def]; omega
  have hm34 : m3 ≤ m4 := by rw [hm3_def, hm4_def]; omega
  have hm4M : m4 ≤ M := by rw [hm4_def]; omega
  have div64 : ∀ a b : Nat, 64 * a ≤ 64 * b → a ≤ b := fun a b h =>
    Nat.le_of_mul_le_mul_left h (by decide)
  refine ⟨hm12, hm23, hm34, hm4M, ?_, ?_, ?_, ?_, ?_⟩
  · apply div64
    have h1 : 64 * m1 ^ 2 ≤ 16 * M ^ 2 := by nlinarith only [hm1_le]
    have h2 : 16 * M ^ 2 ≤ 64 * (0 ^ 2 + 129 * R) := by linarith only [hnb0]
    exact h1.trans h2
  · apply div64
    have h1 : 64 * m2 ^ 2 ≤ 25 * M ^ 2 := by nlinarith only [hm2_le]
    have h2 : 16 * M ^ 2 ≤ 64 * m1 ^ 2 + 32 * M + 16 := by nlinarith only [hm1_le, hm1_ge]
    have h3 : 25 * M ^ 2 ≤ 64 * m1 ^ 2 + (9 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m1 ^ 2 + (9 * M ^ 2 + 98 * M + 49) ≤ 64 * (m1 ^ 2 + 73 * R) := by linarith only [hnb1]
    exact h1.trans (h3.trans h4)
  · apply div64
    have h1 : 64 * m3 ^ 2 ≤ 36 * M ^ 2 := by nlinarith only [hm3_le]
    have h2 : 25 * M ^ 2 ≤ 64 * m2 ^ 2 + 70 * M + 49 := by nlinarith only [hm2_le, hm2_ge]
    have h3 : 36 * M ^ 2 ≤ 64 * m2 ^ 2 + (11 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m2 ^ 2 + (11 * M ^ 2 + 98 * M + 49) ≤ 64 * (m2 ^ 2 + 89 * R) := by linarith only [hnb2]
    exact h1.trans (h3.trans h4)
  · apply div64
    have h1 : 64 * m4 ^ 2 ≤ 49 * M ^ 2 := by nlinarith only [hm4_le]
    have h2 : 36 * M ^ 2 ≤ 64 * m3 ^ 2 + 72 * M + 36 := by nlinarith only [hm3_le, hm3_ge]
    have h3 : 49 * M ^ 2 ≤ 64 * m3 ^ 2 + (13 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m3 ^ 2 + (13 * M ^ 2 + 98 * M + 49) ≤ 64 * (m3 ^ 2 + 105 * R) := by linarith only [hnb3]
    exact h1.trans (h3.trans h4)
  · apply div64
    have h2 : 49 * M ^ 2 ≤ 64 * m4 ^ 2 + 98 * M + 49 := by nlinarith only [hm4_le, hm4_ge]
    have h3 : 64 * M ^ 2 ≤ 64 * m4 ^ 2 + (15 * M ^ 2 + 98 * M + 49) := by linarith only [h2]
    have h4 : 64 * m4 ^ 2 + (15 * M ^ 2 + 98 * M + 49) ≤ 64 * (m4 ^ 2 + 121 * R) := by linarith only [hnb4]
    exact h3.trans h4

theorem one_le_budget_add_prod_survFactor (budget : Nat)
    (hpos : 1 ≤ budget) (hsmall : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (1 : ENNReal) ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS +
      ∏ i ∈ Finset.range (budget + 2 ^ 39), survFactor i := by
  change budget ≤ 2 ^ 120 at hsmall
  change (1 : ENNReal) ≤ (budget : ENNReal) / 2 ^ 120 +
    ∏ i ∈ Finset.range (budget + 2 ^ 39), survFactor i
  set M := budget + 2 ^ 39
  have hM_lt : M ≤ 2 ^ 238 := (Nat.add_le_add_right hsmall (2 ^ 39)).trans (by decide)
  by_cases hmid : budget ≤ 2 ^ 118
  · have hweier := one_le_prod_add_sum (Finset.range M) survFactor (fun i => (i : ENNReal) / 2 ^ 238)
      (fun i _ => survFactor_le_one i)
      (fun i hi => one_le_survFactor_add i ((Nat.le_of_lt (Finset.mem_range.mp hi)).trans hM_lt))
    have hsum_nat : 2 * (∑ i ∈ Finset.range M, i) ≤ budget * 2 ^ 119 := by
      have h2 : 2 * (∑ i ∈ Finset.range M, i) ≤ M ^ 2 := by
        simpa [Nat.Ico_zero_eq_range] using two_mul_sum_Ico_le 0 M (Nat.zero_le M)
      have hq2 : budget * budget ≤ budget * 2 ^ 118 := Nat.mul_le_mul_left budget hmid
      have hMsq : M ^ 2 ≤ budget * 2 ^ 119 := by
        have h1 : M ^ 2 = budget * budget + (2 * 2 ^ 39 * budget + 2 ^ 78) := by
          dsimp only [M]; ring
        have h2' : 2 * 2 ^ 39 * budget + 2 ^ 78 ≤ budget * 2 ^ 118 := by
          have h3 : 2 ^ 78 ≤ budget * 2 ^ 78 := Nat.le_mul_of_pos_left _ hpos
          have h4 : 2 * 2 ^ 39 + 2 ^ 78 ≤ 2 ^ 118 := by decide
          calc
            2 * 2 ^ 39 * budget + 2 ^ 78 ≤ budget * (2 * 2 ^ 39) + budget * 2 ^ 78 :=
              Nat.add_le_add (by rw [mul_comm]) h3
            _ = budget * (2 * 2 ^ 39 + 2 ^ 78) := (Nat.mul_add _ _ _).symm
            _ ≤ budget * 2 ^ 118 := Nat.mul_le_mul_left budget h4
        calc
          M ^ 2 = budget * budget + (2 * 2 ^ 39 * budget + 2 ^ 78) := h1
          _ ≤ budget * 2 ^ 118 + budget * 2 ^ 118 := Nat.add_le_add hq2 h2'
          _ = budget * 2 ^ 119 := by ring
      exact h2.trans hMsq
    have hsum : (∑ i ∈ Finset.range M, (i : ENNReal) / 2 ^ 238) ≤ (budget : ENNReal) / 2 ^ 120 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum, ← div_eq_mul_inv]
      have hcast : ((2 * (∑ i ∈ Finset.range M, i) : Nat) : ENNReal) ≤ ((budget * 2 ^ 119 : Nat) : ENNReal) :=
        Nat.cast_le.mpr hsum_nat
      calc
        ((∑ i ∈ Finset.range M, i : Nat) : ENNReal) / 2 ^ 238
          = ((2 : ENNReal) * ((∑ i ∈ Finset.range M, i : Nat) : ENNReal)) / (2 * 2 ^ 238) :=
            (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
        _ ≤ ((budget * 2 ^ 119 : Nat) : ENNReal) / (2 * 2 ^ 238) := by
            apply ENNReal.div_le_div_right
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast
        _ = (budget : ENNReal) / 2 ^ 120 := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) * 2 ^ 238 = 2 ^ 120 * 2 ^ 119 by
              rw [← pow_succ', ← pow_add]]
            exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)
    rw [add_comm]
    exact hweier.trans (add_le_add le_rfl hsum)
  · have hqlo : 16 * 2 ^ 114 < budget := by
      rw [show 16 * 2 ^ 114 = 2 ^ 118 by decide]
      exact Nat.lt_of_not_le hmid
    have hqhi : budget ≤ 64 * 2 ^ 114 := by
      rw [show 64 * 2 ^ 114 = 2 ^ 120 by decide]
      exact hsmall
    set k := (budget - 1) / 2 ^ 114 with hk_def
    have hk_lo : 16 ≤ k :=
      (Nat.le_div_iff_mul_le (by decide)).mpr (Nat.le_sub_one_of_lt hqlo)
    have hk_hi : k < 64 :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr ((Nat.sub_lt hpos Nat.one_pos).trans_le hqhi)
    have hi_mem : k - 16 ∈ List.range 48 := List.mem_range.mpr (by omega)
    have hcov := List.all_eq_true.mp survivalGrid_covers (k - 16) hi_mem
    obtain ⟨⟨u, v⟩, hp_mem, hp_cov⟩ := List.any_eq_true.mp hcov
    have hp_cov' : u ≤ k ∧ k + 1 ≤ v := by
      have hk_eq : k - 16 + 16 = k := by omega
      simpa only [hk_eq, decide_eq_true_eq] using hp_cov
    have hp_ok : 16 ≤ u ∧ u < v ∧ v ≤ 64 ∧
        (64 - u) * 2 ^ 94 ≤
          (2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
          (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
          (2 ^ 20 - 121 * v ^ 2) := by
      have h := List.all_eq_true.mp survivalGrid_ok (u, v) hp_mem
      simpa only [gridCellOk, decide_eq_true_eq] using h
    obtain ⟨hu16, huv, hv64, hgrid⟩ := hp_ok
    have hv17 : 17 ≤ v := Nat.succ_le_of_lt (hu16.trans_lt huv)
    have huq : u * 2 ^ 114 ≤ budget := by
      have hk1 : k * 2 ^ 114 ≤ budget - 1 := by
        rw [hk_def]; exact Nat.div_mul_le_self _ _
      have hk2 : u * 2 ^ 114 ≤ k * 2 ^ 114 := Nat.mul_le_mul_right _ hp_cov'.1
      exact (hk2.trans hk1).trans (Nat.sub_le budget 1)
    have hqv : budget ≤ v * 2 ^ 114 := by
      have hk1 : budget - 1 < k * 2 ^ 114 + 2 ^ 114 := by
        rw [hk_def]; exact Nat.lt_div_mul_add (a := budget - 1) (b := 2 ^ 114) (by decide)
      have hk2 : budget ≤ (k + 1) * 2 ^ 114 := by
        rw [Nat.add_mul, one_mul]
        exact Nat.le_of_pred_lt hk1
      have hk3 : (k + 1) * 2 ^ 114 ≤ v * 2 ^ 114 := Nat.mul_le_mul_right _ hp_cov'.2
      exact hk2.trans hk3
    have hM_le : M ≤ v * 2 ^ 114 + 2 ^ 39 := Nat.add_le_add_right hqv (2 ^ 39)
    obtain ⟨hm12, hm23, hm34, hm4M, hb0', hb1', hb2', hb3', hb4'⟩ :=
      five_block_sq_step M (v ^ 2 * 2 ^ 219)
        (five_block_nat_bound M v 16 129 hv17 hv64 hM_le (by decide) rfl)
        (five_block_nat_bound M v 9 73 hv17 hv64 hM_le (by decide) rfl)
        (five_block_nat_bound M v 11 89 hv17 hv64 hM_le (by decide) rfl)
        (five_block_nat_bound M v 13 105 hv17 hv64 hM_le (by decide) rfl)
        (five_block_nat_bound M v 15 121 hv17 hv64 hM_le (by decide) rfl)
    have hb0 : (M / 2) ^ 2 ≤ 0 ^ 2 + 129 * v ^ 2 * 2 ^ 219 := by
      simpa only [Nat.mul_assoc] using hb0'
    have hb1 : (5 * M / 8) ^ 2 ≤ (M / 2) ^ 2 + 73 * v ^ 2 * 2 ^ 219 := by
      simpa only [Nat.mul_assoc] using hb1'
    have hb2 : (3 * M / 4) ^ 2 ≤ (5 * M / 8) ^ 2 + 89 * v ^ 2 * 2 ^ 219 := by
      simpa only [Nat.mul_assoc] using hb2'
    have hb3 : (7 * M / 8) ^ 2 ≤ (3 * M / 4) ^ 2 + 105 * v ^ 2 * 2 ^ 219 := by
      simpa only [Nat.mul_assoc] using hb3'
    have hb4 : M ^ 2 ≤ (7 * M / 8) ^ 2 + 121 * v ^ 2 * 2 ^ 219 := by
      simpa only [Nat.mul_assoc] using hb4'
    set m1 := M / 2
    set m2 := 5 * M / 8
    set m3 := 3 * M / 4
    set m4 := 7 * M / 8
    have hm01 : 0 ≤ m1 := Nat.zero_le _
    have hm4_lt : m4 ≤ 2 ^ 238 := hm4M.trans hM_lt
    have hm3_lt : m3 ≤ 2 ^ 238 := hm34.trans hm4_lt
    have hm2_lt : m2 ≤ 2 ^ 238 := hm23.trans hm3_lt
    have hm1_lt : m1 ≤ 2 ^ 238 := hm12.trans hm2_lt
    have hvsq : v ^ 2 ≤ 64 ^ 2 := Nat.pow_le_pow_left hv64 2
    have hcv0 : 129 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 129 hvsq).trans (by decide)
    have hcv1 : 73 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 73 hvsq).trans (by decide)
    have hcv2 : 89 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 89 hvsq).trans (by decide)
    have hcv3 : 105 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 105 hvsq).trans (by decide)
    have hcv4 : 121 * v ^ 2 ≤ 2 ^ 20 := (Nat.mul_le_mul_left 121 hvsq).trans (by decide)
    have hp0 := block_prod_lower 0 m1 129 v hm01 hm1_lt hcv0 hb0
    have hp1 := block_prod_lower m1 m2 73 v hm12 hm2_lt hcv1 hb1
    have hp2 := block_prod_lower m2 m3 89 v hm23 hm3_lt hcv2 hb2
    have hp3 := block_prod_lower m3 m4 105 v hm34 hm4_lt hcv3 hb3
    have hp4 := block_prod_lower m4 M 121 v hm4M hM_lt hcv4 hb4
    have hmul5 := mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hp0 hp1) hp2) hp3) hp4
    rw [← prod_range_split5 survFactor m1 m2 m3 m4 M hm12 hm23 hm34 hm4M] at hmul5
    have hprod_ge : ((64 - u : Nat) : ENNReal) / 64 ≤ ∏ i ∈ Finset.range M, survFactor i := by
      have hcast_grid : (((64 - u) * 2 ^ 94 : Nat) : ENNReal) ≤
          ((((2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
             (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
             (2 ^ 20 - 121 * v ^ 2) : Nat)) : ENNReal) :=
        Nat.cast_le.mpr hgrid
      calc
        ((64 - u : Nat) : ENNReal) / 64
          = (((64 - u) * 2 ^ 94 : Nat) : ENNReal) / 2 ^ 100 := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 100 = 64 * 2 ^ 94 by
              rw [show (64 : ENNReal) = 2 ^ 6 by norm_num, ← pow_add]]
            exact (ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)).symm
        _ ≤ ((((2 ^ 20 - 129 * v ^ 2) * (2 ^ 20 - 73 * v ^ 2) *
               (2 ^ 20 - 89 * v ^ 2) * (2 ^ 20 - 105 * v ^ 2) *
               (2 ^ 20 - 121 * v ^ 2) : Nat)) : ENNReal) / 2 ^ 100 :=
            ENNReal.div_le_div_right hcast_grid _
        _ = (((2 ^ 20 - 129 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 73 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 89 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 105 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) *
            (((2 ^ 20 - 121 * v ^ 2 : Nat) : ENNReal) / 2 ^ 20) := by
            simp only [Nat.cast_mul, div_eq_mul_inv]
            have hinv : ((2 : ENNReal) ^ 100)⁻¹ = ((2 : ENNReal) ^ 20)⁻¹ ^ 5 := by
              rw [← ENNReal.inv_pow, ← pow_mul]
            rw [hinv]
            ring
        _ ≤ ∏ i ∈ Finset.range M, survFactor i := hmul5
    have hu_le : (u : ENNReal) / 64 ≤ (budget : ENNReal) / 2 ^ 120 := by
      calc
        (u : ENNReal) / 64
          = ((u * 2 ^ 114 : Nat) : ENNReal) / 2 ^ 120 := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            rw [show (2 : ENNReal) ^ 120 = 64 * 2 ^ 114 by
              rw [show (64 : ENNReal) = 2 ^ 6 by norm_num, ← pow_add]]
            exact (ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)).symm
        _ ≤ (budget : ENNReal) / 2 ^ 120 :=
            ENNReal.div_le_div_right (Nat.cast_le.mpr huq) _
    have h1 : (1 : ENNReal) = (u : ENNReal) / 64 + ((64 - u : Nat) : ENNReal) / 64 := by
      rw [← ENNReal.add_div, ← Nat.cast_add, Nat.add_sub_of_le (huv.le.trans hv64), Nat.cast_ofNat]
      exact (ENNReal.div_self (by positivity) (by finiteness)).symm
    rw [h1]
    exact add_le_add hu_le hprod_ge

private theorem binding_fixed_le_search (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (hsound : CheckSound h768) (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$>
      (oracle.run adversary))) ≤
    (prEvent ((ReplyCollision238) <$> (fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (submission.scheme.Breaks oracle)]
  unfold boundedCollisionSearch
  rw [fixed_oracle_run_bind]
  have hmap : fixedOracleRun oracle (limitPublicQueries adversary budget) =
      Prod.fst <$> oracle.run (limitPublicQueries adversary budget) := rfl
  rw [hmap, bind_map_left, prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨res, calls⟩
  cases res with
  | none =>
    simp [fixed_oracle_run_pure]
  | some claim =>
    by_cases hwin : submission.scheme.Breaks oracle claim
    · simp only [Option.some.injEq, exists_eq_left', hwin, ite_true]
      obtain ⟨⟨i, hi0, hi1, hvalne⟩, hacc0, hacc1⟩ := hwin
      obtain ⟨e0, t0, hrun0, hw0⟩ := hsound oracle
        ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩ hacc0
      obtain ⟨e1, t1, hrun1, hw1⟩ := hsound oracle
        ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩ hacc1
      obtain ⟨w0, hidx0, hv0, hrt0, htr0⟩ := hw0 i hi0
      obtain ⟨w1, hidx1, hv1, hrt1, htr1⟩ := hw1 i hi1
      have hcol := collision238_of_paths (fun x => oracle.compression (x.cast h768.symm)) w0 w1
        (hidx0.trans hidx1.symm) (by rw [hv0, hv1]; exact hvalne) (hrt0.trans hrt1.symm)
      obtain ⟨x, hx, y, hy, hxy, hlow⟩ := hcol
      have hmemx : (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ t0 ++ t1 := by
        rcases List.mem_append.mp hx with hx0 | hx1
        · exact List.mem_append_left _ (htr0 x hx0)
        · exact List.mem_append_right _ (htr1 x hx1)
      have hmemy : (y.cast h768.symm, oracle.compression (y.cast h768.symm)) ∈ t0 ++ t1 := by
        rcases List.mem_append.mp hy with hy0 | hy1
        · exact List.mem_append_left _ (htr0 y hy0)
        · exact List.mem_append_right _ (htr1 y hy1)
      have hrc : ReplyCollision238 (t0 ++ t1) :=
        ⟨_, hmemx, _, hmemy, fun heq => hxy (by simpa using congrArg (BitVec.cast h768) heq), hlow⟩
      rw [fixed_oracle_run_bind, hrun0, pure_bind, fixed_oracle_run_bind, hrun1, pure_bind,
        fixed_oracle_run_pure, prEvent_pure, ite_eq_left_iff.mpr (fun hn => (hn hrc).elim), mul_one]
    · simp [hwin]

/-- Master Binding Theorem: `CheckSound` implies the challenge's full adaptive `Binding` guarantee. -/
theorem binding_of_check_sound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (hsound : CheckSound h768) : submission.scheme.Binding := by
  intro adversary budget hpos
  by_cases hlarge : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · have hone : (1 : ENNReal) ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness)), one_mul]
      exact_mod_cast hlarge
    exact (prEvent_le_one _).trans hone
  · have hsmall : budget ≤ 2 ^ BINDING_SECURITY_BITS := by omega
    have hred :
        (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ budget) <$>
          (Scheme.bindingGame adversary))) ≤
        (prEvent ((ReplyCollision238) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using binding_fixed_le_search h768 hsound oracle adversary budget
    have hperm : ∀ permutation : Perm,
        (prEvent ((ReplyCollision238) <$> (($ᵗ Compression) >>= fun compression =>
          fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      intro permutation
      have heq := (EvalDistEq.of_evalDist_eq
        (compression_sampling_empty permutation (boundedCollisionSearch adversary budget))).prEvent_eq
          ReplyCollision238
      simp only [prEvent_map] at heq
      rw [← heq]
      let run := compressionRun permutation (boundedCollisionSearch adversary budget) ∅
      have hdet : prEvent ((fun result => ReplyCollision238 result.1) <$> run) ≤
          prEvent ((fun result => CacheHasCollision238 result.2) <$> run) :=
        prEvent_mono_of_support _ _ _ fun result reached hcol =>
          search_replyCollision_in_cache permutation adversary budget result reached hcol
      have hsurv : (∏ i ∈ Finset.range (budget + 2 ^ 39), survFactor i) ≤
          prEvent ((fun result => ¬ CacheHasCollision238 result.2) <$> run) :=
        compression_noCollision238_bound permutation (boundedCollisionSearch adversary budget)
          (budget + 2 ^ 39) (boundedCollisionSearch_bound adversary budget)
      have hpart : prEvent ((fun result => CacheHasCollision238 result.2) <$> run) +
          prEvent ((fun result => ¬ CacheHasCollision238 result.2) <$> run) = 1 :=
        (prEvent_add_prEvent_not_eq_prEvent_true run (fun result => CacheHasCollision238 result.2)).trans
          (OracleComp.prEvent_true_eq_one run)
      have h1 := one_le_budget_add_prod_survFactor budget hpos hsmall
      have hfin : (∏ i ∈ Finset.range (budget + 2 ^ 39), survFactor i) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top
          (Finset.prod_le_one (fun _ _ => survFactor_le_one _))
      have hcol_le : prEvent ((fun result => CacheHasCollision238 result.2) <$> run) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
        have hcomb : prEvent ((fun result => CacheHasCollision238 result.2) <$> run) +
            (∏ i ∈ Finset.range (budget + 2 ^ 39), survFactor i) ≤
            (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS +
            (∏ i ∈ Finset.range (budget + 2 ^ 39), survFactor i) :=
          (add_le_add le_rfl hsurv).trans (hpart.le.trans h1)
        exact (ENNReal.add_le_add_iff_right hfin).mp hcomb
      exact hdet.trans hcol_le
    have hsampled :
        (prEvent ((ReplyCollision238) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      have hswap := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
        (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget))
      have hpr := (EvalDistEq.of_evalDist_eq hswap).prEvent_eq ReplyCollision238
      simp only [Oracle.sample, bind_assoc, pure_bind]
      rw [hpr]
      apply prEvent_bind_le_of_forall_le_of_support
      intro permutation _
      exact hperm permutation
    exact hred.trans hsampled

end CommitGolfCandidate
