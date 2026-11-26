import CommitGolfCandidate.MoonImage
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.Execution

/-! Complete 240-bit adaptive position-binding reduction for the r=1 3-ary/binary tree.
Rather than re-implementing a proof parser for deduplicated cap openings, the collision detector
directly executes the submitted deterministic `check` image on both conflicting claims while
recording every `(input, answer)` compression query in `traceCompressionReplies`.
With 240-bit truncated internal digests, `(q + 2^37)^2 / (2 * 2^240) <= q / 2^120` holds for
every `1 <= q <= 2^120` with over 160 bits of headroom on the replay term. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### Witness Paths and Pure 240-bit Structural Collision Extraction -/

structure WitnessPath where
  index : Index
  value : Entry
  salt : Salt192
  l0Sib0 : Digest
  l0Sib1 : Digest
  binSib : Nat → Digest

def WitnessPath.l0Input (c : Comp96) (w : WitnessPath) : BitVec 768 :=
  let d0 := leafDigest c w.index w.salt w.value
  let r := w.index.val % 3
  if r = 0 then ternaryInput d0 w.l0Sib0 w.l0Sib1
  else if r = 1 then ternaryInput w.l0Sib0 d0 w.l0Sib1
  else ternaryInput w.l0Sib0 w.l0Sib1 d0

def WitnessPath.evalL1 (c : Comp96) (w : WitnessPath) : Digest :=
  if w.index.val / 3 = FULL_TRIPLETS then
    leafDigest c w.index w.salt w.value
  else
    c (w.l0Input c)

def WitnessPath.evalLevel (c : Comp96) (w : WitnessPath) : Nat → Digest
  | 0 => leafDigest c w.index w.salt w.value
  | 1 => w.evalL1 c
  | l + 2 =>
      let prev := l + 1
      let cur := w.evalLevel c prev
      let idx := (w.index.val / 3) >>> (prev - 1)
      if (idx ^^^ 1) < levelSize prev then
        let inp := if idx % 2 = 0 then binaryInput cur (w.binSib prev)
                   else binaryInput (w.binSib prev) cur
        let raw := c inp
        if l + 2 = 24 then raw else mask240 raw
      else cur

def WitnessPath.evalRoot (c : Comp96) (w : WitnessPath) : Digest :=
  w.evalLevel c 24

def WitnessPath.leafInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  let iU := leafUInput w.value
  let u := c iU
  let iA := leafAInput u w.value
  let a := c iA
  let iB := leafBInput w.value
  let b := c iB
  let iF := leafFinalInput w.index a b w.salt
  [iU, iA, iB, iF]

def WitnessPath.levelInput (c : Comp96) (w : WitnessPath) (prev : Nat) : List (BitVec 768) :=
  let cur := w.evalLevel c prev
  let idx := (w.index.val / 3) >>> (prev - 1)
  if (idx ^^^ 1) < levelSize prev then
    [if idx % 2 = 0 then binaryInput cur (w.binSib prev) else binaryInput (w.binSib prev) cur]
  else []

def WitnessPath.pathInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  w.leafInputs c ++
  (if w.index.val / 3 = FULL_TRIPLETS then [] else [w.l0Input c]) ++
  (List.range 23).flatMap (fun k => w.levelInput c (k + 1))

def HasCollision240 (c : Comp96) (inputs : List (BitVec 768)) : Prop :=
  ∃ x ∈ inputs, ∃ y ∈ inputs, x ≠ y ∧ low240 (c x) = low240 (c y)

private theorem mem_pathInputs_leaf (c : Comp96) (w : WitnessPath) (x : BitVec 768)
    (hx : x ∈ w.leafInputs c) : x ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs
  simp [hx]

private theorem mem_pathInputs_l0 (c : Comp96) (w : WitnessPath)
    (hfull : w.index.val / 3 ≠ FULL_TRIPLETS) : w.l0Input c ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs
  simp [hfull]

private theorem mem_pathInputs_level (c : Comp96) (w : WitnessPath) (prev : Nat)
    (hp1 : 1 ≤ prev) (hp2 : prev ≤ 23) (x : BitVec 768) (hx : x ∈ w.levelInput c prev) :
    x ∈ w.pathInputs c := by
  unfold WitnessPath.pathInputs
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨prev - 1, List.mem_range.mpr (by omega), by simpa [show prev - 1 + 1 = prev by omega] using hx⟩

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

private theorem leaf_collision240 (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hdig : leafDigest c w1.index w1.salt w1.value = leafDigest c w2.index w2.salt w2.value) :
    HasCollision240 c (w1.pathInputs c ++ w2.pathInputs c) := by
  set iU₁ := leafUInput w1.value; set iU₂ := leafUInput w2.value
  set u₁ := c iU₁; set u₂ := c iU₂
  set iA₁ := leafAInput u₁ w1.value; set iA₂ := leafAInput u₂ w2.value
  set a₁ := c iA₁; set a₂ := c iA₂
  set iB₁ := leafBInput w1.value; set iB₂ := leafBInput w2.value
  set b₁ := c iB₁; set b₂ := c iB₂
  set iF₁ := leafFinalInput w1.index a₁ b₁ w1.salt
  set iF₂ := leafFinalInput w2.index a₂ b₂ w2.salt
  have hmem : ∀ x ∈ w1.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_left _ (mem_pathInputs_leaf c w1 x hx)
  have hmem2 : ∀ x ∈ w2.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_right _ (mem_pathInputs_leaf c w2 x hx)
  by_cases hF : iF₁ ≠ iF₂
  · exact ⟨iF₁, hmem _ (by simp [WitnessPath.leafInputs, iF₁, a₁, iA₁, u₁, iU₁, b₁, iB₁]),
      iF₂, hmem2 _ (by simp [WitnessPath.leafInputs, iF₂, a₂, iA₂, u₂, iU₂, b₂, iB₂]),
      hF, congrArg low240 hdig⟩
  · push_neg at hF
    have hF' : leafFinalInput w2.index a₁ b₁ w1.salt = leafFinalInput w2.index a₂ b₂ w2.salt := by
      simpa [iF₁, iF₂, hidx] using hF
    obtain ⟨ha, hb, _⟩ := leafFinalInput_inj hF'
    by_cases hB : iB₁ ≠ iB₂
    · exact ⟨iB₁, hmem _ (by simp [WitnessPath.leafInputs, iB₁]),
        iB₂, hmem2 _ (by simp [WitnessPath.leafInputs, iB₂]),
        hB, congrArg low240 hb⟩
    · push_neg at hB
      by_cases hA : iA₁ ≠ iA₂
      · exact ⟨iA₁, hmem _ (by simp [WitnessPath.leafInputs, iA₁, u₁, iU₁]),
          iA₂, hmem2 _ (by simp [WitnessPath.leafInputs, iA₂, u₂, iU₂]),
          hA, congrArg low240 ha⟩
      · push_neg at hA
        obtain ⟨hvMid, hu⟩ := bv_append_inj (show w1.value.extractLsb' 768 512 ++ u₁ =
          w2.value.extractLsb' 768 512 ++ u₂ from hA)
        by_cases hU : iU₁ ≠ iU₂
        · exact ⟨iU₁, hmem _ (by simp [WitnessPath.leafInputs, iU₁]),
            iU₂, hmem2 _ (by simp [WitnessPath.leafInputs, iU₂]),
            hU, congrArg low240 hu⟩
        · push_neg at hU
          exact (hne (entry_eq_of_late_slices w1.value w2.value hU hvMid hB)).elim

private theorem l1_step_collision240 (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index)
    (heq : w1.evalL1 c = w2.evalL1 c) :
    leafDigest c w1.index w1.salt w1.value = leafDigest c w2.index w2.salt w2.value ∨
    HasCollision240 c (w1.pathInputs c ++ w2.pathInputs c) := by
  unfold WitnessPath.evalL1 at heq
  rw [hidx] at heq
  by_cases hfull : w2.index.val / 3 = FULL_TRIPLETS
  · left
    simp only [hfull, ite_true] at heq
    simpa [hidx] using heq
  · simp only [hfull, ite_false] at heq
    by_cases hne : w1.l0Input c ≠ w2.l0Input c
    · right
      exact ⟨w1.l0Input c, List.mem_append_left _ (mem_pathInputs_l0 c w1 (by rw [hidx]; exact hfull)),
        w2.l0Input c, List.mem_append_right _ (mem_pathInputs_l0 c w2 hfull),
        hne, congrArg low240 heq⟩
    · left
      push_neg at hne
      unfold WitnessPath.l0Input at hne
      rw [hidx] at hne
      dsimp only at hne
      split at hne
      · have := congrArg (fun v : BitVec 768 => v.extractLsb' 0 256) hne
        simpa [ternaryInput_d0, hidx] using this
      · split at hne
        · have := congrArg (fun v : BitVec 768 => v.extractLsb' 256 256) hne
          simpa [ternaryInput_d1, hidx] using this
        · have := congrArg (fun v : BitVec 768 => v.extractLsb' 512 256) hne
          simpa [ternaryInput_d2, hidx] using this

private theorem bin_step_collision240 (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (prev : Nat) (hp1 : 1 ≤ prev) (hp2 : prev ≤ 23)
    (heq : w1.evalLevel c (prev + 1) = w2.evalLevel c (prev + 1)) :
    w1.evalLevel c prev = w2.evalLevel c prev ∨
    HasCollision240 c (w1.pathInputs c ++ w2.pathInputs c) := by
  obtain ⟨m, rfl⟩ : ∃ m, prev = m + 1 := ⟨prev - 1, by omega⟩
  unfold WitnessPath.evalLevel at heq
  rw [hidx] at heq
  dsimp only at heq
  simp only [Nat.add_sub_cancel] at heq
  set idx := (w2.index.val / 3) >>> m
  by_cases hpair : (idx ^^^ 1) < levelSize (m + 1)
  · rw [if_pos hpair, if_pos hpair] at heq
    set inp1 := if idx % 2 = 0 then binaryInput (w1.evalLevel c (m + 1)) (w1.binSib (m + 1))
                else binaryInput (w1.binSib (m + 1)) (w1.evalLevel c (m + 1))
    set inp2 := if idx % 2 = 0 then binaryInput (w2.evalLevel c (m + 1)) (w2.binSib (m + 1))
                else binaryInput (w2.binSib (m + 1)) (w2.evalLevel c (m + 1))
    by_cases hne : inp1 ≠ inp2
    · right
      have hlow : low240 (c inp1) = low240 (c inp2) := by
        by_cases h24 : m + 2 = 24
        · rw [if_pos h24, if_pos h24] at heq
          exact congrArg low240 heq
        · rw [if_neg h24, if_neg h24] at heq
          exact (mask240_eq_iff _ _).mp heq
      have hm1 : inp1 ∈ w1.levelInput c (m + 1) := by
        unfold WitnessPath.levelInput; rw [hidx]; simp [idx, hpair, inp1]
      have hm2 : inp2 ∈ w2.levelInput c (m + 1) := by
        unfold WitnessPath.levelInput; simp [idx, hpair, inp2]
      exact ⟨inp1, List.mem_append_left _ (mem_pathInputs_level c w1 (m + 1) (by omega) hp2 _ hm1),
        inp2, List.mem_append_right _ (mem_pathInputs_level c w2 (m + 1) (by omega) hp2 _ hm2),
        hne, hlow⟩
    · left
      push_neg at hne
      by_cases heven : idx % 2 = 0
      · simp only [inp1, inp2, heven, ite_true] at hne
        have := congrArg (fun v : BitVec 768 => v.extractLsb' 0 256) hne
        simpa [binaryInput_left] using this
      · simp only [inp1, inp2, heven, ite_false] at hne
        have := congrArg (fun v : BitVec 768 => v.extractLsb' 256 256) hne
        simpa [binaryInput_right] using this
  · left
    rw [if_neg hpair, if_neg hpair] at heq
    exact heq

/-- Two conflicting witness paths reaching the same root MUST witness a 240-bit compression collision. -/
theorem collision240_of_paths (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hroot : w1.evalRoot c = w2.evalRoot c) :
    HasCollision240 c (w1.pathInputs c ++ w2.pathInputs c) := by
  have descend : ∀ k ≤ 23,
      w1.evalLevel c (24 - k) = w2.evalLevel c (24 - k) ∨
      HasCollision240 c (w1.pathInputs c ++ w2.pathInputs c) := by
    intro k hk
    induction k with
    | zero => left; exact hroot
    | succ k ih =>
      rcases ih (by omega) with heq | hcol
      · have hstep : 24 - k = (24 - (k + 1)) + 1 := by omega
        rw [hstep] at heq
        exact bin_step_collision240 c w1 w2 hidx (24 - (k + 1)) (by omega) (by omega) heq
      · exact Or.inr hcol
  rcases descend 23 (by omega) with hl1 | hcol
  · rcases l1_step_collision240 c w1 w2 hidx hl1 with hleaf | hcol
    · exact leaf_collision240 c w1 w2 hidx hne hleaf
    · exact hcol
  · exact hcol

/-! ### 240-bit Lazy Compression ROM Birthday Bound -/

def CacheHasCollision240 (cache : CompressionCache) : Prop :=
  ∃ (x y : BitVec COMPRESSION_INPUT_LENGTH) (vx vy : Digest),
    x ≠ y ∧ cache x = some vx ∧ cache y = some vy ∧ low240 vx = low240 vy

private theorem card_low240_preimage (targets : Finset (BitVec 240))
    [DecidablePred (fun ans : Digest => low240 ans ∈ targets)] :
    (Finset.univ.filter (fun ans : Digest => low240 ans ∈ targets)).card ≤ 2 ^ 16 * targets.card := by
  have hinj : Set.InjOn (fun ans : Digest => (ans.extractLsb' 240 16, low240 ans))
      (Finset.univ.filter (fun ans : Digest => low240 ans ∈ targets) : Set Digest) := by
    intro a _ b _ h
    have hhi : a.extractLsb' 240 16 = b.extractLsb' 240 16 := congrArg Prod.fst h
    have hlo : low240 a = low240 b := congrArg Prod.snd h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h240 : i < 240
    · have := congrArg (fun v : BitVec 240 => v.getLsbD i) hlo
      simpa only [low240, BitVec.getLsbD_extractLsb', h240, decide_true, Bool.true_and, Nat.zero_add] using this
    · have hi16 : i - 240 < 16 := by omega
      have := congrArg (fun v : BitVec 16 => v.getLsbD (i - 240)) hhi
      simpa only [BitVec.getLsbD_extractLsb', hi16, decide_true, Bool.true_and,
        show 240 + (i - 240) = i by omega] using this
  have hmaps : Set.MapsTo (fun ans : Digest => (ans.extractLsb' 240 16, low240 ans))
      (Finset.univ.filter (fun ans : Digest => low240 ans ∈ targets) : Set Digest)
      ((Finset.univ ×ˢ targets : Finset (BitVec 16 × BitVec 240)) : Set (BitVec 16 × BitVec 240)) := by
    intro ans hans
    rw [Finset.mem_coe, Finset.mem_filter] at hans
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_univ _, hans.2⟩
  calc
    (Finset.univ.filter (fun ans : Digest => low240 ans ∈ targets)).card
      ≤ (Finset.univ ×ˢ targets : Finset (BitVec 16 × BitVec 240)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ : Finset (BitVec 16)).card * targets.card := Finset.card_product _ _
    _ = 2 ^ 16 * targets.card := by rw [Finset.card_univ, Fintype.card_bitVec]

theorem fresh_collision240_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCol : ¬ CacheHasCollision240 cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun ans => CacheHasCollision240 (cache.cacheQuery input ans)) <$>
      ($ᵗ CompressionSpec.Range input))) ≤ (keys.card : ENNReal) / 2 ^ 240 := by
  classical
  let targets : Finset (BitVec 240) :=
    keys.biUnion (fun k => match cache k with | some v => {low240 v} | none => ∅)
  have htargets_card : targets.card ≤ keys.card := by
    calc
      targets.card ≤ ∑ k ∈ keys, (match cache k with | some v => ({low240 v} : Finset (BitVec 240)) | none => ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ keys, 1 := by
        apply Finset.sum_le_sum
        intro k _
        cases cache k <;> simp
      _ = keys.card := by simp
  have hsub : (Finset.univ.filter (fun ans : Digest => CacheHasCollision240 (cache.cacheQuery input ans))) ⊆
      Finset.univ.filter (fun ans : Digest => low240 ans ∈ targets) := by
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
  change (prEvent ((fun ans : Digest => CacheHasCollision240 (cache.cacheQuery input ans)) <$>
    ($ᵗ Digest))) ≤ _
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ 256 := Fintype.card_bitVec 256
  rw [hcard]
  have hcount : (Finset.univ.filter (fun ans : Digest => CacheHasCollision240 (cache.cacheQuery input ans))).card ≤
      2 ^ 16 * keys.card :=
    (Finset.card_le_card hsub).trans ((card_low240_preimage targets).trans (Nat.mul_le_mul_left _ htargets_card))
  calc
    ((Finset.univ.filter (fun ans : Digest => CacheHasCollision240 (cache.cacheQuery input ans))).card : ENNReal) /
        (2 ^ 256 : Nat)
      ≤ ((2 ^ 16 * keys.card : Nat) : ENNReal) / (2 ^ 256 : Nat) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _
    _ = (keys.card : ENNReal) / 2 ^ 240 := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 256 = 2 ^ 16 * 2 ^ 240 by rw [← pow_add]]
        exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

theorem compression_collision240_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCol : ¬ CacheHasCollision240 cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun result => CacheHasCollision240 result.2) <$> (compressionRun permutation computation cache))) ≤
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, noCol, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro answer _
      exact ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCol covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have smaller : (∑ step ∈ Finset.range (budget - 1), ((known + step : Nat) : ENNReal) / 2 ^ 240) ≤
          ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le budget 1))
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCol covered).trans smaller
        | none =>
          have fresh : (prEvent ((fun answer => CacheHasCollision240 (cache.cacheQuery input answer)) <$>
              ($ᵗ CompressionSpec.Range input))) ≤ (known : ENNReal) / 2 ^ 240 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_collision240_bound cache input keys noCol covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHasCollision240 (cache.cacheQuery input answer) →
              (prEvent ((fun result => CacheHasCollision240 result.2) <$>
                (compressionRun permutation (next answer) (cache.cacheQuery input answer)))) ≤
                ∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 240 := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have combined := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => CacheHasCollision240 (cache.cacheQuery input answer))
            (fun result => CacheHasCollision240 result.2) continuation).trans
              (add_le_add fresh le_rfl)
          apply combined.trans_eq
          conv_rhs => rw [show budget = (budget - 1) + 1 from by omega]
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro step _
          rw [show known + 1 + step = known + (step + 1) from by omega]
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (ih _ (budget - 1) known (tails _) cache noCol covered).trans smaller
        · rw [compression_run_inverse]
          exact (ih _ (budget - 1) known (tails _) cache noCol covered).trans smaller

theorem compression_collision240_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result => CacheHasCollision240 result.2) <$> (compressionRun permutation computation ∅))) ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) := by
  have est := compression_collision240_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, imp, _, _⟩; simp at imp)
    ⟨∅, by simp, fun _ p => (p rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at est
  exact est.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 240))

/-! ### Query-Answer Tracing and Direct Checker Binding Reduction -/

abbrev CompressionReplies := List (BitVec COMPRESSION_INPUT_LENGTH × Digest)

def ReplyCollision240 (replies : CompressionReplies) : Prop :=
  ∃ a ∈ replies, ∃ b ∈ replies, a.1 ≠ b.1 ∧ low240 a.2 = low240 b.2

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
    PublicQueryBound (boundedCollisionSearch adversary budget) (budget + 2 ^ 37) := by
  unfold boundedCollisionSearch
  apply public_query_bound_bind (limit_public_bound adversary budget)
  intro res
  cases res with
  | none => trivial
  | some claim =>
    have hstep : submission.steps .check + submission.steps .check = 2 ^ 37 := by
      change 68719476736 + 68719476736 = 2 ^ 37; decide
    rw [← hstep]
    apply public_query_bound_bind (traceReplies_bound _ _ (run_check_public_query_bound _))
    intro _
    have h2 := traceReplies_bound _ _ (run_check_public_query_bound
      ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩)
    simpa only [Nat.add_zero] using public_query_bound_bind (second := 0) h2 (fun _ => public_query_bound_pure _ 0)

theorem search_replyCollision_in_cache (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))
    (hcol : ReplyCollision240 result.1) :
    CacheHasCollision240 result.2 := by
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

theorem binding_240_arithmetic (budget : Nat)
    (hpos : 1 ≤ budget) (hsmall : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (((budget + 2 ^ 37) * (budget + 2 ^ 37 - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have hmul : (budget + 2 ^ 37) * (budget + 2 ^ 37 - 1) ≤ 2 * budget * 2 ^ 120 := by
    change budget ≤ 2 ^ 120 at hsmall
    have hsq : (budget + 2 ^ 37) * (budget + 2 ^ 37 - 1) ≤ (budget + 2 ^ 37) ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hq2 : budget * budget ≤ budget * 2 ^ 120 := Nat.mul_le_mul_left budget hsmall
    nlinarith
  have hcast : (((budget + 2 ^ 37) * (budget + 2 ^ 37 - 1) : Nat) : ENNReal) ≤
      (budget : ENNReal) * (2 * 2 ^ 120) := by
    have : (budget + 2 ^ 37) * (budget + 2 ^ 37 - 1) ≤ budget * (2 * 2 ^ 120) := by linarith
    exact_mod_cast this
  calc
    _ ≤ ((budget : ENNReal) * (2 * 2 ^ 120)) / (2 * 2 ^ 240) :=
      ENNReal.div_le_div_right hcast _
    _ = (budget : ENNReal) / 2 ^ 120 := by
      rw [show (2 : ENNReal) * 2 ^ 240 = 2 ^ 120 * (2 * 2 ^ 120) by
        rw [← mul_assoc, mul_comm (2 ^ 120 : ENNReal) 2, mul_assoc, ← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

private theorem binding_fixed_le_search (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (hsound : CheckSound h768) (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$>
      (oracle.run adversary))) ≤
    (prEvent ((ReplyCollision240) <$> (fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (submission.scheme.Breaks oracle)]
  unfold boundedCollisionSearch
  rw [fixed_oracle_run_bind]
  change (prEvent ((fun result => ∃ value, result.1 = some value ∧ submission.scheme.Breaks oracle value) <$>
      (oracle.run (limitPublicQueries adversary budget)))) ≤ _
  have hmap : fixedOracleRun oracle (limitPublicQueries adversary budget) =
      Prod.fst <$> oracle.run (limitPublicQueries adversary budget) := rfl
  rw [hmap, bind_map_left, prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨res, calls⟩
  cases res with
  | none =>
    simp [fixed_oracle_run_pure, prEvent_pure]
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
      have hcol := collision240_of_paths (fun x => oracle.compression (x.cast h768.symm)) w0 w1
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
      have hrc : ReplyCollision240 (t0 ++ t1) :=
        ⟨_, hmemx, _, hmemy, fun heq => hxy (by simpa using congrArg (BitVec.cast h768) heq), hlow⟩
      rw [fixed_oracle_run_bind, hrun0, pure_bind, fixed_oracle_run_bind, hrun1, pure_bind,
        fixed_oracle_run_pure, prEvent_pure, if_pos hrc, mul_one]
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
        (prEvent ((ReplyCollision240) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using binding_fixed_le_search h768 hsound oracle adversary budget
    have hperm : ∀ permutation : Perm,
        (prEvent ((ReplyCollision240) <$> (($ᵗ Compression) >>= fun compression =>
          fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      intro permutation
      have heq := (EvalDistEq.of_evalDist_eq
        (compression_sampling_empty permutation (boundedCollisionSearch adversary budget))).prEvent_eq
          ReplyCollision240
      simp only [prEvent_map, Function.comp_def] at heq
      rw [← heq]
      have hdet : (prEvent ((fun result => ReplyCollision240 result.1) <$>
            (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))) ≤
          (prEvent ((fun result => CacheHasCollision240 result.2) <$>
            (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))) :=
        prEvent_mono_of_support _ _ _ fun result reached hcol =>
          search_replyCollision_in_cache permutation adversary budget result reached hcol
      have hbd := compression_collision240_bound permutation (boundedCollisionSearch adversary budget)
        (budget + 2 ^ 37) (boundedCollisionSearch_bound adversary budget)
      exact hdet.trans (hbd.trans (binding_240_arithmetic budget hpos hsmall))
    have hsampled :
        (prEvent ((ReplyCollision240) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      have hswap := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
        (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget))
      have hpr := (EvalDistEq.of_evalDist_eq hswap).prEvent_eq ReplyCollision240
      simp only [Oracle.sample, bind_assoc, pure_bind]
      rw [hpr]
      apply prEvent_bind_le_of_forall_le_of_support
      intro permutation _
      exact hperm permutation
    exact hred.trans hsampled

end CommitGolfCandidate
