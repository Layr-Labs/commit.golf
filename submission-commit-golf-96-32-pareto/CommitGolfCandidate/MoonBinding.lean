import CommitGolfCandidate.MoonImage
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.Execution

/-! Complete 256-bit adaptive position-binding reduction for the pure 3-ary FIFO queue tree.
The collision detector directly executes the submitted deterministic `check` image on both
conflicting claims while recording every `(input, answer)` compression query in
`traceCompressionReplies`. Because every internal digest in the queue tree is full 256-bit,
any forgery yields a direct 256-bit compression collision, bounded by `M * (M - 1) / 2^257 ≤ q / 2^120`
in the lazy compression ROM with `M = q + 2^39` total queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### Witness Paths and Pure 256-bit Structural Collision Extraction -/

structure WitnessPath where
  index : Index
  value : Entry
  salt : Salt192
  /-- For any non-root node `v < ROOT_NODE`, the two siblings `(sib0, sib1)` of `v` in its parent
  triplet `(3*(v/3), 3*(v/3)+1, 3*(v/3)+2)`. At the root's children (`v ∈ {25165821, 25165822}`),
  `sib0` is the other child and the third slot is fixed to `0`. -/
  sibOf : Nat → Digest × Digest

def stepInput (v : Nat) (cur : Digest) (sib : Digest × Digest) : BitVec 768 :=
  if v / 3 = QUEUE_CALLS - 1 then
    if v % 3 = 0 then ternaryInput cur sib.1 0
    else ternaryInput sib.1 cur 0
  else
    let r := v % 3
    if r = 0 then ternaryInput cur sib.1 sib.2
    else if r = 1 then ternaryInput sib.1 cur sib.2
    else ternaryInput sib.1 sib.2 cur

theorem stepInput_cur_inj {v : Nat} {d1 d2 : Digest} {s1 s2 : Digest × Digest}
    (h : stepInput v d1 s1 = stepInput v d2 s2) : d1 = d2 := by
  unfold stepInput at h
  dsimp only at h
  split_ifs at h
  · exact (ternaryInput_inj h).1
  · exact (ternaryInput_inj h).2.1
  · exact (ternaryInput_inj h).1
  · exact (ternaryInput_inj h).2.1
  · exact (ternaryInput_inj h).2.2

def WitnessPath.leafInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  let iU := leafUInput w.value
  let u := c iU
  let iA := leafAInput u w.value
  let a := c iA
  let iB := leafBInput w.value
  let b := c iB
  let iF := leafFinalInput w.index a b w.salt
  [iU, iA, iB, iF]

def WitnessPath.evalFrom (c : Comp96) (w : WitnessPath) (v : Nat) (cur : Digest) : Digest :=
  if v < ROOT_NODE then
    w.evalFrom c (parentNode v) (c (stepInput v cur (w.sibOf v)))
  else cur
termination_by ROOT_NODE - v
decreasing_by
  unfold parentNode
  have h1 := rootNode_eq
  have h2 : LENGTH = 16777216 := by decide
  omega

theorem WitnessPath.evalFrom_lt (c : Comp96) (w : WitnessPath) {v : Nat} (hv : v < ROOT_NODE) (cur : Digest) :
    w.evalFrom c v cur = w.evalFrom c (parentNode v) (c (stepInput v cur (w.sibOf v))) := by
  rw [WitnessPath.evalFrom]
  simp only [hv, ite_true]

theorem WitnessPath.evalFrom_ge (c : Comp96) (w : WitnessPath) {v : Nat} (hv : ROOT_NODE ≤ v) (cur : Digest) :
    w.evalFrom c v cur = cur := by
  rw [WitnessPath.evalFrom]
  simp only [show ¬ (v < ROOT_NODE) by omega, ite_false]

def WitnessPath.evalRoot (c : Comp96) (w : WitnessPath) : Digest :=
  w.evalFrom c w.index.val (leafDigest c w.index w.salt w.value)

def WitnessPath.inputsFrom (c : Comp96) (w : WitnessPath) (v : Nat) (cur : Digest) : List (BitVec 768) :=
  if v < ROOT_NODE then
    let inp := stepInput v cur (w.sibOf v)
    inp :: w.inputsFrom c (parentNode v) (c inp)
  else []
termination_by ROOT_NODE - v
decreasing_by
  unfold parentNode
  have h1 := rootNode_eq
  have h2 : LENGTH = 16777216 := by decide
  omega

theorem WitnessPath.inputsFrom_lt (c : Comp96) (w : WitnessPath) {v : Nat} (hv : v < ROOT_NODE) (cur : Digest) :
    w.inputsFrom c v cur =
      stepInput v cur (w.sibOf v) :: w.inputsFrom c (parentNode v) (c (stepInput v cur (w.sibOf v))) := by
  rw [WitnessPath.inputsFrom]
  simp only [hv, ite_true]

theorem WitnessPath.inputsFrom_ge (c : Comp96) (w : WitnessPath) {v : Nat} (hv : ROOT_NODE ≤ v) (cur : Digest) :
    w.inputsFrom c v cur = [] := by
  rw [WitnessPath.inputsFrom]
  simp only [show ¬ (v < ROOT_NODE) by omega, ite_false]

def WitnessPath.pathInputs (c : Comp96) (w : WitnessPath) : List (BitVec 768) :=
  w.leafInputs c ++ w.inputsFrom c w.index.val (leafDigest c w.index w.salt w.value)

def HasCollision256 (c : Comp96) (inputs : List (BitVec 768)) : Prop :=
  ∃ x ∈ inputs, ∃ y ∈ inputs, x ≠ y ∧ c x = c y

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

private theorem leaf_collision256 (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hdig : leafDigest c w1.index w1.salt w1.value = leafDigest c w2.index w2.salt w2.value) :
    HasCollision256 c (w1.pathInputs c ++ w2.pathInputs c) := by
  set iU₁ := leafUInput w1.value; set iU₂ := leafUInput w2.value
  set u₁ := c iU₁; set u₂ := c iU₂
  set iA₁ := leafAInput u₁ w1.value; set iA₂ := leafAInput u₂ w2.value
  set a₁ := c iA₁; set a₂ := c iA₂
  set iB₁ := leafBInput w1.value; set iB₂ := leafBInput w2.value
  set b₁ := c iB₁; set b₂ := c iB₂
  set iF₁ := leafFinalInput w1.index a₁ b₁ w1.salt
  set iF₂ := leafFinalInput w2.index a₂ b₂ w2.salt
  have hmem1 : ∀ x ∈ w1.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ hx)
  have hmem2 : ∀ x ∈ w2.leafInputs c, x ∈ w1.pathInputs c ++ w2.pathInputs c := fun x hx =>
    List.mem_append_right _ (List.mem_append_left _ hx)
  by_cases hF : iF₁ ≠ iF₂
  · exact ⟨iF₁, hmem1 _ (by simp [WitnessPath.leafInputs, iF₁, a₁, iA₁, u₁, iU₁, b₁, iB₁]),
      iF₂, hmem2 _ (by simp [WitnessPath.leafInputs, iF₂, a₂, iA₂, u₂, iU₂, b₂, iB₂]),
      hF, hdig⟩
  · push_neg at hF
    have hF' : leafFinalInput w2.index a₁ b₁ w1.salt = leafFinalInput w2.index a₂ b₂ w2.salt := by
      simpa [iF₁, iF₂, hidx] using hF
    obtain ⟨ha, hb, _⟩ := leafFinalInput_inj hF'
    by_cases hB : iB₁ ≠ iB₂
    · exact ⟨iB₁, hmem1 _ (by simp [WitnessPath.leafInputs, iB₁]),
        iB₂, hmem2 _ (by simp [WitnessPath.leafInputs, iB₂]),
        hB, hb⟩
    · push_neg at hB
      by_cases hA : iA₁ ≠ iA₂
      · exact ⟨iA₁, hmem1 _ (by simp [WitnessPath.leafInputs, iA₁, u₁, iU₁]),
          iA₂, hmem2 _ (by simp [WitnessPath.leafInputs, iA₂, u₂, iU₂]),
          hA, ha⟩
      · push_neg at hA
        obtain ⟨hvMid, hu⟩ := bv_append_inj (show w1.value.extractLsb' 768 512 ++ u₁ =
          w2.value.extractLsb' 768 512 ++ u₂ from hA)
        by_cases hU : iU₁ ≠ iU₂
        · exact ⟨iU₁, hmem1 _ (by simp [WitnessPath.leafInputs, iU₁]),
            iU₂, hmem2 _ (by simp [WitnessPath.leafInputs, iU₂]),
            hU, hu⟩
        · push_neg at hU
          exact (hne (entry_eq_of_late_slices w1.value w2.value hU hvMid hB)).elim

private theorem climb_collision256 (c : Comp96) (w1 w2 : WitnessPath) :
    ∀ k v d1 d2,
      ROOT_NODE - v ≤ k →
      w1.evalFrom c v d1 = w2.evalFrom c v d2 →
      d1 = d2 ∨ HasCollision256 c (w1.inputsFrom c v d1 ++ w2.inputsFrom c v d2) := by
  intro k
  induction k with
  | zero =>
    intro v d1 d2 hle heq
    have hge : ROOT_NODE ≤ v := by omega
    rw [w1.evalFrom_ge c hge, w2.evalFrom_ge c hge] at heq
    exact Or.inl heq
  | succ k ih =>
    intro v d1 d2 hle heq
    by_cases hv : v < ROOT_NODE
    · rw [w1.evalFrom_lt c hv, w2.evalFrom_lt c hv] at heq
      have hpar_le : ROOT_NODE - parentNode v ≤ k := by
        unfold parentNode
        have h1 := rootNode_eq
        have h2 : LENGTH = 16777216 := by decide
        omega
      let inp1 := stepInput v d1 (w1.sibOf v)
      let inp2 := stepInput v d2 (w2.sibOf v)
      rcases ih (parentNode v) (c inp1) (c inp2) hpar_le heq with hceq | ⟨x, hx, y, hy, hne, hcxy⟩
      · by_cases hne : inp1 ≠ inp2
        · right
          rw [w1.inputsFrom_lt c hv, w2.inputsFrom_lt c hv]
          exact ⟨inp1, List.mem_append_left _ (List.mem_cons_self),
            inp2, List.mem_append_right _ (List.mem_cons_self), hne, hceq⟩
        · push_neg at hne
          exact Or.inl (stepInput_cur_inj hne)
      · right
        rw [w1.inputsFrom_lt c hv, w2.inputsFrom_lt c hv]
        have hlift : ∀ z ∈ w1.inputsFrom c (parentNode v) (c inp1) ++ w2.inputsFrom c (parentNode v) (c inp2),
            z ∈ (inp1 :: w1.inputsFrom c (parentNode v) (c inp1)) ++ (inp2 :: w2.inputsFrom c (parentNode v) (c inp2)) := by
          intro z hz
          rcases List.mem_append.mp hz with h1 | h2
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ h1)
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
        exact ⟨x, hlift x hx, y, hlift y hy, hne, hcxy⟩
    · have hge : ROOT_NODE ≤ v := by omega
      rw [w1.evalFrom_ge c hge, w2.evalFrom_ge c hge] at heq
      exact Or.inl heq

/-- Two conflicting witness paths reaching the same root MUST witness a 256-bit compression collision. -/
theorem collision256_of_paths (c : Comp96) (w1 w2 : WitnessPath)
    (hidx : w1.index = w2.index) (hne : w1.value ≠ w2.value)
    (hroot : w1.evalRoot c = w2.evalRoot c) :
    HasCollision256 c (w1.pathInputs c ++ w2.pathInputs c) := by
  unfold WitnessPath.evalRoot at hroot
  rw [hidx] at hroot
  rcases climb_collision256 c w1 w2 ROOT_NODE w2.index.val
      (leafDigest c w2.index w1.salt w1.value) (leafDigest c w2.index w2.salt w2.value)
      (Nat.sub_le _ _) hroot with hleaf | ⟨x, hx, y, hy, hxy, hcxy⟩
  · exact leaf_collision256 c w1 w2 hidx hne (by simpa [hidx] using hleaf)
  · have hlift : ∀ z ∈ w1.inputsFrom c w2.index.val (leafDigest c w2.index w1.salt w1.value) ++
        w2.inputsFrom c w2.index.val (leafDigest c w2.index w2.salt w2.value),
        z ∈ w1.pathInputs c ++ w2.pathInputs c := by
      intro z hz
      rcases List.mem_append.mp hz with h1 | h2
      · rw [← hidx] at h1
        exact List.mem_append_left _ (List.mem_append_right _ h1)
      · exact List.mem_append_right _ (List.mem_append_right _ h2)
    exact ⟨x, hlift x hx, y, hlift y hy, hxy, hcxy⟩

/-! ### 256-bit Lazy Compression ROM Birthday Bound -/

def CacheHasCollision256 (cache : CompressionCache) : Prop :=
  ∃ (x y : BitVec COMPRESSION_INPUT_LENGTH) (vx vy : Digest),
    x ≠ y ∧ cache x = some vx ∧ cache y = some vy ∧ vx = vy

theorem fresh_collision256_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCol : ¬ CacheHasCollision256 cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    prEvent ((fun ans => CacheHasCollision256 (cache.cacheQuery input ans)) <$>
        ($ᵗ CompressionSpec.Range input)) ≤
      (keys.card : ENNReal) / 2 ^ 256 := by
  classical
  let targets : Finset Digest :=
    keys.biUnion (fun k => match cache k with | some v => {v} | none => ∅)
  have htargets_card : targets.card ≤ keys.card := by
    calc
      targets.card ≤ ∑ k ∈ keys, (match cache k with | some v => ({v} : Finset Digest) | none => ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ keys, 1 := by
        apply Finset.sum_le_sum; intro k _
        cases cache k with
        | none => simp
        | some v => exact (Finset.card_singleton (v : Digest)).le
      _ = keys.card := by simp
  have hsub : (Finset.univ.filter (fun ans : Digest => CacheHasCollision256 (cache.cacheQuery input ans))) ⊆
      targets := by
    intro ans hans
    rw [Finset.mem_filter] at hans
    obtain ⟨x, y, vx, vy, hne, hx, hy, hveq⟩ := hans.2
    by_cases hxi : x = input
    · subst hxi
      have hyne : y ≠ x := Ne.symm hne
      erw [QueryCache.cacheQuery_self cache x ans] at hx
      erw [QueryCache.cacheQuery_of_ne cache ans hyne] at hy
      cases hx
      have hy' : cache y = some vy := hy
      have hyk : y ∈ keys := covers y (by intro hnone; rw [hnone] at hy'; cases hy')
      exact Finset.mem_biUnion.mpr ⟨y, hyk, by simp only [hy', hveq]; exact Finset.mem_singleton_self _⟩
    · by_cases hyi : y = input
      · subst hyi
        erw [QueryCache.cacheQuery_of_ne cache ans hxi] at hx
        erw [QueryCache.cacheQuery_self cache y ans] at hy
        cases hy
        have hx' : cache x = some vx := hx
        have hxk : x ∈ keys := covers x (by intro hnone; rw [hnone] at hx'; cases hx')
        exact Finset.mem_biUnion.mpr ⟨x, hxk, by simp only [hx', hveq]; exact Finset.mem_singleton_self _⟩
      · erw [QueryCache.cacheQuery_of_ne cache ans hxi] at hx
        erw [QueryCache.cacheQuery_of_ne cache ans hyi] at hy
        exact (noCol ⟨x, y, vx, vy, hne, hx, hy, hveq⟩).elim
  change prEvent ((fun ans : Digest => CacheHasCollision256 (cache.cacheQuery input ans)) <$> ($ᵗ Digest)) ≤ _
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ 256 := Fintype.card_bitVec 256
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans htargets_card)) _

private theorem prEvent_bind_split_good {α β : Type}
    (mx : ProbComp α) (f : α → ProbComp β) (bad : α → Prop) (event : β → Prop) (r : ENNReal)
    (h : ∀ a ∈ support mx, ¬ bad a → prEvent (event <$> f a) ≤ r) :
    prEvent (event <$> (mx >>= f)) ≤ prEvent (bad <$> mx) + r := by
  classical
  rw [bind_eq_attach_bind mx f, prEvent_bind_eq_tsum]
  let p := fun a : Subtype (MonadAttach.CanReturn mx) => Pr{let z ← MonadAttach.attach mx}[z = a]
  have hbad : prEvent (bad <$> mx) = ∑' a, if bad a.1 then p a else 0 := by
    have hmap : prEvent (bad <$> mx) =
        prEvent ((fun a : Subtype (MonadAttach.CanReturn mx) => bad a.1) <$> MonadAttach.attach mx) := by
      conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
      rw [Functor.map_map]
    rw [hmap, OracleComp.prEvent_eq_tsum_ite]
  have hsum_one : (∑' a, p a) = 1 := by
    have htr := OracleComp.prEvent_true_eq_one (MonadAttach.attach mx)
    rw [OracleComp.prEvent_eq_tsum_ite] at htr
    simp only [ite_true] at htr
    exact htr
  calc
    ∑' a, p a * prEvent (event <$> f a.1)
      ≤ ∑' a, ((if bad a.1 then p a else 0) + p a * r) := by
        apply ENNReal.tsum_le_tsum
        intro a
        by_cases hb : bad a.1
        · simp only [hb, ite_true]
          calc
            p a * prEvent (event <$> f a.1)
              ≤ p a * 1 := mul_le_mul' le_rfl (prEvent_le_one _)
            _ = p a := mul_one _
            _ ≤ p a + p a * r := le_self_add
        · simp only [hb, ite_false, zero_add]
          exact mul_le_mul' le_rfl (h a.1 a.2 hb)
    _ = (∑' a, if bad a.1 then p a else 0) + (∑' a, p a * r) := ENNReal.tsum_add
    _ = prEvent (bad <$> mx) + (∑' a, p a) * r := by rw [← hbad, ENNReal.tsum_mul_right]
    _ = prEvent (bad <$> mx) + r := by rw [hsum_one, one_mul]

theorem compression_collision256_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCol : ¬ CacheHasCollision256 cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    prEvent ((fun result => CacheHasCollision256 result.2) <$> (compressionRun permutation computation cache)) ≤
      (∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256) := by
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
      have hsmaller :
          (∑ step ∈ Finset.range (budget - 1), ((known + step : Nat) : ENNReal) / 2 ^ 256) ≤
          (∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256) := by
        conv_rhs => rw [show budget = (budget - 1) + 1 from by omega]
        rw [Finset.sum_range_succ]
        exact le_self_add
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCol covered).trans hsmaller
        | none =>
          have hfresh :
              prEvent ((fun answer => CacheHasCollision256 (cache.cacheQuery input answer)) <$>
                ($ᵗ CompressionSpec.Range input)) ≤
              (known : ENNReal) / 2 ^ 256 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_collision256_bound cache input keys noCol covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have hcont : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHasCollision256 (cache.cacheQuery input answer) →
              prEvent ((fun result => CacheHasCollision256 result.2) <$>
                (compressionRun permutation (next answer) (cache.cacheQuery input answer))) ≤
              (∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256) := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have hsum_eq :
              (known : ENNReal) / 2 ^ 256 +
                (∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256) =
              ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 := by
            conv_rhs => rw [show budget = (budget - 1) + 1 from by omega]
            rw [Finset.sum_range_succ']
            simp only [Nat.add_zero]
            rw [add_comm]
            congr 1
            apply Finset.sum_congr rfl
            intro step _
            rw [show known + 1 + step = known + (step + 1) from by omega]
          rw [← hsum_eq]
          exact (prEvent_bind_split_good
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => CacheHasCollision256 (cache.cacheQuery input answer))
            (fun result => CacheHasCollision256 result.2) _ hcont).trans (add_le_add hfresh le_rfl)
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (ih _ (budget - 1) known (tails _) cache noCol covered).trans hsmaller
        · rw [compression_run_inverse]
          exact (ih _ (budget - 1) known (tails _) cache noCol covered).trans hsmaller

theorem compression_collision256_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    prEvent ((fun result => CacheHasCollision256 result.2) <$> (compressionRun permutation computation ∅)) ≤
      ((∑ i ∈ Finset.range budget, i : Nat) : ENNReal) / 2 ^ 256 := by
  have est := compression_collision256_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, imp, _, _⟩; simp at imp)
    ⟨∅, by simp, fun _ p => (p rfl).elim⟩
  refine est.trans (le_of_eq ?_)
  simp_rw [Nat.zero_add, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]

/-! ### Query-Answer Tracing and Direct Checker Binding Reduction -/

abbrev CompressionReplies := List (BitVec COMPRESSION_INPUT_LENGTH × Digest)

def ReplyCollision256 (replies : CompressionReplies) : Prop :=
  ∃ a ∈ replies, ∃ b ∈ replies, a.1 ≠ b.1 ∧ a.2 = b.2

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
    (hcol : ReplyCollision256 result.1) :
    CacheHasCollision256 result.2 := by
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
    obtain ⟨a, ha, b, hb, hne, heq⟩ := hcol
    exact ⟨a.1, b.1, a.2, b.2, hne, hboth a ha, hboth b hb, heq⟩

private theorem two_mul_sum_range_le_sq (M : Nat) :
    2 * (∑ i ∈ Finset.range M, i) ≤ M ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    nlinarith

private theorem collision256_sum_le_budget (budget : Nat)
    (hpos : 1 ≤ budget) (hsmall : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((∑ i ∈ Finset.range (budget + 2 ^ 39), i : Nat) : ENNReal) / 2 ^ 256 ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have hsec : BINDING_SECURITY_BITS = 120 := rfl
  rw [hsec] at hsmall ⊢
  set M := budget + 2 ^ 39
  have hsum_nat : 2 * (∑ i ∈ Finset.range M, i) ≤ budget * 2 ^ 137 := by
    have hsq := two_mul_sum_range_le_sq M
    have hM2 : M ^ 2 = budget ^ 2 + 2 ^ 40 * budget + 2 ^ 78 := by
      dsimp only [M]; ring
    have hq2 : budget ^ 2 ≤ budget * 2 ^ 120 := by
      rw [sq]; exact Nat.mul_le_mul_left budget hsmall
    have h78 : 2 ^ 78 ≤ budget * 2 ^ 78 := Nat.le_mul_of_pos_left _ hpos
    have hcoeff : 2 ^ 120 + 2 ^ 40 + 2 ^ 78 ≤ 2 ^ 137 := by decide
    have hmul : budget * (2 ^ 120 + 2 ^ 40 + 2 ^ 78) ≤ budget * 2 ^ 137 :=
      Nat.mul_le_mul_left budget hcoeff
    calc
      2 * (∑ i ∈ Finset.range M, i) ≤ M ^ 2 := hsq
      _ = budget ^ 2 + 2 ^ 40 * budget + 2 ^ 78 := hM2
      _ ≤ budget * 2 ^ 120 + budget * 2 ^ 40 + budget * 2 ^ 78 := by
            have := Nat.mul_comm (2 ^ 40) budget; omega
      _ = budget * (2 ^ 120 + 2 ^ 40 + 2 ^ 78) := by ring
      _ ≤ budget * 2 ^ 137 := hmul
  have hcast : ((2 * (∑ i ∈ Finset.range M, i) : Nat) : ENNReal) ≤ ((budget * 2 ^ 137 : Nat) : ENNReal) :=
    Nat.cast_le.mpr hsum_nat
  calc
    ((∑ i ∈ Finset.range M, i : Nat) : ENNReal) / 2 ^ 256
      = ((2 : ENNReal) * ((∑ i ∈ Finset.range M, i : Nat) : ENNReal)) / (2 * 2 ^ 256) :=
        (ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)).symm
    _ ≤ ((budget * 2 ^ 137 : Nat) : ENNReal) / (2 * 2 ^ 256) := by
        apply ENNReal.div_le_div_right
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast
    _ = (budget : ENNReal) / 2 ^ 120 := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) * 2 ^ 256 = 2 ^ 120 * 2 ^ 137 by
          rw [← pow_succ', ← pow_add]]
        exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

private theorem binding_fixed_le_search (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (hsound : CheckSound h768) (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$>
      (oracle.run adversary))) ≤
    (prEvent ((ReplyCollision256) <$> (fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
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
      have hcol := collision256_of_paths (fun x => oracle.compression (x.cast h768.symm)) w0 w1
        (hidx0.trans hidx1.symm) (by rw [hv0, hv1]; exact hvalne) (hrt0.trans hrt1.symm)
      obtain ⟨x, hx, y, hy, hxy, heq⟩ := hcol
      have hmemx : (x.cast h768.symm, oracle.compression (x.cast h768.symm)) ∈ t0 ++ t1 := by
        rcases List.mem_append.mp hx with hx0 | hx1
        · exact List.mem_append_left _ (htr0 x hx0)
        · exact List.mem_append_right _ (htr1 x hx1)
      have hmemy : (y.cast h768.symm, oracle.compression (y.cast h768.symm)) ∈ t0 ++ t1 := by
        rcases List.mem_append.mp hy with hy0 | hy1
        · exact List.mem_append_left _ (htr0 y hy0)
        · exact List.mem_append_right _ (htr1 y hy1)
      have hrc : ReplyCollision256 (t0 ++ t1) :=
        ⟨_, hmemx, _, hmemy, fun heq' => hxy (by simpa using congrArg (BitVec.cast h768) heq'), heq⟩
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
        (prEvent ((ReplyCollision256) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using binding_fixed_le_search h768 hsound oracle adversary budget
    have hperm : ∀ permutation : Perm,
        (prEvent ((ReplyCollision256) <$> (($ᵗ Compression) >>= fun compression =>
          fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      intro permutation
      have heq := (EvalDistEq.of_evalDist_eq
        (compression_sampling_empty permutation (boundedCollisionSearch adversary budget))).prEvent_eq
          ReplyCollision256
      simp only [prEvent_map] at heq
      rw [← heq]
      let run := compressionRun permutation (boundedCollisionSearch adversary budget) ∅
      have hdet : prEvent ((fun result => ReplyCollision256 result.1) <$> run) ≤
          prEvent ((fun result => CacheHasCollision256 result.2) <$> run) :=
        prEvent_mono_of_support _ _ _ fun result reached hcol =>
          search_replyCollision_in_cache permutation adversary budget result reached hcol
      have hcol := compression_collision256_bound permutation (boundedCollisionSearch adversary budget)
        (budget + 2 ^ 39) (boundedCollisionSearch_bound adversary budget)
      exact (hdet.trans hcol).trans (collision256_sum_le_budget budget hpos hsmall)
    have hsampled :
        (prEvent ((ReplyCollision256) <$> (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) ≤
          (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      have hswap := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
        (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget))
      have hpr := (EvalDistEq.of_evalDist_eq hswap).prEvent_eq ReplyCollision256
      simp only [Oracle.sample, bind_assoc, pure_bind]
      rw [hpr]
      apply prEvent_bind_le_of_forall_le_of_support
      intro permutation _
      exact hperm permutation
    exact hred.trans hsampled

end CommitGolfCandidate
