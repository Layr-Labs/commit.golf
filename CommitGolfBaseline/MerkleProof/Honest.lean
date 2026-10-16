import CommitGolfBaseline.MerkleProof.Tree
import VCVio.EvalDist.Expectation

/-! # The Merkle baseline: honest runs

Completeness, honest budgets, proof size, and verification cost of `merkle`, and what an accepting
`check` says about each opened position (used for binding). -/

namespace CommitGolf.Baseline
open OracleComp OracleSpec OracleComp.EvalDist

variable (π : Perm)

/-! ### Splitting lists into chunks -/

/-- Chunks of `n + 1` elements, by structural spec. -/
def chunks {α : Type} (n : Nat) (l : List α) : List (List α) :=
  if h : l = [] then [] else l.take (n + 1) :: chunks n (l.drop (n + 1))
termination_by l.length
decreasing_by
  simp only [List.length_drop]
  have : 0 < l.length := List.length_pos_iff.mpr h
  omega

@[simp] theorem chunks_nil {α : Type} (n : Nat) : chunks n ([] : List α) = [] := by
  rw [chunks]; simp

theorem chunks_cons {α : Type} (n : Nat) (x : α) (xs : List α) :
    chunks n (x :: xs) = (x :: xs.take n) :: chunks n (xs.drop n) := by
  rw [chunks]; simp

theorem chunks_flatMap {α β : Type} (n : Nat) (L : List β) (f : β → List α)
    (h : ∀ b ∈ L, (f b).length = n + 1) : chunks n (L.flatMap f) = L.map f := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.flatMap_cons, List.map_cons]
    have hb := h b List.mem_cons_self
    obtain ⟨x, xs, hx⟩ : ∃ x xs, f b = x :: xs := by
      cases hf : f b with
      | nil => simp [hf] at hb
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hxs : xs.length = n := by simpa [hx] using hb
    rw [hx, List.cons_append, chunks_cons, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_of_length_le (by omega), List.nil_append,
      ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]

theorem chunks_length {α : Type} (n k : Nat) (l : List α) (h : l.length = (n + 1) * k) :
    (chunks n l).length = k ∧ ∀ c ∈ chunks n l, c.length = n + 1 := by
  induction k generalizing l with
  | zero => simp_all
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons x xs =>
      rw [chunks_cons]
      have hxs : xs.length = n + (n + 1) * k := by simp at h; linarith
      obtain ⟨h1, h2⟩ := ih (xs.drop n) (by simp; omega)
      refine ⟨by simp [h1], ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp; omega
      · exact h2 c hc

theorem toChunks_go {α : Type} (n : Nat) (xs : List α) (acc₁ : Array α) (acc₂ : Array (List α))
    (h1 : 1 ≤ acc₁.size) (h2 : acc₁.size ≤ n + 1) :
    List.toChunks.go (n + 1) xs acc₁ acc₂ =
      acc₂.toList ++ (acc₁.toList ++ xs.take (n + 1 - acc₁.size)) ::
        chunks n (xs.drop (n + 1 - acc₁.size)) := by
  induction xs generalizing acc₁ acc₂ with
  | nil => simp [List.toChunks.go]
  | cons x xs ih =>
    rw [List.toChunks.go]
    split
    · rename_i h
      have hs : acc₁.size = n + 1 := by simpa using h
      rw [ih _ _ (by simp) (by simp)]
      rw [hs, Nat.sub_self, List.take_zero, List.drop_zero, chunks_cons]
      simp
    · rename_i h
      have hs : acc₁.size ≠ n + 1 := by simpa using h
      rw [ih _ _ (by simp) (by simp; omega)]
      have : n + 1 - acc₁.size = (n + 1 - (acc₁.size + 1)) + 1 := by omega
      simp only [this, List.take_succ_cons, List.drop_succ_cons, Array.size_push]
      simp

/-- `List.toChunks` agrees with the structural `chunks`. -/
theorem toChunks_eq_chunks {α : Type} (n : Nat) (l : List α) :
    l.toChunks (n + 1) = chunks n l := by
  cases l with
  | nil => simp [List.toChunks]
  | cons x xs =>
    rw [List.toChunks, toChunks_go n xs #[x] #[] (by simp) (by simp), chunks_cons]
    · simp
    · omega

theorem zip_map_self {α β : Type} (L : List α) (f : α → β) :
    L.zip (L.map f) = L.map fun a => (a, f a) := by
  induction L <;> simp_all

theorem length_ordered (positions : Positions) : (ordered positions).length = positions.card := by
  simp [ordered]

theorem mem_ordered (positions : Positions) (i : positions) : i ∈ ordered positions := by
  simp [ordered]

/-! ### Evaluating `check` -/

theorem eval_mapM {α β : Type} (L : List α) (g : α → OracleComp PermSpec β) :
    π.eval (L.mapM g) = (L.map fun a => (π.eval (g a)).1, (L.map fun a => (π.eval (g a)).2).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.mapM_cons, Perm.eval_bind, ih, Perm.eval_pure, List.map_cons, List.sum_cons]
    simp

/-- The copaths `check` reads from a proof, in order. -/
def paths (proof : Proof) : List (List Digest) :=
  ((proof.toChunks DIGEST_BYTES).map Digest.ofBytes).toChunks LOG_LENGTH

theorem eval_check (root : Commitment) (positions : Positions) (values : Values positions)
    (proof : Proof) :
    π.eval (merkle.check root positions values proof) =
      if proof.length ≠ positions.card * LOG_LENGTH * DIGEST_BYTES then (false, 0) else
        ((((ordered positions).zip (paths proof)).map
          fun p => pClimb π p.1.1.1 (values p.1) p.2).all (· == root),
         (((ordered positions).zip (paths proof)).map fun p => p.2.length).sum) := by
  simp only [merkle]
  split
  · simp
  · simp only [Perm.eval_bind, eval_mapM, eval_climb, Perm.eval_pure, paths]
    simp

/-! ### The honest run -/

/-- The bytes `opening` returns for a tree. -/
def proofOf (tree : List (List Digest)) (positions : Positions) : Proof :=
  (ordered positions).flatMap fun i => (copath tree LOG_LENGTH i.1.1).flatMap Digest.toBytes

theorem merkle_commit (m : Message) : merkle.commit m =
    (liftM (layers LOG_LENGTH (List.ofFn m)) >>= fun tree => pure (rootOf tree, tree)) := rfl

theorem merkle_opening (tree : List (List Digest)) (I : Positions) :
    merkle.opening tree I = pure (proofOf tree I) := rfl

/-- `commit` returns the root and the tree, for a tree and call count given abstractly (so that
no proof term ever has to evaluate the 2 ^ 24-leaf tree). -/
theorem run_commit (m : Message) (T : List (List Digest)) (c : Nat)
    (hE : π.eval (layers LOG_LENGTH (List.ofFn m)) = (T, c)) :
    π.run (merkle.commit m) = pure ((rootOf T, T), c) := by
  change π.run (liftM (layers LOG_LENGTH (List.ofFn m)) >>= fun tree => pure (rootOf tree, tree) :
        OracleComp World (Commitment × List (List Digest))) = _
  rw [Perm.run_bind, Perm.run_liftM, pure_bind, hE]
  simp only [Perm.run_pure, pure_bind, Nat.add_zero]

theorem length_copath (tree : List (List Digest)) (d index : Nat) :
    (copath tree d index).length = d := by
  simp [copath]

theorem proofOf_eq (tree : List (List Digest)) (positions : Positions) :
    proofOf tree positions =
      ((ordered positions).flatMap fun i => copath tree LOG_LENGTH i.1.1).flatMap
        Digest.toBytes := by
  simp [proofOf, List.flatMap_assoc]

theorem length_proofOf (tree : List (List Digest)) (positions : Positions) :
    (proofOf tree positions).length = positions.card * LOG_LENGTH * DIGEST_BYTES := by
  rw [proofOf_eq, ← length_ordered]
  generalize ordered positions = L
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, ih, List.length_cons] at *
    simp [Digest.length_toBytes, length_copath, List.length_flatMap]
    ring

/-- The honest proof parses back into the copaths of the opened positions. -/
theorem paths_proofOf (tree : List (List Digest)) (positions : Positions) :
    paths (proofOf tree positions) =
      (ordered positions).map fun i => copath tree LOG_LENGTH i.1.1 := by
  rw [paths, proofOf_eq, show DIGEST_BYTES = 31 + 1 from rfl, toChunks_eq_chunks,
    chunks_flatMap _ _ _ (fun d _ => Digest.length_toBytes d), List.map_map]
  have : (Digest.ofBytes ∘ Digest.toBytes) = id := funext Digest.ofBytes_toBytes
  rw [this, List.map_id, show LOG_LENGTH = 23 + 1 from rfl, toChunks_eq_chunks,
    chunks_flatMap _ _ _ (fun i _ => length_copath _ _ _)]

/-- `check` accepts the honest opening, with `LOG_LENGTH` calls per opened position. -/
theorem eval_check_honest (m : Message) (positions : Positions) :
    π.eval (merkle.check (rootOf (pLayers π LOG_LENGTH (List.ofFn m))) positions
      (m.restrict positions) (proofOf (pLayers π LOG_LENGTH (List.ofFn m)) positions)) =
      (true, positions.card * LOG_LENGTH) := by
  have hcl : ∀ i : positions, pClimb π i.1.1 (m.restrict positions i)
      (copath (pLayers π LOG_LENGTH (List.ofFn m)) LOG_LENGTH i.1.1) =
      rootOf (pLayers π LOG_LENGTH (List.ofFn m)) := by
    intro i
    have hleaf : (List.ofFn m).getD i.1.1 0 = m.restrict positions i := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.1.2]
      rfl
    rw [← hleaf]
    exact pClimb_copath π LOG_LENGTH (List.ofFn m) (by rw [List.length_ofFn]; rfl) i.1.1 i.1.2
  rw [eval_check]
  generalize pLayers π LOG_LENGTH (List.ofFn m) = T at hcl ⊢
  rw [if_neg (by rw [length_proofOf]; exact fun h => h rfl)]
  rw [paths_proofOf]
  simp only [zip_map_self, List.map_map]
  refine Prod.ext ?_ ?_
  · show List.all _ _ = true
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply, beq_iff_eq]
    exact hcl i
  · show List.sum _ = _
    have : ((fun p : positions × List Digest => p.2.length) ∘
        fun a : positions => (a, copath T LOG_LENGTH a.1.1)) = fun _ => LOG_LENGTH := by
      funext a; exact length_copath _ _ _
    rw [this, List.map_const', List.sum_replicate, length_ordered, smul_eq_mul]

/-- The copath `check` reads for the opened position `i`: the chunk of the proof at `i`'s rank
among the opened positions. -/
def pathOf (positions : Positions) (proof : Proof) (i : positions) : List Digest :=
  (((proof.toChunks DIGEST_BYTES).map Digest.ofBytes).toChunks LOG_LENGTH).getD
    ((ordered positions).idxOf i) []

/-- **What acceptance means.** If `check` accepts, every opened position's copath has
`LOG_LENGTH` digests and climbs from the claimed value to the commitment. -/
theorem check_accepts (π : Perm) (root : Commitment) (positions : Positions)
    (values : Values positions) (proof : Proof)
    (h : (π.eval (merkle.check root positions values proof)).1 = true) (i : positions) :
    (pathOf positions proof i).length = LOG_LENGTH ∧
      pClimb π i.1.1 (values i) (pathOf positions proof i) = root := by
  rw [eval_check] at h
  split at h
  · exact absurd h (by simp)
  rename_i hlen
  simp only [ne_eq, not_not] at hlen
  -- The proof splits into `|I| × LOG_LENGTH` digests, then into `|I|` copaths of `LOG_LENGTH`.
  have hD : ((proof.toChunks DIGEST_BYTES).map Digest.ofBytes).length =
      (23 + 1) * positions.card := by
    rw [List.length_map, show DIGEST_BYTES = 31 + 1 from rfl, toChunks_eq_chunks,
      (chunks_length 31 (positions.card * LOG_LENGTH) proof
        (by rw [hlen]; simp [DIGEST_BYTES, LOG_LENGTH]; ring)).1]
    simp [LOG_LENGTH]; ring
  have hP := chunks_length 23 positions.card _ hD
  rw [← toChunks_eq_chunks, show 23 + 1 = LOG_LENGTH from rfl] at hP
  obtain ⟨hPlen, hPall⟩ := hP
  have hmem : i ∈ ordered positions := mem_ordered positions i
  have hidx : (ordered positions).idxOf i < (ordered positions).length :=
    List.idxOf_lt_length_of_mem hmem
  have hidx' : (ordered positions).idxOf i < (paths proof).length := by
    rw [paths, hPlen, ← length_ordered]; exact hidx
  have hpath : pathOf positions proof i = (paths proof)[(ordered positions).idxOf i] := by
    change (paths proof).getD _ [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx']
    rfl
  refine ⟨by rw [hpath]; exact hPall _ (List.getElem_mem _), ?_⟩
  -- The pair `(i, its copath)` sits in the zip that `check` climbs.
  have hzip : (i, pathOf positions proof i) ∈ (ordered positions).zip (paths proof) := by
    have hz : (ordered positions).idxOf i < ((ordered positions).zip (paths proof)).length := by
      rw [List.length_zip]; exact lt_min hidx hidx'
    have := List.getElem_mem hz
    rw [List.getElem_zip, List.getElem_idxOf] at this
    rw [hpath]; exact this
  rw [List.all_eq_true] at h
  have := h _ (List.mem_map.mpr ⟨_, hzip, rfl⟩)
  simpa using this

/-- The honest run, summarized by the facts the statements need. -/
theorem honest_spec (π : Perm) (m : Message) (positions : Positions) :
    ∃ r, merkle.honest π m positions = pure r ∧ r.accepted = true ∧ r.commitCalls ≤ LENGTH ∧
      r.openCalls = 0 ∧ r.checkCalls = positions.card * LOG_LENGTH ∧
      r.proofBytes = positions.card * LOG_LENGTH * DIGEST_BYTES := by
  obtain ⟨E, hE⟩ : ∃ E, π.eval (layers LOG_LENGTH (List.ofFn m)) = E := ⟨_, rfl⟩
  obtain ⟨T, c⟩ := E
  have hT : T = pLayers π LOG_LENGTH (List.ofFn m) := by
    rw [← (eval_layers π LOG_LENGTH (List.ofFn m)).1, hE]
  have hc : c ≤ LENGTH := by
    have := (eval_layers π LOG_LENGTH (List.ofFn m)).2
    rw [hE, List.length_ofFn] at this
    exact this
  have hk : π.eval (merkle.check (rootOf T) positions (m.restrict positions)
      (proofOf T positions)) = (true, positions.card * LOG_LENGTH) := by
    rw [hT]; exact eval_check_honest π m positions
  refine ⟨⟨true, c, 0, positions.card * LOG_LENGTH, (proofOf T positions).length⟩,
    ?_, rfl, hc, rfl, rfl, length_proofOf _ _⟩
  unfold Scheme.honest
  rw [run_commit π m T c hE]
  erw [pure_bind]
  dsimp only
  rw [merkle_opening, Perm.run_pure, pure_bind]
  dsimp only
  rw [hk]

theorem merkle_completeness : merkle.Completeness := by
  intro π m positions
  obtain ⟨r, hr, hacc, -⟩ := honest_spec π m positions
  rw [hr, probEvent_pure, if_pos hacc]

theorem length_le_commitBudget : LENGTH ≤ COMMIT_BUDGET := by
  unfold COMMIT_BUDGET; omega

theorem merkle_honestBudgets : merkle.HonestBudgets := by
  intro π m positions
  obtain ⟨r, hr, -, hc, ho, hk, -⟩ := honest_spec π m positions
  have hcheck : r.checkCalls ≤ CHECK_BUDGET positions.card := by
    rw [hk]; unfold CHECK_BUDGET LOG_LENGTH; omega
  rw [hr, probEvent_pure, if_pos ⟨hc.trans length_le_commitBudget, ho ▸ Nat.zero_le _, hcheck⟩]

/-- In the scored run, every outcome is an honest run on a batch of `BATCH` positions. -/
theorem expectedValue_scoredRun_le (m : Message) (g : Scheme.HonestResult → ENNReal) (c : ENNReal)
    (h : ∀ r : Scheme.HonestResult, r.checkCalls = BATCH * LOG_LENGTH →
      r.proofBytes = BATCH * LOG_LENGTH * DIGEST_BYTES → g r ≤ c) :
    expectedValue (merkle.scoredRun m) g ≤ c := by
  unfold Scheme.scoredRun Scheme.randomBatch
  apply expectedValue_bind_le_of_le
  intro π
  rw [bind_assoc]
  apply expectedValue_bind_le_of_le
  intro e
  rw [pure_bind]
  obtain ⟨r, hr, -, -, -, hk, hp⟩ := honest_spec π m (Finset.univ.map e)
  have hcard : (Finset.univ.map e).card = BATCH := by simp
  rw [hr, expectedValue_pure]
  exact h r (by rw [hk, hcard]) (by rw [hp, hcard])

theorem merkle_proofSize : merkle.ProofSize 76800 := by
  intro m
  apply expectedValue_scoredRun_le
  intro r _ hp
  rw [hp]
  norm_num [BATCH, LOG_LENGTH, DIGEST_BYTES]

theorem merkle_verificationCost : merkle.VerificationCost 2400 := by
  intro m
  apply expectedValue_scoredRun_le
  intro r hk _
  rw [hk]
  norm_num [BATCH, LOG_LENGTH]

end CommitGolf.Baseline
