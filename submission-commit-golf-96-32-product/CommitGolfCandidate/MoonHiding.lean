import CommitGolfCandidate.MoonHidingCore

/-! Complete 128-bit index-tagged statistical hiding proof for our r=1 commitment scheme.
Two-step hybrid conditioned on Stage 1's lazy compression cache (at most `budget` keys):
  1. Simultaneous Call-0 reprogramming for ALL hidden leaves `i ∉ positions`:
     `TV(Real(m), Ideal0(m)) <= 3 * budget / 2^128 + (2^24 + HONEST_TREE_BUDGET) * 2^24 / 2^192`.
  2. Leaf-by-leaf 256-bit chaining-value hybrid for Calls 1..3 of hidden leaves:
     `TV(Ideal0(m₀), Ideal0(m₁)) <= LENGTH * 6 * (2 * budget + HONEST_TREE_BUDGET + 3) / 2^256`.
Total TV distance is strictly below `(budget + 1) / 2^120` for every opening size `0 <= k <= 2^24`. -/
namespace CommitGolfCandidate

local instance moonHidingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-! ### 1. Exact Machine-to-Reference Interface -/

def honestTranscript (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← submission.scheme.commit message
  let proof ← submission.scheme.opening trapdoor positions
  return (root, proof)

def referenceTranscript (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (message : Message) (salts : Index → Salt128) (positions : Positions) : Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  (rootVal c message salts, referenceProof (nodeVal c message salts) salts positions)

/-- Machine refinement contract proved by `MoonCommitRef` + `MoonOpenRef`. -/
def HonestTranscriptRefines (h768 : COMPRESSION_INPUT_LENGTH = 768) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (honestTranscript message positions) =
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        pure (referenceTranscript h768 oracle.compression message (splitBlocks 128 LENGTH packed) positions))

/-! ### 2. Ideal-0 Game (Fresh Uniform 256-bit `cv0` on Unopened Leaves) -/

def ideal0Leaves (c : Comp96) (msg : Message) (sOpen : Index → Salt128) (cv0 : Index → Digest)
    (positions : Positions) (i : Index) : Digest :=
  if i ∈ positions then leafDigest c i (sOpen i) (msg i)
  else leafChainFromCv0 c (cv0 i) (msg i)

def ideal0Transcript (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (msg : Message) (sOpen : Index → Salt128) (cv0 : Index → Digest) (positions : Positions) :
    Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  let nodes := nodeValFromLeaves c (ideal0Leaves c msg sOpen cv0 positions)
  (nodes 24 0, referenceProof nodes sOpen positions)

theorem referenceProof_congr_opened (nodes : Nat → Nat → Digest)
    (s1 s2 : Index → Salt128) (positions : Positions)
    (hagree : ∀ i ∈ positions, s1 i = s2 i) :
    referenceProof nodes s1 positions = referenceProof nodes s2 positions := by
  unfold referenceProof
  split
  · rfl
  · apply congrArg (· ++ capFrontierProof nodes positions)
    apply List.flatMap_congr
    intro i hi
    have hmem : i ∈ positions := (Finset.mem_sort (· ≤ ·)).mp hi
    simp only [recordProof, hagree i hmem]

theorem ideal0Transcript_eq_reference_of_cv0 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (compress : Compression) (msg : Message) (sOpen sHidden : Index → Salt128) (positions : Positions) :
    let c : Comp96 := fun x => compress (x.cast h768.symm)
    ideal0Transcript h768 compress msg sOpen
      (fun i => c (leafCall0Input i (sHidden i) (msg i))) positions =
    referenceTranscript h768 compress msg (saltsMerge positions sOpen sHidden) positions := by
  intro c
  have hleaves : ideal0Leaves c msg sOpen (fun i => c (leafCall0Input i (sHidden i) (msg i))) positions =
      fun i => leafDigest c i (saltsMerge positions sOpen sHidden i) (msg i) := by
    funext i
    unfold ideal0Leaves saltsMerge leafDigest
    by_cases hi : i ∈ positions <;> simp [hi]
  unfold ideal0Transcript referenceTranscript rootVal nodeVal
  simp only [c, hleaves]
  congr 1
  exact referenceProof_congr_opened _ sOpen (saltsMerge positions sOpen sHidden) positions
    (fun i hi => by simp [saltsMerge, hi])

/-! ### 3. Simultaneous Reprogramming on All Hidden Call-0 Inputs -/

def hiddenCall0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message)
    (sHidden : Index → Salt128) (i : Index) : BitVec COMPRESSION_INPUT_LENGTH :=
  (leafCall0Input i (sHidden i) (msg i)).cast h768.symm

theorem hiddenCall0_injective (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message)
    (sHidden : Index → Salt128) : Function.Injective (hiddenCall0 h768 msg sHidden) := by
  intro a b h
  have hcast : leafCall0Input a (sHidden a) (msg a) = leafCall0Input b (sHidden b) (msg b) := by
    simpa [hiddenCall0] using congrArg (BitVec.cast h768) h
  have htag := congrArg (fun v : BitVec 768 => v.extractLsb' 128 64) hcast
  simp only [leafCall0Input_tag] at htag
  exact leafTag_injective htag

private def toOut (d : Digest) : BitVec COMPRESSION_OUTPUT_LENGTH := d
private def fromOut (d : BitVec COMPRESSION_OUTPUT_LENGTH) : Digest := d

noncomputable def reprogramFinset (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt128)
    (cv0 : Index → Digest) (S : Finset Index) : Compression :=
  fun x =>
    if h : ∃ i ∈ S, hiddenCall0 h768 msg sHidden i = x then
      toOut (cv0 (Classical.choose h))
    else table x

theorem reprogramFinset_mem (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt128)
    (cv0 : Index → Digest) (S : Finset Index) (i : Index) (hi : i ∈ S) :
    reprogramFinset h768 table msg sHidden cv0 S (hiddenCall0 h768 msg sHidden i) = toOut (cv0 i) := by
  unfold reprogramFinset
  split_ifs with h
  · rw [hiddenCall0_injective h768 msg sHidden (Classical.choose_spec h).2]
  · exact (h ⟨i, hi, rfl⟩).elim

theorem reprogramFinset_not_mem (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt128)
    (cv0 : Index → Digest) (S : Finset Index) (x : BitVec COMPRESSION_INPUT_LENGTH)
    (hnot : ∀ i ∈ S, hiddenCall0 h768 msg sHidden i ≠ x) :
    reprogramFinset h768 table msg sHidden cv0 S x = table x := by
  unfold reprogramFinset
  split_ifs with h
  · obtain ⟨i, hi, heq⟩ := h
    exact (hnot i hi heq).elim
  · rfl

theorem reprogramFinset_insert (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt128)
    (cv0 : Index → Digest) (a : Index) (S : Finset Index) (ha : a ∉ S) :
    reprogramFinset h768 table msg sHidden cv0 (insert a S) =
      Function.update (reprogramFinset h768 table msg sHidden cv0 S)
        (hiddenCall0 h768 msg sHidden a) (toOut (cv0 a)) := by
  funext x
  by_cases hx : x = hiddenCall0 h768 msg sHidden a
  · subst hx
    rw [Function.update_self, reprogramFinset_mem _ _ _ _ _ _ a (Finset.mem_insert_self a S)]
  · rw [Function.update_of_ne hx]
    by_cases hS : ∃ i ∈ S, hiddenCall0 h768 msg sHidden i = x
    · obtain ⟨i, hi, rfl⟩ := hS
      rw [reprogramFinset_mem _ _ _ _ _ _ i (Finset.mem_insert_of_mem hi),
        reprogramFinset_mem _ _ _ _ _ _ i hi]
    · rw [reprogramFinset_not_mem _ _ _ _ _ (insert a S), reprogramFinset_not_mem _ _ _ _ _ S]
      · intro i hi heq; exact hS ⟨i, hi, heq⟩
      · intro i hi heq
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact hx heq.symm
        · exact hS ⟨i, hiS, heq⟩

/-- Simultaneous programming identity: updating `table` at all `i ∈ S` with fresh uniform `cv0`
produces the EXACT joint distribution `(table, fun i => if i ∈ S then table (hiddenCall0 i) else cv0 i)`. -/
theorem reprogramFinset_dist (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (msg : Message) (sHidden : Index → Salt128) (S : Finset Index) {α : Type}
    (F : Compression → (Index → Digest) → ProbComp α) :
    𝒟[do let cv0 ← $ᵗ (Index → Digest)
         let table ← $ᵗ Compression
         F (reprogramFinset h768 table msg sHidden cv0 S) cv0] =
    𝒟[do let cv0 ← $ᵗ (Index → Digest)
         let table ← $ᵗ Compression
         F table (fun i => if i ∈ S then table (hiddenCall0 h768 msg sHidden i) else cv0 i)] := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    apply _root_.evalDist_bind_congr; intro cv0
    apply _root_.evalDist_bind_congr; intro table
    have h1 : reprogramFinset h768 table msg sHidden cv0 ∅ = table := by
      funext x; exact reprogramFinset_not_mem _ _ _ _ _ ∅ x (by simp)
    have h2 : (fun i => if i ∈ (∅ : Finset Index) then (table (hiddenCall0 h768 msg sHidden i) : Digest) else cv0 i) = cv0 := by
      funext i; exact if_neg (Finset.notMem_empty i)
    rw [h1]
    exact congrArg (fun cv => 𝒟[F table cv]) h2.symm
  | @insert a S ha ih =>
    let F' : Compression → (Index → Digest) → ProbComp α := fun tbl cv =>
      do let ans ← $ᵗ Digest
         F (Function.update tbl (hiddenCall0 h768 msg sHidden a) (toOut ans)) (Function.update cv a ans)
    have hlhs :
        𝒟[do let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             F (reprogramFinset h768 table msg sHidden cv0 (insert a S)) cv0] =
        𝒟[do let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             F' (reprogramFinset h768 table msg sHidden cv0 S) cv0] := by
      rw [← uniform_coordinate_bind a (fun cv0 =>
        ($ᵗ Compression) >>= fun table => F (reprogramFinset h768 table msg sHidden cv0 (insert a S)) cv0)]
      apply _root_.evalDist_bind_congr; intro cv0
      rw [distribution_bind_comm ($ᵗ Digest) ($ᵗ Compression)]
      apply _root_.evalDist_bind_congr; intro table
      apply _root_.evalDist_bind_congr; intro ans
      have hrep : reprogramFinset h768 table msg sHidden (Function.update cv0 a ans) (insert a S) =
          Function.update (reprogramFinset h768 table msg sHidden cv0 S)
            (hiddenCall0 h768 msg sHidden a) (toOut ans) := by
        rw [reprogramFinset_insert _ _ _ _ _ a S ha, Function.update_self]
        apply congrArg (fun f : Compression => Function.update f (hiddenCall0 h768 msg sHidden a) (toOut ans))
        funext x
        by_cases hS : ∃ i ∈ S, hiddenCall0 h768 msg sHidden i = x
        · obtain ⟨i, hi, rfl⟩ := hS
          rw [reprogramFinset_mem _ _ _ _ _ S i hi, reprogramFinset_mem _ _ _ _ _ S i hi,
            Function.update_of_ne (fun h => ha (by subst h; exact hi))]
        · rw [reprogramFinset_not_mem _ _ _ _ _ S x (fun i hi heq => hS ⟨i, hi, heq⟩),
            reprogramFinset_not_mem _ _ _ _ _ S x (fun i hi heq => hS ⟨i, hi, heq⟩)]
      simp only [F', hrep]
    rw [hlhs, ih F']
    apply _root_.evalDist_bind_congr; intro cv0
    rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ Digest)]
    have hupd := compression_table_update_bind (hiddenCall0 h768 msg sHidden a)
      (fun table => F table (fun i => if i ∈ insert a S then table (hiddenCall0 h768 msg sHidden i) else cv0 i))
    rw [← hupd]
    apply _root_.evalDist_bind_congr; intro ans
    apply _root_.evalDist_bind_congr; intro table
    have hcv : Function.update (fun i => if i ∈ S then fromOut (table (hiddenCall0 h768 msg sHidden i)) else cv0 i) a ans =
        (fun i => if i ∈ insert a S then
          fromOut ((Function.update table (hiddenCall0 h768 msg sHidden a) (toOut ans)) (hiddenCall0 h768 msg sHidden i))
        else cv0 i) := by
      funext i
      by_cases hia : i = a
      · subst hia
        rw [Function.update_self, if_pos (Finset.mem_insert_self i S), Function.update_self]
        rfl
      · rw [Function.update_of_ne hia]
        by_cases hiS : i ∈ S
        · have hne : hiddenCall0 h768 msg sHidden i ≠ hiddenCall0 h768 msg sHidden a :=
            fun heq => hia (hiddenCall0_injective h768 msg sHidden heq)
          rw [if_pos hiS, if_pos (Finset.mem_insert_of_mem hiS), Function.update_of_ne hne]
        · have hni : i ∉ insert a S := by
            intro hm; rcases Finset.mem_insert.mp hm with rfl | h'
            · exact hia rfl
            · exact hiS h'
          rw [if_neg hiS, if_neg hni]
    exact congrArg (fun cv => 𝒟[F (Function.update table (hiddenCall0 h768 msg sHidden a) (toOut ans)) cv]) hcv

/-! ### 4. 128-bit Tagged Salt Hit Bounds (`1 / 2^128` per Query!) -/

def hiddenPrefixes (positions : Positions) (sHidden : Index → Salt128) : Finset (BitVec 192) :=
  (Finset.univ \ positions).image (fun i => leafTag i ++ sHidden i)

theorem hiddenPrefixes_card_le (positions : Positions) (sHidden : Index → Salt128) :
    (hiddenPrefixes positions sHidden).card ≤ LENGTH := by
  calc
    (hiddenPrefixes positions sHidden).card ≤ (Finset.univ \ positions).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset Index).card := Finset.card_le_card Finset.sdiff_subset
    _ = LENGTH := by rw [Finset.card_univ]; exact Fintype.card_fin LENGTH

private theorem extractLsb'_128_64_tag_salt (t : BitVec 64) (s : Salt128) :
    (t ++ s).extractLsb' 128 64 = t := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
    show ¬ (128 + b < 128) by omega, ite_false, show 128 + b - 128 = b by omega]

private theorem extractLsb'_0_128_tag_salt (t : BitVec 64) (s : Salt128) :
    (t ++ s).extractLsb' 0 128 = s := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.zero_add, hb,
    decide_true, Bool.true_and, ite_true]

private theorem prEvent_uniform_eq_target {α : Type} [Fintype α] [DecidableEq α] [SampleableType α]
    (target : α) :
    prEvent ((fun x : α => x = target) <$> ($ᵗ α)) = (1 : ENNReal) / Fintype.card α := by
  rw [SampleableType.prEvent_uniformSample]
  have hfilt : (Finset.univ.filter (fun x : α => x = target)).card = 1 := by
    rw [Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.card_singleton]
  rw [hfilt, Nat.cast_one]

private theorem prEvent_uniform_coord_le {D R : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (i0 : D) (p : R → Prop) {ε : ENNReal} (hp : prEvent (p <$> ($ᵗ R)) ≤ ε) :
    prEvent ((fun f : D → R => p (f i0)) <$> ($ᵗ (D → R))) ≤ ε := by
  rw [map_eq_bind_pure_comp, ← id_map (x := ($ᵗ (D → R)) >>= _)]
  change prEvent (id <$> (do let values ← $ᵗ (D → R); pure (p (values i0)))) ≤ ε
  have hswap := (EvalDistEq.of_evalDist_eq
    (uniform_coordinate_bind (D := D) (R := R) i0 (fun f => pure (p (f i0))))).prEvent_eq id
  rw [← hswap]
  apply prEvent_bind_le_of_forall_le_of_support
  intro f _
  have hev : (do let fresh ← $ᵗ R; pure (p (Function.update f i0 fresh i0))) =
      (p <$> ($ᵗ R)) := by
    simp only [Function.update_self, map_eq_bind_pure_comp]
    rfl
  rw [hev, prEvent_map]
  exact hp

/-- For ANY fixed 192-bit target `v`, because `leafTag` is injective, at most ONE hidden index
can match `v[128..192)`, so `Pr_{sHidden}[v ∈ hiddenPrefixes] <= 1 / 2^128`! -/
theorem single_prefix_hit_128 (positions : Positions) (v : BitVec 192) :
    (prEvent ((fun sHidden : Index → Salt128 => v ∈ hiddenPrefixes positions sHidden) <$>
      ($ᵗ (Index → Salt128)))) ≤ (1 : ENNReal) / 2 ^ 128 := by
  by_cases hex : ∃ i ∈ Finset.univ \ positions, leafTag i = v.extractLsb' 128 64
  · obtain ⟨i0, hi0, htag0⟩ := hex
    have himp : ∀ sHidden : Index → Salt128,
        v ∈ hiddenPrefixes positions sHidden → sHidden i0 = v.extractLsb' 0 128 := by
      intro sHidden hmem
      obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hmem
      have hjtag : leafTag j = v.extractLsb' 128 64 := by
        rw [← hjv]; exact (extractLsb'_128_64_tag_salt (leafTag j) (sHidden j)).symm
      have hji : j = i0 := leafTag_injective (hjtag.trans htag0.symm)
      subst hji
      rw [← hjv]; exact (extractLsb'_0_128_tag_salt (leafTag j) (sHidden j)).symm
    have hle : (prEvent ((fun sHidden : Index → Salt128 => v ∈ hiddenPrefixes positions sHidden) <$>
        ($ᵗ (Index → Salt128)))) ≤
        (prEvent ((fun sHidden : Index → Salt128 => sHidden i0 = v.extractLsb' 0 128) <$>
          ($ᵗ (Index → Salt128)))) :=
      prEvent_mono_of_support _ _ _ (fun s _ h => himp s h)
    refine hle.trans (prEvent_uniform_coord_le (D := Index) (R := Salt128) i0
      (fun fresh => fresh = v.extractLsb' 0 128) ?_)
    rw [prEvent_uniform_eq_target, Fintype.card_bitVec 128]
    simp only [Nat.cast_pow, Nat.cast_ofNat, le_refl]
  · have hzero : (prEvent ((fun sHidden : Index → Salt128 => v ∈ hiddenPrefixes positions sHidden) <$>
        ($ᵗ (Index → Salt128)))) = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro s _ hmem
      obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hmem
      apply hex
      exact ⟨j, hj, by rw [← hjv]; exact (extractLsb'_128_64_tag_salt (leafTag j) (s j)).symm⟩
    rw [hzero]; exact zero_le

theorem list_prefix_hit_128 (positions : Positions) (vs : List (BitVec 192)) :
    (prEvent ((fun sHidden : Index → Salt128 => ∃ v ∈ vs, v ∈ hiddenPrefixes positions sHidden) <$>
      ($ᵗ (Index → Salt128)))) ≤ (vs.length : ENNReal) / 2 ^ 128 := by
  induction vs with
  | nil =>
    have hz : (prEvent ((fun s : Index → Salt128 => ∃ v ∈ ([] : List (BitVec 192)), v ∈ hiddenPrefixes positions s) <$>
        ($ᵗ (Index → Salt128)))) = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ ⟨_, hv, _⟩ => List.not_mem_nil hv)
    rw [hz]; exact zero_le
  | cons v rest ih =>
    have hunion : (prEvent ((fun s => ∃ u ∈ v :: rest, u ∈ hiddenPrefixes positions s) <$> ($ᵗ (Index → Salt128)))) ≤
        (prEvent ((fun s => v ∈ hiddenPrefixes positions s) <$> ($ᵗ (Index → Salt128)))) +
        (prEvent ((fun s => ∃ u ∈ rest, u ∈ hiddenPrefixes positions s) <$> ($ᵗ (Index → Salt128)))) := by
      have hle := prEvent_or_le ($ᵗ (Index → Salt128))
        (fun s => v ∈ hiddenPrefixes positions s)
        (fun s => ∃ u ∈ rest, u ∈ hiddenPrefixes positions s)
      refine (prEvent_mono_of_support _ _ _ ?_).trans hle
      intro s _ ⟨u, hu, hmem⟩
      rcases List.mem_cons.mp hu with rfl | hrest
      · exact Or.inl hmem
      · exact Or.inr ⟨u, hrest, hmem⟩
    refine (hunion.trans (add_le_add (single_prefix_hit_128 positions v) ih)).trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ENNReal.add_div]
    rw [add_comm]

theorem cache_keys_hit_hidden_128 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (msg : Message) (positions : Positions) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys) :
    (prEvent ((fun sHidden : Index → Salt128 => ∃ i ∉ positions, cache (hiddenCall0 h768 msg sHidden i) ≠ none) <$>
      ($ᵗ (Index → Salt128)))) ≤ (keys.card : ENNReal) / 2 ^ 128 := by
  have hle : (prEvent ((fun sHidden => ∃ i ∉ positions, cache (hiddenCall0 h768 msg sHidden i) ≠ none) <$>
      ($ᵗ (Index → Salt128)))) ≤
      (prEvent ((fun sHidden => ∃ v ∈ keys.toList.map (fun k => k.extractLsb' 0 192),
        v ∈ hiddenPrefixes positions sHidden) <$> ($ᵗ (Index → Salt128)))) := by
    apply prEvent_mono_of_support
    intro sHidden _ ⟨i, hi, hne⟩
    refine ⟨(hiddenCall0 h768 msg sHidden i).extractLsb' 0 192,
      List.mem_map.mpr ⟨_, Finset.mem_toList.mpr (covered _ hne), rfl⟩, ?_⟩
    have hp : (hiddenCall0 h768 msg sHidden i).extractLsb' 0 192 = leafTag i ++ sHidden i := by
      unfold hiddenCall0
      rw [extractLsb'_cast_eq, leafCall0Input_prefix192]
    rw [hp]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  exact hle.trans (by simpa only [List.length_map, Finset.length_toList] using
    list_prefix_hit_128 positions (keys.toList.map (fun k => k.extractLsb' 0 192)))

theorem cache_vals_hit_hidden_128 (positions : Positions) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys) :
    (prEvent ((fun sHidden : Index → Salt128 => CacheHitsPrefix cache (hiddenPrefixes positions sHidden)) <$>
      ($ᵗ (Index → Salt128)))) ≤ (keys.card : ENNReal) / 2 ^ 128 := by
  let valPrefixes : List (BitVec 192) := keys.toList.map (fun k => (cache k).getD 0 |>.extractLsb' 0 192)
  have hle : (prEvent ((fun sHidden => CacheHitsPrefix cache (hiddenPrefixes positions sHidden)) <$>
      ($ᵗ (Index → Salt128)))) ≤
      (prEvent ((fun sHidden => ∃ v ∈ valPrefixes, v ∈ hiddenPrefixes positions sHidden) <$>
        ($ᵗ (Index → Salt128)))) := by
    apply prEvent_mono_of_support
    intro sHidden _ ⟨k, ans, hkans, hmem⟩
    refine ⟨ans.extractLsb' 0 192, ?_, hmem⟩
    exact List.mem_map.mpr ⟨k, Finset.mem_toList.mpr (covered k (by rw [hkans]; exact Option.some_ne_none _)),
      by change ((cache k).getD 0).extractLsb' 0 192 = ans.extractLsb' 0 192; rw [hkans]; rfl⟩
  exact hle.trans (by simpa only [valPrefixes, List.length_map, Finset.length_toList] using
    list_prefix_hit_128 positions valPrefixes)

/-! ### 5. Step 1: Real(msg) ↔ Ideal0(msg) Distance (`<= 3t/2^128 + 2^-140`) -/

def realObservation (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let salts ← $ᵗ (Index → Salt128)
  let tr := referenceTranscript h768 (tableExtending cache table) msg salts positions
  fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)

def ideal0Observation (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let sOpen ← $ᵗ (Index → Salt128)
  let cv0 ← $ᵗ (Index → Digest)
  let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
  fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)

def marksHidden (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message)
    (positions : Positions) (sHidden : Index → Salt128) : World.Domain → Bool
  | .inr (.inl x) => decide (∃ i ∉ positions, hiddenCall0 h768 msg sHidden i = x)
  | _ => false

theorem real_ideal0_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) budget) :
    measureTVDist
      (realObservation h768 permutation cache msg positions observe)
      (ideal0Observation h768 permutation cache msg positions observe) ≤
      ((2 * keys.card + budget : Nat) : ℝ) / 2 ^ 128 +
      (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 := by
  classical
  let H : Finset Index := Finset.univ \ positions
  let progComp (sOpen sHidden : Index → Salt128) (cv0 : Index → Digest) (table : Compression) : ProbComp α :=
    let tbl' := tableExtending cache (reprogramFinset h768 table msg sHidden cv0 H)
    let tr := ideal0Transcript h768 tbl' msg sOpen cv0 positions
    fixedOracleRun ⟨tbl', permutation⟩ (observe tr.1 tr.2)
  let idealComp (sOpen : Index → Salt128) (cv0 : Index → Digest) (table : Compression) : ProbComp α :=
    let tbl := tableExtending cache table
    let tr := ideal0Transcript h768 tbl msg sOpen cv0 positions
    fixedOracleRun ⟨tbl, permutation⟩ (observe tr.1 tr.2)
  let progGame : ProbComp α := do
    let sOpen ← $ᵗ (Index → Salt128)
    let sHidden ← $ᵗ (Index → Salt128)
    let cv0 ← $ᵗ (Index → Digest)
    let table ← $ᵗ Compression
    progComp sOpen sHidden cv0 table
  -- A. Compare realObservation with progGame: they agree whenever `sHidden` avoids `cache` keys!
  have hRealProg : measureTVDist (realObservation h768 permutation cache msg positions observe) progGame ≤
      ((keys.card : ENNReal) / 2 ^ 128).toReal := by
    have hRealEq : 𝒟[realObservation h768 permutation cache msg positions observe] =
        𝒟[do let sOpen ← $ᵗ (Index → Salt128)
             let sHidden ← $ᵗ (Index → Salt128)
             let _cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             let tr := referenceTranscript h768 (tableExtending cache table) msg (saltsMerge positions sOpen sHidden) positions
             fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)] := by
      unfold realObservation
      trans 𝒟[do let table ← $ᵗ Compression
                 let sOpen ← $ᵗ (Index → Salt128)
                 let sHidden ← $ᵗ (Index → Salt128)
                 let tr := referenceTranscript h768 (tableExtending cache table) msg (saltsMerge positions sOpen sHidden) positions
                 fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)]
      · apply _root_.evalDist_bind_congr; intro table
        exact (saltsMerge_uniform_bind positions _).symm
      · rw [distribution_bind_comm ($ᵗ Compression)]
        apply _root_.evalDist_bind_congr; intro sOpen
        rw [distribution_bind_comm ($ᵗ Compression)]
        apply _root_.evalDist_bind_congr; intro sHidden
        exact (OracleComp.evalDist_bind_const ($ᵗ (Index → Digest)) _).symm
    have hProgEq : 𝒟[progGame] =
        𝒟[do let sOpen ← $ᵗ (Index → Salt128)
             let sHidden ← $ᵗ (Index → Salt128)
             let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen
               (fun i => if i ∈ H then table (hiddenCall0 h768 msg sHidden i) else cv0 i) positions
             fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)] := by
      unfold progGame progComp
      apply _root_.evalDist_bind_congr; intro sOpen
      apply _root_.evalDist_bind_congr; intro sHidden
      exact reprogramFinset_dist h768 msg sHidden H
        (fun tbl cv =>
          let t := tableExtending cache tbl
          let tr := ideal0Transcript h768 t msg sOpen cv positions
          fixedOracleRun ⟨t, permutation⟩ (observe tr.1 tr.2))
    rw [measureTVDist, hRealEq, hProgEq, ← measureTVDist]
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt128)) _ _ (by positivity)
    intro sOpen
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ (Index → Salt128)) _ _
      (fun sHidden => ∃ i ∉ positions, cache (hiddenCall0 h768 msg sHidden i) ≠ none) ?_).trans ?_
    · intro sHidden hdisj
      push_neg at hdisj
      apply EvalDistEq.of_evalDist_eq
      apply _root_.evalDist_bind_congr; intro cv0
      apply _root_.evalDist_bind_congr; intro table
      have htr : ideal0Transcript h768 (tableExtending cache table) msg sOpen
          (fun i => if i ∈ H then table (hiddenCall0 h768 msg sHidden i) else cv0 i) positions =
          referenceTranscript h768 (tableExtending cache table) msg (saltsMerge positions sOpen sHidden) positions := by
        rw [← ideal0Transcript_eq_reference_of_cv0 h768 (tableExtending cache table) msg sOpen sHidden positions]
        unfold ideal0Transcript
        have hlv : ideal0Leaves (fun x => tableExtending cache table (x.cast h768.symm)) msg sOpen
            (fun i => if i ∈ H then table (hiddenCall0 h768 msg sHidden i) else cv0 i) positions =
            ideal0Leaves (fun x => tableExtending cache table (x.cast h768.symm)) msg sOpen
            (fun i => tableExtending cache table (hiddenCall0 h768 msg sHidden i)) positions := by
          funext i
          unfold ideal0Leaves
          by_cases hi : i ∈ positions
          · simp [hi]
          · have hiH : i ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
            simp only [hi, ite_false, hiH, ite_true]
            have hnone := hdisj i hi
            have hte : (tableExtending cache table (hiddenCall0 h768 msg sHidden i) : Digest) =
                table (hiddenCall0 h768 msg sHidden i) := by
              change (cache (hiddenCall0 h768 msg sHidden i)).getD (table _) = _; rw [hnone]; rfl
            exact congrArg
              (fun d : Digest => leafChainFromCv0 (fun x => tableExtending cache table (x.cast h768.symm)) d (msg i))
              hte.symm
        exact congrArg
          (fun lv =>
            let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
            (nodeValFromLeaves c lv 24 0, referenceProof (nodeValFromLeaves c lv) sOpen positions))
          hlv
      rw [htr]
    · exact ENNReal.toReal_mono (by finiteness) (cache_keys_hit_hidden_128 h768 msg positions cache keys covered)
  -- B. Compare ideal0Observation with progGame using `oracle_change_distance_le_hit`!
  have hIdealProg : measureTVDist (ideal0Observation h768 permutation cache msg positions observe) progGame ≤
      ((keys.card + budget : Nat) : ℝ) / 2 ^ 128 +
      (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 := by
    have hIdEq : 𝒟[ideal0Observation h768 permutation cache msg positions observe] =
        𝒟[do let sOpen ← $ᵗ (Index → Salt128)
             let sHidden ← $ᵗ (Index → Salt128)
             let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             idealComp sOpen cv0 table] := by
      unfold ideal0Observation idealComp
      rw [distribution_bind_comm ($ᵗ Compression)]
      apply _root_.evalDist_bind_congr; intro sOpen
      trans 𝒟[do let _sHidden ← $ᵗ (Index → Salt128)
                 let table ← $ᵗ Compression
                 let cv0 ← $ᵗ (Index → Digest)
                 let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
                 fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)]
      · exact (OracleComp.evalDist_bind_const ($ᵗ (Index → Salt128)) _).symm
      · apply _root_.evalDist_bind_congr; intro sHidden
        exact distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Digest)) _
    rw [measureTVDist, hIdEq, ← measureTVDist]
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt128)) _ _ (by positivity)
    intro sOpen
    -- Define the full honest+observe OracleComp for fixed `sOpen, cv0`!
    let fullComp (cv0 : Index → Digest) : OracleComp World α := do
      let nodes ← queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)
      observe (nodes 24 0) (referenceProof nodes sOpen positions)
    have hfull_fixed : ∀ (o : Oracle) (cv0 : Index → Digest),
        fixedOracleRun o (fullComp cv0) =
          let tr := ideal0Transcript h768 o.compression msg sOpen cv0 positions
          fixedOracleRun o (observe tr.1 tr.2) := by
      intro o cv0
      obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
        (ideal0LeafFn h768 msg sOpen cv0 positions)
        (ideal0Leaves (fun x => o.compression (x.cast h768.symm)) msg sOpen cv0 positions)
        (fun i => by
          unfold ideal0LeafFn ideal0Leaves
          by_cases hi : i ∈ positions
          · rw [if_pos hi, if_pos hi]; exact queryLeafOpened_fixed h768 o i (sOpen i) (msg i)
          · rw [if_neg hi, if_neg hi]; exact queryLeafFromCv0_fixed h768 o (cv0 i) (msg i))
      unfold fullComp
      rw [fixed_oracle_run_bind, hrun, pure_bind]
      have hroot : nodes 24 0 = nodeValFromLeaves (fun x => o.compression (x.cast h768.symm))
          (ideal0Leaves (fun x => o.compression (x.cast h768.symm)) msg sOpen cv0 positions) 24 0 :=
        hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
      have hpf : referenceProof nodes sOpen positions =
          referenceProof (nodeValFromLeaves (fun x => o.compression (x.cast h768.symm))
            (ideal0Leaves (fun x => o.compression (x.cast h768.symm)) msg sOpen cv0 positions)) sOpen positions :=
        referenceProof_congr_nodes _ _ hval sOpen positions
      rw [hroot, hpf]; rfl
    -- Apply `oracle_change_distance_le_hit` pointwise on `(sHidden, cv0, table)`!
    let hitProb (sHidden : Index → Salt128) : ENNReal :=
      prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
        (do let cv0 ← $ᵗ (Index → Digest)
            let table ← $ᵗ Compression
            flaggedRun ⟨tableExtending cache table, permutation⟩
              (marksHidden h768 msg positions sHidden) (fullComp cv0)))
    have hpt : ∀ (sHidden : Index → Salt128) (cv0 : Index → Digest) (table : Compression),
        measureTVDist (idealComp sOpen cv0 table) (progComp sOpen sHidden cv0 table) ≤
        (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          flaggedRun ⟨tableExtending cache table, permutation⟩
            (marksHidden h768 msg positions sHidden) (fullComp cv0))).toReal := by
      intro sHidden cv0 table
      unfold idealComp progComp
      rw [← hfull_fixed ⟨tableExtending cache table, permutation⟩ cv0,
        ← hfull_fixed ⟨tableExtending cache (reprogramFinset h768 table msg sHidden cv0 H), permutation⟩ cv0]
      apply oracle_change_distance_le_hit
      intro query hunm
      rcases query with coins | pq
      · simp only [Oracle.world, QueryImpl.add_apply_inl]
      · rcases pq with x | permq
        · simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_inj]
          have hnot : ∀ i ∈ H, hiddenCall0 h768 msg sHidden i ≠ x := by
            intro i hi heq
            have hni : i ∉ positions := (Finset.mem_sdiff.mp hi).2
            simp [marksHidden] at hunm
            exact hunm i hni heq
          change (cache x).getD (table x) = (cache x).getD (reprogramFinset h768 table msg sHidden cv0 H x)
          rw [reprogramFinset_not_mem h768 table msg sHidden cv0 H x hnot]
        · rcases permq <;> simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr]
    have havg := distance_bind_le_averaged_bad
      (do let sHidden ← $ᵗ (Index → Salt128)
          let cv0 ← $ᵗ (Index → Digest)
          let table ← $ᵗ Compression
          pure (sHidden, cv0, table))
      (fun p => idealComp sOpen p.2.1 p.2.2)
      (fun p => progComp sOpen p.1 p.2.1 p.2.2)
      (fun p => flaggedRun ⟨tableExtending cache p.2.2, permutation⟩
        (marksHidden h768 msg positions p.1) (fullComp p.2.1))
      (fun ⟨sH, cv0, tbl⟩ => hpt sH cv0 tbl)
    -- Bound the averaged hit event by splitting `fullComp` into honest tree + `observe`!
    -- Under fixed `(table, cv0)`, `fullComp`'s trace is `treeTrace ++ obsTrace`.
    have hhit_total :
        (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          (do let sHidden ← $ᵗ (Index → Salt128)
              let cv0 ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              flaggedRun ⟨tableExtending cache table, permutation⟩
                (marksHidden h768 msg positions sHidden) (fullComp cv0)))) ≤
        ((keys.card + budget : Nat) : ENNReal) / 2 ^ 128 +
        (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
      -- For fixed `(sHidden, cv0, table)`, split `flaggedRun` on `fullComp cv0`:
      -- `flaggedRun o m (A >>= B)` hits iff `A` hits OR `B` hits!
      have hflag_split : ∀ (o : Oracle) (m : World.Domain → Bool) (cv0 : Index → Digest),
          (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$> flaggedRun o m (fullComp cv0))) ≤
          (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
            flaggedRun o m (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)))) +
          (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
            let tr := ideal0Transcript h768 o.compression msg sOpen cv0 positions
            flaggedRun o m (observe tr.1 tr.2))) := by
        intro o m cv0
        have hrun_tree : ∃ nodes,
            fixedOracleRun o (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)) = pure nodes ∧
            (nodes 24 0, referenceProof nodes sOpen positions) = ideal0Transcript h768 o.compression msg sOpen cv0 positions := by
          obtain ⟨nodes, hr, hv⟩ := queryTreeFromLeafFn_fixed h768 o
            (ideal0LeafFn h768 msg sOpen cv0 positions)
            (ideal0Leaves (fun x => o.compression (x.cast h768.symm)) msg sOpen cv0 positions)
            (fun i => by
              unfold ideal0LeafFn ideal0Leaves
              by_cases hi : i ∈ positions
              · rw [if_pos hi, if_pos hi]; exact queryLeafOpened_fixed h768 o i (sOpen i) (msg i)
              · rw [if_neg hi, if_neg hi]; exact queryLeafFromCv0_fixed h768 o (cv0 i) (msg i))
          refine ⟨nodes, hr, ?_⟩
          exact Prod.ext (hv 24 (le_refl _) 0 (by rw [levelSize_24]; omega))
            (referenceProof_congr_nodes _ _ hv sOpen positions)
        -- `flaggedRun o m (A >>= B) false` splits cleanly by `simulateQ_bind`!
        have hbind_flag : ∀ {β γ : Type} (A : OracleComp World β) (B : β → OracleComp World γ) (f : Bool),
            flaggedRun o m (A >>= B) f = (do
              let r1 ← flaggedRun o m A f
              flaggedRun o m (B r1.1) r1.2.2) := by
          intro β γ A B f; simp [flaggedRun, simulateQ_bind, StateT.run_bind]
        rw [hbind_flag]
        have hstep := prEvent_bind_le_prEvent_add_of_support
          (flaggedRun o m (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)))
          (fun r1 => flaggedRun o m (observe (r1.1 24 0) (referenceProof r1.1 sOpen positions)) r1.2.2)
          (fun r1 => r1.2.2 = true)
          (fun r2 => r2.2.2 = true)
          (ε := prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
            let tr := ideal0Transcript h768 o.compression msg sOpen cv0 positions
            flaggedRun o m (observe tr.1 tr.2)))
          (fun r1 hr1 hnot => by
            have hfalse : r1.2.2 = false := Bool.eq_false_iff.mpr hnot
            rw [hfalse]
            obtain ⟨nodes, htrun, htrEq⟩ := hrun_tree
            have hproj : r1.1 ∈ support (Prod.fst <$> flaggedRun o m
                (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))) := by
              rw [support_map]; exact ⟨r1, hr1, rfl⟩
            rw [flagged_run_projection, htrun, support_pure, Set.mem_singleton_iff] at hproj
            have h1 : r1.1 24 0 = (ideal0Transcript h768 o.compression msg sOpen cv0 positions).1 := by
              rw [hproj]; exact congrArg Prod.fst htrEq
            have h2 : referenceProof r1.1 sOpen positions =
                (ideal0Transcript h768 o.compression msg sOpen cv0 positions).2 := by
              rw [hproj]; exact congrArg Prod.snd htrEq
            rw [h1, h2])
        exact hstep
      -- Split total hit probability into Tree hit + Observe hit!
      have hsplit_all :
          (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt128)
                let cv0 ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden) (fullComp cv0)))) ≤
          (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt128)
                let cv0 ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden)
                  (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))))) +
          (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt128)
                let cv0 ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
                flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden)
                  (observe tr.1 tr.2)))) := by
        simp only [map_bind, prEvent_bind_eq_tsum_prEvent]
        rw [← ENNReal.tsum_add]
        apply ENNReal.tsum_le_tsum; intro sH
        rw [← mul_add, ← ENNReal.tsum_add]
        apply mul_le_mul_of_nonneg_left _ zero_le
        apply ENNReal.tsum_le_tsum; intro cv0
        rw [← mul_add, ← ENNReal.tsum_add]
        apply mul_le_mul_of_nonneg_left _ zero_le
        apply ENNReal.tsum_le_tsum; intro tbl
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ zero_le
        exact hflag_split ⟨tableExtending cache tbl, permutation⟩ (marksHidden h768 msg positions sH) cv0
      -- Part B1: Observe hit probability <= budget / 2^128!
      have hObsHit :
          (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt128)
                let cv0 ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
                flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden)
                  (observe tr.1 tr.2)))) ≤ (budget : ENNReal) / 2 ^ 128 := by
        letI : MeasurableSpace (α × Unit × Bool) := ⊤
        -- Swap `sHidden` inside `(cv0, table)` since `(tr, table)` is independent of `sHidden`!
        have hswap1 :
            𝒟[do let sHidden ← $ᵗ (Index → Salt128)
                 let cv0 ← $ᵗ (Index → Digest)
                 let table ← $ᵗ Compression
                 let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
                 flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden)
                   (observe tr.1 tr.2)] =
            𝒟[do let cv0 ← $ᵗ (Index → Digest)
                 let table ← $ᵗ Compression
                 let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
                 let traced ← fixedOracleRun ⟨tableExtending cache table, permutation⟩ (traceCompression (observe tr.1 tr.2))
                 let sHidden ← $ᵗ (Index → Salt128)
                 pure (traced.1, (), traced.2.any (fun x => decide (∃ i ∉ positions, hiddenCall0 h768 msg sHidden i = x)))] := by
          rw [distribution_bind_comm ($ᵗ (Index → Salt128)) ($ᵗ (Index → Digest))]
          apply _root_.evalDist_bind_congr; intro cv0
          rw [distribution_bind_comm ($ᵗ (Index → Salt128)) ($ᵗ Compression)]
          apply _root_.evalDist_bind_congr; intro table
          -- Express `flaggedRun ... (marksHidden ...)` via `traceCompression`!
          have hft : ∀ (o : Oracle) (comp : OracleComp World α) (sH : Index → Salt128) (f : Bool),
              flaggedRun o (marksHidden h768 msg positions sH) comp f =
              (fun r : α × List (BitVec COMPRESSION_INPUT_LENGTH) =>
                (r.1, (), f || r.2.any (fun x => decide (∃ i ∉ positions, hiddenCall0 h768 msg sH i = x)))) <$>
                fixedOracleRun o (traceCompression comp) := by
            intro o comp sH f
            induction comp using OracleComp.inductionOn generalizing f with
            | pure v =>
              simp only [flaggedRun, simulateQ_pure, StateT.run_pure, trace_compression_pure,
                fixed_oracle_run_pure, map_pure, List.any_nil, Bool.or_false]
            | query_bind q k ih =>
              rw [flagged_run_query_bind, trace_run_query_bind, map_bind]
              apply bind_congr; intro ans; rw [ih]; simp only [bind_pure_comp, Functor.map_map]
              apply congrArg (fun g => g <$> fixedOracleRun o (traceCompression (k ans)))
              funext r
              have hhd : (compressionHead q).any (fun x => decide (∃ i ∉ positions, hiddenCall0 h768 msg sH i = x)) =
                  marksHidden h768 msg positions sH q := by
                rcases q with _ | pq
                · rfl
                · rcases pq with x | permq
                  · change (decide (∃ i ∉ positions, hiddenCall0 h768 msg sH i = x) || false) = _
                    exact Bool.or_false _
                  · rcases permq <;> rfl
              simp only [List.any_append, hhd, Bool.or_assoc]
          simp only [hft, Bool.false_or, map_eq_bind_pure_comp]
          exact distribution_bind_comm ($ᵗ (Index → Salt128)) _ _
        rw [(EvalDistEq.of_evalDist_eq hswap1).prEvent_eq (fun r => r.2.2 = true)]
        apply prEvent_bind_le_of_forall_le_of_support; intro cv0 _
        apply prEvent_bind_le_of_forall_le_of_support; intro table _
        apply prEvent_bind_le_of_forall_le_of_support; intro traced htraced
        rw [bind_pure_comp, prEvent_map]
        have hlen := trace_run_length ⟨tableExtending cache table, permutation⟩ _ budget (hobs _ _) traced htraced
        have hle : (prEvent ((fun sH => traced.2.any (fun x => decide (∃ i ∉ positions, hiddenCall0 h768 msg sH i = x)) = true) <$>
            ($ᵗ (Index → Salt128)))) ≤
            (prEvent ((fun sH => ∃ v ∈ traced.2.map (fun x => x.extractLsb' 0 192), v ∈ hiddenPrefixes positions sH) <$>
              ($ᵗ (Index → Salt128)))) := by
          apply prEvent_mono_of_support
          intro sH _ hany
          obtain ⟨x, hx, hdec⟩ := List.any_eq_true.mp hany
          obtain ⟨i, hi, rfl⟩ := decide_eq_true_eq.mp hdec
          refine ⟨(hiddenCall0 h768 msg sH i).extractLsb' 0 192, List.mem_map.mpr ⟨_, hx, rfl⟩, ?_⟩
          unfold hiddenCall0
          rw [extractLsb'_cast_eq, leafCall0Input_prefix192]
          exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
        exact hle.trans ((list_prefix_hit_128 positions _).trans (by
          simp only [List.length_map]
          exact ENNReal.div_le_div_right (Nat.cast_le.mpr hlen) _))
      -- Part B2: Honest Tree hit probability <= keys.card / 2^128 + (LENGTH + HONEST_TREE_BUDGET) * LENGTH / 2^192!
      have hTreeHit :
          (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
            (do let sHidden ← $ᵗ (Index → Salt128)
                let cv0 ← $ᵗ (Index → Digest)
                let table ← $ᵗ Compression
                flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden)
                  (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))))) ≤
          (keys.card : ENNReal) / 2 ^ 128 +
          (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
        -- For fixed `sHidden`, split on whether `cache` already hits `hiddenPrefixes positions sHidden`!
        let P (sH : Index → Salt128) := hiddenPrefixes positions sH
        have hstep_sH : ∀ sH : Index → Salt128, ¬ CacheHitsPrefix cache (P sH) →
            (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
              (do let cv0 ← $ᵗ (Index → Digest)
                  let table ← $ᵗ Compression
                  flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sH)
                    (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))))) ≤
            (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
          intro sH hclean
          -- Split on whether `cv0` hits `P sH`:
          -- (1) `Pr_{cv0}[∃ i ∉ positions, (cv0 i)[0..192) ∈ P sH] <= LENGTH * (P sH).card / 2^192`
          -- (2) For clean `cv0`, by `queryIdeal0Tree_good_trace` + `compression_sampling_equivalence`
          --     + `compression_run_hits_prefix_bound`, prob `<= HONEST_TREE_BUDGET * (P sH).card / 2^192`!
          have hcv0_bad : (prEvent ((fun cv0 : Index → Digest => ∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P sH) <$>
              ($ᵗ (Index → Digest)))) ≤ (LENGTH : ENNReal) * ((P sH).card : ENNReal) / 2 ^ 192 := by
            have hlist : ∀ (is : List Index),
                (prEvent ((fun cv0 : Index → Digest => ∃ i ∈ is, (cv0 i).extractLsb' 0 192 ∈ P sH) <$>
                  ($ᵗ (Index → Digest)))) ≤ (is.length : ENNReal) * ((P sH).card : ENNReal) / 2 ^ 192 := by
              intro is; induction is with
              | nil =>
                have hz : (prEvent ((fun cv0 : Index → Digest => ∃ i ∈ ([] : List Index), (cv0 i).extractLsb' 0 192 ∈ P sH) <$> ($ᵗ (Index → Digest)))) = 0 :=
                  prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ ⟨_, hi, _⟩ => List.not_mem_nil hi)
                rw [hz]; exact zero_le
              | cons i rest ih =>
                have hu := prEvent_or_le ($ᵗ (Index → Digest))
                  (fun cv0 => (cv0 i).extractLsb' 0 192 ∈ P sH)
                  (fun cv0 => ∃ j ∈ rest, (cv0 j).extractLsb' 0 192 ∈ P sH)
                have hmono : (prEvent ((fun cv0 => ∃ j ∈ i :: rest, (cv0 j).extractLsb' 0 192 ∈ P sH) <$> ($ᵗ (Index → Digest)))) ≤ _ :=
                  (prEvent_mono_of_support _ _ _ (fun cv0 _ ⟨j, hj, hm⟩ => by
                    rcases List.mem_cons.mp hj with rfl | hr
                    · exact Or.inl hm
                    · exact Or.inr ⟨j, hr, hm⟩)).trans hu
                have hone : (prEvent ((fun cv0 : Index → Digest => (cv0 i).extractLsb' 0 192 ∈ P sH) <$> ($ᵗ (Index → Digest)))) ≤
                    ((P sH).card : ENNReal) / 2 ^ 192 :=
                  prEvent_uniform_coord_le (D := Index) (R := Digest) i
                    (fun fresh => fresh.extractLsb' 0 192 ∈ P sH) (uniform_digest_hits_prefix_le (P sH))
                refine (hmono.trans (add_le_add hone ih)).trans ?_
                simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
                rw [add_mul, one_mul, ENNReal.add_div, add_comm]
            have hle : (prEvent ((fun cv0 => ∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P sH) <$> ($ᵗ (Index → Digest)))) ≤
                (prEvent ((fun cv0 => ∃ i ∈ (Finset.univ : Finset Index).toList, (cv0 i).extractLsb' 0 192 ∈ P sH) <$> ($ᵗ (Index → Digest)))) :=
              prEvent_mono_of_support _ _ _ (fun _ _ ⟨i, _, hm⟩ => ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), hm⟩)
            exact hle.trans (by
              simpa only [Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using
                hlist (Finset.univ : Finset Index).toList)
          have hcv0_clean : ∀ cv0 : Index → Digest, ¬ (∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P sH) →
              (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
                (($ᵗ Compression) >>= fun table =>
                  flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sH)
                    (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))))) ≤
              (HONEST_TREE_BUDGET : ENNReal) * ((P sH).card : ENNReal) / 2 ^ 192 := by
            intro cv0 hcv0_ok
            let comp := queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)
            have hcomp_bd : PublicQueryBound comp HONEST_TREE_BUDGET := by
              apply queryTreeFromLeafFn_bound h768
              intro i; unfold ideal0LeafFn
              by_cases hi : i ∈ positions
              · rw [if_pos hi]; exact queryLeafOpened_bound h768 i (sOpen i) (msg i)
              · rw [if_neg hi]; exact (queryLeafFromCv0_bound h768 (cv0 i) (msg i)).mono (by omega)
            -- Show that if `flaggedRun` hits `marksHidden`, then `traceCompressionReplies` contains a pair whose
            -- answer has `ans[0..192) ∈ P sH`!
            have hhit_le_tr :
                (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
                  (($ᵗ Compression) >>= fun table =>
                    flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sH) comp))) ≤
                (prEvent ((fun res : (Nat → Nat → Digest) × CompressionReplies =>
                  ∃ pair ∈ res.2, pair.2.extractLsb' 0 192 ∈ P sH) <$>
                  (($ᵗ Compression) >>= fun table =>
                    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (traceCompressionReplies comp)))) := by
              simp only [map_bind, prEvent_bind_eq_tsum_prEvent]
              apply ENNReal.tsum_le_tsum; intro table
              apply mul_le_mul_of_nonneg_left _ zero_le
              let o : Oracle := ⟨tableExtending cache table, permutation⟩
              obtain ⟨nodes, trace, htr_run, hgood⟩ := queryIdeal0Tree_good_trace h768 o msg sOpen cv0 positions
              have hflag_tr : ∀ {β : Type} (c : OracleComp World β) (f : Bool),
                  flaggedRun o (marksHidden h768 msg positions sH) c f =
                  (fun r : β × CompressionReplies =>
                    (r.1, (), f || r.2.any (fun p => decide (∃ i ∉ positions, hiddenCall0 h768 msg sH i = p.1)))) <$>
                    fixedOracleRun o (traceCompressionReplies c) := by
                intro β c
                induction c using OracleComp.inductionOn with
                | pure v =>
                  intro f
                  change pure (v, ((), f)) =
                    (fun r : β × CompressionReplies => _) <$> fixedOracleRun o (pure (v, []))
                  rw [fixed_oracle_run_pure, map_pure]
                  simp only [List.any_nil, Bool.or_false]
                | query_bind q k ih =>
                  intro f
                  rw [flagged_run_query_bind]
                  rcases q with coins | pq
                  · change (o.world (.inl coins) >>= fun ans =>
                        flaggedRun o (marksHidden h768 msg positions sH) (k ans) (f || false)) =
                      _ <$> fixedOracleRun o ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
                        traceCompressionReplies (k ans))
                    rw [fixed_run_query_bind, map_bind]
                    apply bind_congr; intro ans
                    rw [Bool.or_false, ih ans f]
                  · rcases pq with x | permq
                    · let ans0 : Digest := o.compression x
                      have hcomp :
                          fixedOracleRun o ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>=
                            fun (ans : Digest) => traceCompressionReplies (k ans) >>= fun (v, tr) => pure (v, (x, ans) :: tr)) =
                          fixedOracleRun o (traceCompressionReplies (k ans0) >>= fun (v, tr) => pure (v, (x, ans0) :: tr)) :=
                        fixed_oracle_run_compress o x _
                      change ((pure ans0 : ProbComp Digest) >>= fun (ans : Digest) =>
                            flaggedRun o (marksHidden h768 msg positions sH) (k ans)
                              (f || decide (∃ i ∉ positions, hiddenCall0 h768 msg sH i = x))) =
                          _ <$> fixedOracleRun o ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>=
                            fun (ans : Digest) => traceCompressionReplies (k ans) >>= fun (v, tr) => pure (v, (x, ans) :: tr))
                      rw [pure_bind, hcomp, ih ans0, fixed_oracle_run_bind, map_bind, map_eq_bind_pure_comp]
                      apply bind_congr; rintro ⟨v, tr⟩
                      rw [fixed_oracle_run_pure, map_pure]
                      simp only [List.any_cons, Bool.or_assoc]
                      rfl
                    · change (o.world (.inr (.inr permq)) >>= fun ans =>
                          flaggedRun o (marksHidden h768 msg positions sH) (k ans) (f || false)) =
                        _ <$> fixedOracleRun o ((liftM (World.query (.inr (.inr permq))) : OracleComp World _) >>= fun ans =>
                          traceCompressionReplies (k ans))
                      rw [fixed_run_query_bind, map_bind]
                      apply bind_congr; intro ans
                      rw [Bool.or_false, ih ans f]
              rw [hflag_tr comp false, htr_run, map_pure]
              apply prEvent_pure_le_pure
              intro hhit
              simp only [Bool.false_or] at hhit
              obtain ⟨p, hp, hdec⟩ := List.any_eq_true.mp hhit
              obtain ⟨i, hi, hpeq⟩ := decide_eq_true_eq.mp hdec
              have hp192 : p.1.extractLsb' 0 192 ∈ P sH := by
                rw [← hpeq]; unfold hiddenCall0 P hiddenPrefixes
                rw [extractLsb'_cast_eq, leafCall0Input_prefix192]
                exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
              have hpTag : p.1.extractLsb' 128 64 = leafTag i := by
                rw [← hpeq]; unfold hiddenCall0
                rw [extractLsb'_cast_eq, leafCall0Input_tag]
              rcases hgood p hp with ⟨j, hj, hjt⟩ | ⟨j, hj, hjcv⟩ | ⟨q, hq, hqeq⟩
              · have : j = i := leafTag_injective (hjt.symm.trans hpTag)
                exact (hi (this ▸ hj)).elim
              · exact (hcv0_ok ⟨j, hj, hjcv ▸ hp192⟩).elim
              · exact ⟨q, hq, hqeq ▸ hp192⟩
            -- Now use `compression_sampling_equivalence` to move to `compressionRun`!
            have heq_rom := (EvalDistEq.of_evalDist_eq
              (compression_sampling_equivalence permutation (traceCompressionReplies comp) cache)).prEvent_eq
                (fun res : (Nat → Nat → Digest) × CompressionReplies => ∃ pair ∈ res.2, pair.2.extractLsb' 0 192 ∈ P sH)
            simp only [Functor.map_map, Function.comp_def] at heq_rom
            rw [← heq_rom] at hhit_le_tr
            have hin_cache :
                (prEvent ((fun res : ((Nat → Nat → Digest) × CompressionReplies) × CompressionCache =>
                  ∃ pair ∈ res.1.2, pair.2.extractLsb' 0 192 ∈ P sH) <$>
                  (compressionRun permutation (traceCompressionReplies comp) cache))) ≤
                (prEvent ((fun res => CacheHitsPrefix res.2 (P sH)) <$>
                  (compressionRun permutation (traceCompressionReplies comp) cache))) := by
              apply prEvent_mono_of_support
              intro res hreach ⟨pair, hmem, hpref⟩
              exact ⟨pair.1, pair.2, (traceReplies_compressionRun_cache permutation comp cache res hreach).2 pair hmem, hpref⟩
            have hrom_bd := compression_run_hits_prefix_bound permutation (traceCompressionReplies comp)
              HONEST_TREE_BUDGET (traceReplies_bound comp HONEST_TREE_BUDGET hcomp_bd) cache (P sH) hclean
            refine hhit_le_tr.trans (hin_cache.trans (hrom_bd.trans ?_))
            rw [mul_div_assoc]
          -- Combine `hcv0_bad` and `hcv0_clean`!
          have hcomb := prEvent_bind_le_prEvent_add_of_support
            ($ᵗ (Index → Digest))
            (fun cv0 => ($ᵗ Compression) >>= fun table =>
              flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sH)
                (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)))
            (fun cv0 => ∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P sH)
            (fun res => res.2.2 = true)
            (fun cv0 _ hok => hcv0_clean cv0 hok)
          refine (hcomb.trans (add_le_add hcv0_bad le_rfl)).trans ?_
          have hcard : (P sH).card ≤ LENGTH := hiddenPrefixes_card_le positions sH
          rw [← ENNReal.add_div, ← add_mul]
          apply ENNReal.div_le_div_right
          calc
            ((LENGTH : ENNReal) + HONEST_TREE_BUDGET) * ((P sH).card : ENNReal)
              ≤ ((LENGTH : ENNReal) + HONEST_TREE_BUDGET) * (LENGTH : ENNReal) :=
                mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) zero_le
            _ = (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) := by push_cast; rfl
        have houter := prEvent_bind_le_prEvent_add_of_support
          ($ᵗ (Index → Salt128))
          (fun sH => do
            let cv0 ← $ᵗ (Index → Digest)
            let table ← $ᵗ Compression
            flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sH)
              (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)))
          (fun sH => CacheHitsPrefix cache (P sH))
          (fun res => res.2.2 = true)
          (fun sH _ hclean => hstep_sH sH hclean)
        exact houter.trans (add_le_add (cache_vals_hit_hidden_128 positions cache keys covered) le_rfl)
      refine (hsplit_all.trans (add_le_add hTreeHit hObsHit)).trans ?_
      rw [add_right_comm, ← ENNReal.add_div]
      push_cast; rfl
    have hflat :
        𝒟[do let sHidden ← $ᵗ (Index → Salt128)
             let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             idealComp sOpen cv0 table] =
        𝒟[(do let sHidden ← $ᵗ (Index → Salt128)
              let cv0 ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              pure (sHidden, cv0, table)) >>= fun p => idealComp sOpen p.2.1 p.2.2] := by
      simp [bind_assoc]
    have hflat2 :
        𝒟[do let sHidden ← $ᵗ (Index → Salt128)
             let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             progComp sOpen sHidden cv0 table] =
        𝒟[(do let sHidden ← $ᵗ (Index → Salt128)
              let cv0 ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              pure (sHidden, cv0, table)) >>= fun p => progComp sOpen p.1 p.2.1 p.2.2] := by
      simp [bind_assoc]
    have hflat3 :
        (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          ((do let sHidden ← $ᵗ (Index → Salt128)
               let cv0 ← $ᵗ (Index → Digest)
               let table ← $ᵗ Compression
               pure (sHidden, cv0, table)) >>= fun p =>
            flaggedRun ⟨tableExtending cache p.2.2, permutation⟩ (marksHidden h768 msg positions p.1) (fullComp p.2.1)))) =
        (prEvent ((fun res : α × Unit × Bool => res.2.2 = true) <$>
          (do let sHidden ← $ᵗ (Index → Salt128)
              let cv0 ← $ᵗ (Index → Digest)
              let table ← $ᵗ Compression
              flaggedRun ⟨tableExtending cache table, permutation⟩ (marksHidden h768 msg positions sHidden) (fullComp cv0)))) := by
      simp [bind_assoc]
    rw [measureTVDist, hflat, hflat2, ← measureTVDist]
    refine havg.trans ?_
    rw [hflat3]
    have htoReal := ENNReal.toReal_mono (by finiteness) hhit_total
    refine htoReal.trans ?_
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    rfl
  -- Combine Step A and Step B via triangle inequality!
  rw [measureTVDist_comm] at hIdealProg
  refine ((measureTVDist_triangle _ progGame _).trans (add_le_add hRealProg hIdealProg)).trans ?_
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  rw [← add_assoc, ← add_div]
  push_cast
  have : ((keys.card : ℝ) + (keys.card + budget)) / 2 ^ 128 = (2 * keys.card + budget) / 2 ^ 128 := by ring
  rw [this]

/-! ### 6. Step 2: Ideal0(m₀) ↔ Ideal0(m₁) 256-bit Leaf-by-Leaf Hybrid -/

def hybridMessage (left right : Message) (indices : List Index) : Message :=
  fun i => if i ∈ indices then right i else left i

theorem ideal0_coordinate_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) budget)
    (hidden : Index) (hunopen : hidden ∉ positions) (left right : Entry) :
    measureTVDist
      (ideal0Observation h768 permutation cache (Function.update msg hidden left) positions observe)
      (ideal0Observation h768 permutation cache (Function.update msg hidden right) positions observe) ≤
      6 * ((keys.card + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256 := by
  -- For fixed `sOpen` and other `cv0` coordinates, isolate `cv0 hidden` and apply `cached_chain3_distance`!
  let exceptComp (sOpen : Index → Salt128) (cv0 : Index → Digest) (d : Digest) : OracleComp World α := do
    let nodes ← queryTreeFromLeafFn h768 (fun i =>
      if i = hidden then pure d else ideal0LeafFn h768 msg sOpen cv0 positions i)
    observe (nodes 24 0) (referenceProof nodes sOpen positions)
  have hexcept_bd : ∀ sOpen cv0 d, PublicQueryBound (exceptComp sOpen cv0 d) (HONEST_TREE_BUDGET + budget) := by
    intro sOpen cv0 d
    apply public_query_bound_bind _ (fun nodes => hobs _ _)
    apply queryTreeFromLeafFn_bound h768
    intro i
    by_cases hih : i = hidden
    · rw [if_pos hih]; exact (public_query_bound_pure' d 0).mono (by omega)
    · rw [if_neg hih]; unfold ideal0LeafFn
      by_cases hi : i ∈ positions
      · rw [if_pos hi]; exact queryLeafOpened_bound h768 i (sOpen i) (msg i)
      · rw [if_neg hi]; exact (queryLeafFromCv0_bound h768 (cv0 i) (msg i)).mono (by omega)
  have hupdate_eq : ∀ (val : Entry),
      𝒟[ideal0Observation h768 permutation cache (Function.update msg hidden val) positions observe] =
      𝒟[do let sOpen ← $ᵗ (Index → Salt128)
           let cv0 ← $ᵗ (Index → Digest)
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Digest
           let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
           fixedOracleRun ⟨tableExtending cache table, permutation⟩
             (exceptComp sOpen cv0 (leafChainFromCv0 c fresh val))] := by
    intro val
    unfold ideal0Observation
    rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Salt128))]
    apply _root_.evalDist_bind_congr; intro sOpen
    trans 𝒟[do let table ← $ᵗ Compression
               let cv0 ← $ᵗ (Index → Digest)
               let fresh ← $ᵗ Digest
               let tr := ideal0Transcript h768 (tableExtending cache table) (Function.update msg hidden val)
                 sOpen (Function.update cv0 hidden fresh) positions
               fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)]
    · apply _root_.evalDist_bind_congr; intro table
      exact (uniform_coordinate_bind hidden _).symm
    · rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Digest))]
      apply _root_.evalDist_bind_congr; intro cv0
      apply _root_.evalDist_bind_congr; intro table
      apply _root_.evalDist_bind_congr; intro fresh
      let o : Oracle := ⟨tableExtending cache table, permutation⟩
      let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
      obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
        (fun i => if i = hidden then pure (leafChainFromCv0 c fresh val) else ideal0LeafFn h768 msg sOpen cv0 positions i)
        (ideal0Leaves c (Function.update msg hidden val) sOpen (Function.update cv0 hidden fresh) positions)
        (fun i => by
          by_cases hih : i = hidden
          · subst hih; simp [ideal0Leaves, hunopen, fixed_oracle_run_pure]
          · simp only [if_neg hih, ideal0LeafFn, ideal0Leaves, Function.update_of_ne hih]
            by_cases hi : i ∈ positions
            · rw [if_pos hi, if_pos hi]; exact queryLeafOpened_fixed h768 o i (sOpen i) (msg i)
            · rw [if_neg hi, if_neg hi]; exact queryLeafFromCv0_fixed h768 o (cv0 i) (msg i))
      unfold exceptComp
      rw [fixed_oracle_run_bind, hrun, pure_bind]
      have hrt : nodes 24 0 = (ideal0Transcript h768 o.compression (Function.update msg hidden val) sOpen
          (Function.update cv0 hidden fresh) positions).1 :=
        hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
      have hpf : referenceProof nodes sOpen positions =
          (ideal0Transcript h768 o.compression (Function.update msg hidden val) sOpen
            (Function.update cv0 hidden fresh) positions).2 :=
        referenceProof_congr_nodes _ _ hval sOpen positions
      rw [hrt, hpf]
  rw [measureTVDist, hupdate_eq left, hupdate_eq right, ← measureTVDist]
  apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt128)) _ _ (by positivity)
  intro sOpen
  apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Digest)) _ _ (by positivity)
  intro cv0
  have hl := cached_chain3_distance h768 permutation cache keys covered left
    (exceptComp sOpen cv0) (HONEST_TREE_BUDGET + budget) (hexcept_bd sOpen cv0)
  have hr := cached_chain3_distance h768 permutation cache keys covered right
    (exceptComp sOpen cv0) (HONEST_TREE_BUDGET + budget) (hexcept_bd sOpen cv0)
  rw [measureTVDist_comm] at hr
  refine ((measureTVDist_triangle _ _ _).trans (add_le_add hl hr)).trans ?_
  exact le_of_eq (by ring)

theorem ideal0_hybrid_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (left right : Message) (positions : Positions)
    (hagree : ∀ i ∈ positions, left i = right i)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (budget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) budget) :
    measureTVDist
      (ideal0Observation h768 permutation cache left positions observe)
      (ideal0Observation h768 permutation cache right positions observe) ≤
      (LENGTH : ℝ) * (6 * ((keys.card + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256) := by
  let stepLoss : ℝ := 6 * ((keys.card + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256
  have hnn : 0 ≤ stepLoss := by positivity
  have hgen : ∀ (indices : List Index),
      measureTVDist
        (ideal0Observation h768 permutation cache left positions observe)
        (ideal0Observation h768 permutation cache (hybridMessage left right indices) positions observe) ≤
        (indices.length : ℝ) * stepLoss := by
    intro indices; induction indices with
    | nil =>
      have hnil : hybridMessage left right [] = left := by funext i; simp [hybridMessage]
      simp [hnil]
    | cons i rest ih =>
      have hcons : hybridMessage left right (i :: rest) = Function.update (hybridMessage left right rest) i (right i) := by
        funext j; by_cases hj : j = i <;> simp [hybridMessage, hj]
      have hstep : measureTVDist
          (ideal0Observation h768 permutation cache (hybridMessage left right rest) positions observe)
          (ideal0Observation h768 permutation cache (hybridMessage left right (i :: rest)) positions observe) ≤ stepLoss := by
        rw [hcons]
        by_cases hi : i ∈ positions
        · have hsame : right i = hybridMessage left right rest i := by
            unfold hybridMessage; split
            · rfl
            · exact (hagree i hi).symm
          rw [hsame, Function.update_eq_self, measureTVDist_self]; exact hnn
        · have hchg := ideal0_coordinate_distance h768 permutation cache keys covered
            (hybridMessage left right rest) positions observe budget hobs i hi
            (hybridMessage left right rest i) (right i)
          simpa only [Function.update_eq_self] using hchg
      refine ((measureTVDist_triangle _ _ _).trans (add_le_add ih hstep)).trans ?_
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      exact le_of_eq (by ring)
  have hall : hybridMessage left right (Finset.univ.toList : List Index) = right := by
    funext i; simp [hybridMessage]
  have hr := hgen (Finset.univ.toList : List Index)
  simpa only [hall, Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using hr

/-! ### 7. Final Statistical Hiding Arithmetic & Master Theorem -/

theorem moon_hiding_arithmetic (known budget : Nat) (hknown : known ≤ budget) :
    2 * (((2 * known + budget : Nat) : ℝ) / 2 ^ 128 +
         (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
    (LENGTH : ℝ) * (6 * ((known + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256) ≤
    ((budget : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS := by
  have hk : (known : ℝ) ≤ budget := Nat.cast_le.mpr hknown
  have hb : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have h1 : ((2 * known + budget : Nat) : ℝ) ≤ 3 * budget := by push_cast; linarith
  have h2 : ((known + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) ≤
      2 * budget + (HONEST_TREE_BUDGET + 3 : Nat) := by push_cast; linarith
  have hstep :
      2 * (((2 * known + budget : Nat) : ℝ) / 2 ^ 128 +
           (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
      (LENGTH : ℝ) * (6 * ((known + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256) ≤
      2 * ((3 * budget) / 2 ^ 128 + (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
      (LENGTH : ℝ) * (6 * (2 * budget + (HONEST_TREE_BUDGET + 3 : Nat)) / 2 ^ 256) := by
    gcongr
  refine hstep.trans ?_
  have hL : (LENGTH : ℝ) = (2 : ℝ) ^ 24 := by norm_num [LENGTH, LOG_LENGTH]
  have hLT_nat : LENGTH + HONEST_TREE_BUDGET ≤ 2 ^ 27 := by
    unfold HONEST_TREE_BUDGET LENGTH LOG_LENGTH; omega
  have hLT : ((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) ≤ (2 : ℝ) ^ 27 := by
    exact_mod_cast hLT_nat
  have hT3_nat : HONEST_TREE_BUDGET + 3 ≤ 2 ^ 27 := by
    unfold HONEST_TREE_BUDGET LENGTH LOG_LENGTH; omega
  have hT3 : ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) ≤ (2 : ℝ) ^ 27 := by
    exact_mod_cast hT3_nat
  have h2pos : ∀ n : Nat, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  have hp128 : (2 : ℝ) ^ 128 = 2 ^ 8 * 2 ^ 120 := by rw [← pow_add]
  have hp192 : (2 : ℝ) ^ 192 = 2 ^ 72 * 2 ^ 120 := by rw [← pow_add]
  have hp256 : (2 : ℝ) ^ 256 = 2 ^ 136 * 2 ^ 120 := by rw [← pow_add]
  have hA : 2 * ((3 * (budget : ℝ)) / 2 ^ 128) ≤ (1 / 2) * ((budget : ℝ) / 2 ^ 120) := by
    rw [hp128]
    have hcoeff : (6 : ℝ) / (2 : ℝ) ^ 8 ≤ 1 / 2 := by norm_num
    have hEq : 2 * ((3 * (budget : ℝ)) / ((2 : ℝ) ^ 8 * (2 : ℝ) ^ 120)) =
        ((6 : ℝ) / (2 : ℝ) ^ 8) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hB : 2 * ((((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) ≤
      (1 / 2) * (1 / (2 : ℝ) ^ 120) := by
    rw [Nat.cast_mul, hL, hp192]
    have hnum : 2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24) ≤ (2 : ℝ) ^ 52 := by
      have : (2 : ℝ) * ((2 : ℝ) ^ 27 * (2 : ℝ) ^ 24) = (2 : ℝ) ^ 52 := by
        rw [← pow_add, ← pow_succ']
      linarith [mul_le_mul_of_nonneg_right hLT (h2pos 24).le]
    have h52 : (2 : ℝ) ^ 52 / (2 : ℝ) ^ 72 ≤ 1 / 2 := by
      have : (2 : ℝ) ^ 72 = (2 : ℝ) ^ 52 * (2 : ℝ) ^ 20 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 52))]
      have h20 : (2 : ℝ) ≤ (2 : ℝ) ^ 20 := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 1 ≤ 20)
        simpa using this
      exact one_div_le_one_div_of_le (by norm_num) h20
    have hEq : 2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) =
        (2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 72) * (1 / (2 : ℝ) ^ 120) := by
      ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 72).le).trans h52) (by positivity)
  have hC : (LENGTH : ℝ) * (6 * (2 * (budget : ℝ)) / 2 ^ 256) ≤ (1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by
    rw [hL, hp256]
    have h12 : (12 : ℝ) * (2 : ℝ) ^ 24 ≤ (2 : ℝ) ^ 28 := by
      have : (16 : ℝ) * (2 : ℝ) ^ 24 = (2 : ℝ) ^ 28 := by
        have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        rw [h16, ← pow_add]
      linarith [h2pos 24]
    have h28 : (2 : ℝ) ^ 28 / (2 : ℝ) ^ 136 ≤ 1 / 2 := by
      have : (2 : ℝ) ^ 136 = (2 : ℝ) ^ 28 * (2 : ℝ) ^ 108 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 28))]
      have h108 : (2 : ℝ) ≤ (2 : ℝ) ^ 108 := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 1 ≤ 108)
        simpa using this
      exact one_div_le_one_div_of_le (by norm_num) h108
    have hEq : (2 : ℝ) ^ 24 * (6 * (2 * (budget : ℝ)) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) =
        (((12 : ℝ) * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 136) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by
      ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right h12 (h2pos 136).le).trans h28) (by positivity)
  have hD : (LENGTH : ℝ) * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / 2 ^ 256) ≤
      (1 / 2) * (1 / (2 : ℝ) ^ 120) := by
    rw [hL, hp256]
    have hnum : (2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ)) ≤ (2 : ℝ) ^ 54 := by
      have h8 : (2 : ℝ) ^ 24 * (8 * (2 : ℝ) ^ 27) = (2 : ℝ) ^ 54 := by
        have : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        rw [this, ← pow_add, ← pow_add]
      have h68 : (6 : ℝ) * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) ≤ 8 * (2 : ℝ) ^ 27 := by linarith [h2pos 27]
      exact (mul_le_mul_of_nonneg_left h68 (h2pos 24).le).trans h8.le
    have h54 : (2 : ℝ) ^ 54 / (2 : ℝ) ^ 136 ≤ 1 / 2 := by
      have : (2 : ℝ) ^ 136 = (2 : ℝ) ^ 54 * (2 : ℝ) ^ 82 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 54))]
      have h82 : (2 : ℝ) ≤ (2 : ℝ) ^ 82 := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 1 ≤ 82)
        simpa using this
      exact one_div_le_one_div_of_le (by norm_num) h82
    have hEq : (2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) =
        (((2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ))) / (2 : ℝ) ^ 136) * (1 / (2 : ℝ) ^ 120) := by
      ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 136).le).trans h54) (by positivity)
  have hRHS : ((budget : ℝ) + 1) / (2 : ℝ) ^ HIDING_SECURITY_BITS =
      ((1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120) + (1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120)) +
      ((1 / 2) * (1 / (2 : ℝ) ^ 120) + (1 / 2) * (1 / (2 : ℝ) ^ 120)) := by
    unfold HIDING_SECURITY_BITS; ring
  have hLHS :
      2 * ((3 * (budget : ℝ)) / 2 ^ 128 + (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
      (LENGTH : ℝ) * (6 * (2 * (budget : ℝ) + ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ)) / 2 ^ 256) =
      (2 * ((3 * (budget : ℝ)) / 2 ^ 128) + (LENGTH : ℝ) * (6 * (2 * (budget : ℝ)) / 2 ^ 256)) +
      (2 * ((((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
       (LENGTH : ℝ) * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / 2 ^ 256)) := by
    ring
  rw [hLHS, hRHS]
  linarith [hA, hB, hC, hD]

/-- Master Hiding Theorem: once `MoonCommitRef` + `MoonOpenRef` establish `HonestTranscriptRefines`,
the submitted RISC-V scheme satisfies the full two-stage adaptive `Hiding HIDING_ERROR` property. -/
theorem hiding_of_refines (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (href : HonestTranscriptRefines h768) :
    submission.scheme.Hiding HIDING_ERROR := by
  constructor
  · intro _ budget; unfold HIDING_ERROR; exact le_min (by norm_num) (by positivity)
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _)
    -- Move both sides to the staged lazy-ROM representation!
    let staged (perm : Perm) (sel : Bool) : ProbComp Output := do
      let (ch, cache) ← compressionRun perm adversary.choose ∅
      realObservation h768 perm cache (if sel then ch.message₁ else ch.message₀)
        ch.positions (adversary.observe ch.aux)
    have hstaged_eq : ∀ sel : Bool,
        𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary sel)] =
        𝒟[($ᵗ Perm) >>= fun perm => staged perm sel] := by
      intro sel
      have hexp : Hiding.hidingExperiment submission.scheme adversary sel = (do
          let ch ← adversary.choose
          let msg := if sel then ch.message₁ else ch.message₀
          let tr ← honestTranscript msg ch.positions
          adversary.observe ch.aux tr.1 tr.2) := by
        simp only [Hiding.hidingExperiment, honestTranscript, bind_assoc, pure_bind]
      let toCommit : Digest → Commitment := fun d => d
      let refComp : OracleComp World Output := do
        let ch ← adversary.choose
        let msg := if sel then ch.message₁ else ch.message₀
        let salts ← (liftM ($ᵗ (Index → Salt128)) : OracleComp World (Index → Salt128))
        let nodes ← queryTreeFromLeafFn h768 (fun i => queryLeafOpened h768 i (salts i) (msg i))
        adversary.observe ch.aux (toCommit (nodes 24 0)) (referenceProof nodes salts ch.positions)
      have href_run : ∀ o : Oracle,
          𝒟[fixedOracleRun o (Hiding.hidingExperiment submission.scheme adversary sel)] =
          𝒟[fixedOracleRun o refComp] := by
        intro o
        rw [hexp, fixed_oracle_run_bind]
        unfold refComp
        rw [fixed_oracle_run_bind]
        apply _root_.evalDist_bind_congr; intro ch
        rw [fixed_oracle_run_bind, href o, bind_assoc, fixed_oracle_run_bind, fixed_oracle_run_coins]
        simp only [pure_bind]
        let msg := if sel then ch.message₁ else ch.message₀
        trans 𝒟[($ᵗ (Index → Salt128)) >>= fun salts =>
          let tr := referenceTranscript h768 o.compression msg salts ch.positions
          fixedOracleRun o (adversary.observe ch.aux tr.1 tr.2)]
        · exact split_blocks_uniform_bind 128 LENGTH (by decide)
            (fun salts =>
              let tr := referenceTranscript h768 o.compression msg salts ch.positions
              fixedOracleRun o (adversary.observe ch.aux tr.1 tr.2))
        · apply _root_.evalDist_bind_congr; intro salts
          obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
            (fun i => queryLeafOpened h768 i (salts i) (msg i))
            (fun i => leafDigest (fun x => o.compression (x.cast h768.symm)) i (salts i) (msg i))
            (fun i => queryLeafOpened_fixed h768 o i (salts i) (msg i))
          rw [fixed_oracle_run_bind, hrun, pure_bind]
          have hrt : toCommit (nodes 24 0) = (referenceTranscript h768 o.compression msg salts ch.positions).1 :=
            hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
          have hpf : referenceProof nodes salts ch.positions =
              (referenceTranscript h768 o.compression msg salts ch.positions).2 :=
            referenceProof_congr_nodes _ _ hval salts ch.positions
          rw [hrt, hpf]
      unfold Hiding.runHiding
      have hfst : ∀ o : Oracle,
          (do let (out, _) ← o.run (Hiding.hidingExperiment submission.scheme adversary sel); pure out) =
          fixedOracleRun o (Hiding.hidingExperiment submission.scheme adversary sel) := by
        intro o; unfold fixedOracleRun; rw [map_eq_bind_pure_comp]; apply bind_congr; rintro ⟨a, b⟩; rfl
      simp only [hfst]
      trans 𝒟[Oracle.sample >>= fun o => fixedOracleRun o refComp]
      · exact _root_.evalDist_bind_congr _ _ _ href_run
      · simp only [Oracle.sample, bind_assoc, pure_bind]
        rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)]
        apply _root_.evalDist_bind_congr; intro perm
        unfold refComp
        rw [staged_compression_sampling]
        unfold staged realObservation
        apply _root_.evalDist_bind_congr; rintro ⟨ch, cache⟩
        apply _root_.evalDist_bind_congr; intro table
        rw [fixed_oracle_run_bind, fixed_oracle_run_coins]
        apply _root_.evalDist_bind_congr; intro salts
        let o : Oracle := ⟨tableExtending cache table, perm⟩
        let msg := if sel then ch.message₁ else ch.message₀
        obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 o
          (fun i => queryLeafOpened h768 i (salts i) (msg i))
          (fun i => leafDigest (fun x => o.compression (x.cast h768.symm)) i (salts i) (msg i))
          (fun i => queryLeafOpened_fixed h768 o i (salts i) (msg i))
        rw [fixed_oracle_run_bind, hrun, pure_bind]
        have hrt : toCommit (nodes 24 0) = (referenceTranscript h768 o.compression msg salts ch.positions).1 :=
          hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega)
        have hpf : referenceProof nodes salts ch.positions =
            (referenceTranscript h768 o.compression msg salts ch.positions).2 :=
          referenceProof_congr_nodes _ _ hval salts ch.positions
        rw [hrt, hpf]
    rw [measureTVDist, hstaged_eq false, hstaged_eq true, ← measureTVDist]
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Perm) _ _ (by positivity)
    intro perm
    unfold staged
    rw [bind_eq_attach_bind (compressionRun perm adversary.choose ∅)]
    rw [bind_eq_attach_bind (compressionRun perm adversary.choose ∅)]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    rintro ⟨⟨ch, cache⟩, hreach⟩
    obtain ⟨keys, hkeys_card, hcov⟩ := first_stage_cache_bound perm adversary.choose budget
      (hiding_choose_query_bound adversary bounded) (ch, cache) hreach
    have hobs_bd := staged_observe_query_bound perm adversary bounded (ch, cache) hreach
    have hagree : ∀ i ∈ ch.positions, ch.message₀ i = ch.message₁ i :=
      fun i hi => congrFun ch.agree ⟨i, hi⟩
    have hd0 := real_ideal0_distance h768 perm cache keys hcov ch.message₀ ch.positions
      (adversary.observe ch.aux) budget hobs_bd
    have hdm := ideal0_hybrid_distance h768 perm cache keys hcov ch.message₀ ch.message₁
      ch.positions hagree (adversary.observe ch.aux) budget hobs_bd
    have hd1 := real_ideal0_distance h768 perm cache keys hcov ch.message₁ ch.positions
      (adversary.observe ch.aux) budget hobs_bd
    rw [measureTVDist_comm] at hd1
    have htri := (measureTVDist_triangle _ _ _).trans (add_le_add hd0
      ((measureTVDist_triangle _ _ _).trans (add_le_add hdm hd1)))
    refine htri.trans ?_
    have hrearr :
        (((2 * keys.card + budget : Nat) : ℝ) / 2 ^ 128 +
          (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
        ((LENGTH : ℝ) * (6 * ((keys.card + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256) +
         (((2 * keys.card + budget : Nat) : ℝ) / 2 ^ 128 +
          (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192)) =
        2 * (((2 * keys.card + budget : Nat) : ℝ) / 2 ^ 128 +
          (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) +
        (LENGTH : ℝ) * (6 * ((keys.card + (HONEST_TREE_BUDGET + budget) + 3 : Nat) : ℝ) / 2 ^ 256) := by
      ring
    rw [hrearr]
    exact moon_hiding_arithmetic keys.card budget hkeys_card

end CommitGolfCandidate
