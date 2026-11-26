import CommitGolfCandidate.MoonHidingCore

/-! Complete airtight 121-bit early-tagged statistical hiding proof for B1-Ultra-121
(`r = 0, c = 8`, uniform `238`-bit masking on `L0..L23`, `121`-bit independent salts).
Key ingredients avoiding any `2×` loss on the 121-bit salt bound:
  1. Exact combined Stage-1/Stage-2 query budget (`keys.card ≤ q1`, `observe` budget `= budget - q1`).
  2. Sampling `sHidden` BEFORE Stage 1 (`allPrefixes`) bounds Stage-1 cache value collisions at
     `budget * 2^24 / 2^192` instead of `q1 / 2^121`.
  3. One-sided identical-until-bad (`measureTVDist_one_sided_with_slack`) with msg-independent
     `marksPrefix` and `flagComp` gives:
       `TV(Real₀, Real₁) ≤ budget / 2^121 + 2*(budget + 2^24 + H)*2^24 / 2^192 + 6*2^24*(budget + H + 3) / 2^256`
       `                  ≤ (budget + 1) / 2^120`
     for EVERY query budget `budget` and EVERY opening size `0 ≤ k ≤ 2^24`. -/
namespace CommitGolfCandidate

local instance moonHidingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
local instance moonHidingDiscrete {α : Type} : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
local instance moonHidingProdBoolDiscrete {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (α × Bool) :=
  ⟨fun s => by
    have h : s = ({a | (a, false) ∈ s} ×ˢ ({false} : Set Bool)) ∪
                 ({a | (a, true) ∈ s} ×ˢ ({true} : Set Bool)) := by
      ext ⟨a, b⟩; cases b <;> simp
    rw [h]
    exact (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete).union
      (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete)⟩
local instance moonHidingProdUnitBoolDiscrete {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (α × Unit × Bool) :=
  ⟨fun s => by
    have h : s = ({a | (a, (), false) ∈ s} ×ˢ ({((), false)} : Set (Unit × Bool))) ∪
                 ({a | (a, (), true) ∈ s} ×ˢ ({((), true)} : Set (Unit × Bool))) := by
      ext ⟨a, ⟨⟨⟩, b⟩⟩; cases b <;> simp
    rw [h]
    exact (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete).union
      (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete)⟩
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling
open MeasureTheory
open scoped ENNReal

/-! ### 1. Exact Machine-to-Reference Interface -/

def honestTranscript (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← submission.scheme.commit message
  let proof ← submission.scheme.opening trapdoor positions
  return (root, proof)

def referenceTranscript (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (message : Message) (salts : Index → Salt121) (positions : Positions) : Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  (rootVal c message salts, referenceProof (nodeVal c message salts) salts positions)

/-- Machine refinement contract proved by `MoonCommitRef` + `MoonOpenRef` + `MoonCertificate`. -/
def HonestTranscriptRefines (h768 : COMPRESSION_INPUT_LENGTH = 768) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    EvalDistEq (fixedOracleRun oracle (honestTranscript message positions))
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        pure (referenceTranscript h768 oracle.compression message (splitSalts121 packed) positions))

/-! ### 2. Ideal-0 Game (Fresh Uniform 256-bit `cv0` on Unopened Leaves) -/

def ideal0Leaves (c : Comp96) (msg : Message) (sOpen : Index → Salt121) (cv0 : Index → Digest)
    (positions : Positions) (i : Index) : Digest :=
  if i ∈ positions then leafDigest c i (sOpen i) (msg i)
  else leafChainFromCv0 c (cv0 i) (msg i)

def ideal0Transcript (h768 : COMPRESSION_INPUT_LENGTH = 768) (compress : Compression)
    (msg : Message) (sOpen : Index → Salt121) (cv0 : Index → Digest) (positions : Positions) :
    Commitment × Proof :=
  let c : Comp96 := fun x => compress (x.cast h768.symm)
  let nodes := nodeValFromLeaves c (ideal0Leaves c msg sOpen cv0 positions)
  (nodes 24 0, referenceProof nodes sOpen positions)

theorem ideal0Transcript_eq_reference_of_cv0 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (compress : Compression) (msg : Message) (sOpen sHidden : Index → Salt121) (positions : Positions) :
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
  exact Prod.ext rfl (referenceProof_congr_opened _ sOpen (saltsMerge positions sOpen sHidden) positions
    (fun i hi => by simp [saltsMerge, hi]))

/-! ### 3. Simultaneous Reprogramming on All Hidden Call-0 Inputs -/

def hiddenCall0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message)
    (sHidden : Index → Salt121) (i : Index) : BitVec COMPRESSION_INPUT_LENGTH :=
  (leafCall0Input i (sHidden i) (msg i)).cast h768.symm

theorem hiddenCall0_injective (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message)
    (sHidden : Index → Salt121) : Function.Injective (hiddenCall0 h768 msg sHidden) := by
  intro a b h
  have hcast : leafCall0Input a (sHidden a) (msg a) = leafCall0Input b (sHidden b) (msg b) := by
    simpa [hiddenCall0] using congrArg (BitVec.cast h768) h
  have htag := congrArg (fun v : BitVec 768 => v.extractLsb' 128 64) hcast
  simp only [leafCall0Input_tag] at htag
  exact leafTag_injective htag

private def toOut (d : Digest) : BitVec COMPRESSION_OUTPUT_LENGTH := d
private def fromOut (d : BitVec COMPRESSION_OUTPUT_LENGTH) : Digest := d

noncomputable def reprogramFinset (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt121)
    (cv0 : Index → Digest) (S : Finset Index) : Compression :=
  fun x =>
    if h : ∃ i ∈ S, hiddenCall0 h768 msg sHidden i = x then
      toOut (cv0 (Classical.choose h))
    else table x

theorem reprogramFinset_mem (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt121)
    (cv0 : Index → Digest) (S : Finset Index) (i : Index) (hi : i ∈ S) :
    reprogramFinset h768 table msg sHidden cv0 S (hiddenCall0 h768 msg sHidden i) = toOut (cv0 i) := by
  unfold reprogramFinset
  split_ifs with h
  · rw [hiddenCall0_injective h768 msg sHidden (Classical.choose_spec h).2]
  · exact (h ⟨i, hi, rfl⟩).elim

theorem reprogramFinset_not_mem (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt121)
    (cv0 : Index → Digest) (S : Finset Index) (x : BitVec COMPRESSION_INPUT_LENGTH)
    (hnot : ∀ i ∈ S, hiddenCall0 h768 msg sHidden i ≠ x) :
    reprogramFinset h768 table msg sHidden cv0 S x = table x := by
  unfold reprogramFinset
  split_ifs with h
  · obtain ⟨i, hi, heq⟩ := h
    exact (hnot i hi heq).elim
  · rfl

theorem reprogramFinset_insert (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (table : Compression) (msg : Message) (sHidden : Index → Salt121)
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

theorem reprogramFinset_dist (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (msg : Message) (sHidden : Index → Salt121) (S : Finset Index) {α : Type}
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

/-! ### 4. 121-Bit Tagged Salt Prefix Sets and Hit Bounds (`1 / 2^121` per Query) -/

def allPrefixes (sHidden : Index → Salt121) : Finset (BitVec 192) :=
  Finset.univ.image (fun i => leafCall0Prefix i (sHidden i))

def hiddenPrefixes (positions : Positions) (sHidden : Index → Salt121) : Finset (BitVec 192) :=
  (Finset.univ \ positions).image (fun i => leafCall0Prefix i (sHidden i))

theorem allPrefixes_card_le (sHidden : Index → Salt121) :
    (allPrefixes sHidden).card ≤ LENGTH := by
  calc
    (allPrefixes sHidden).card ≤ (Finset.univ : Finset Index).card := Finset.card_image_le
    _ = LENGTH := by rw [Finset.card_univ]; exact Fintype.card_fin LENGTH

theorem hiddenPrefixes_subset_allPrefixes (positions : Positions) (sHidden : Index → Salt121) :
    hiddenPrefixes positions sHidden ⊆ allPrefixes sHidden :=
  Finset.image_subset_image Finset.sdiff_subset

theorem hiddenPrefixes_card_le (positions : Positions) (sHidden : Index → Salt121) :
    (hiddenPrefixes positions sHidden).card ≤ LENGTH :=
  (Finset.card_le_card (hiddenPrefixes_subset_allPrefixes positions sHidden)).trans (allPrefixes_card_le sHidden)

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

/-- Because `leafTag` is injective, any fixed 192-bit target `v` matches at most ONE hidden index
`i0 ∉ positions`, so `Pr_{sHidden}[v ∈ hiddenPrefixes] ≤ 1 / 2^121`! -/
theorem single_prefix_hit_121 (positions : Positions) (v : BitVec 192) :
    (prEvent ((fun sHidden : Index → Salt121 => v ∈ hiddenPrefixes positions sHidden) <$>
      ($ᵗ (Index → Salt121)))) ≤ (1 : ENNReal) / 2 ^ 121 := by
  by_cases hex : ∃ i ∈ Finset.univ \ positions, leafTag i = v.extractLsb' 128 64
  · obtain ⟨i0, hi0, htag0⟩ := hex
    have himp : ∀ sHidden : Index → Salt121,
        v ∈ hiddenPrefixes positions sHidden → sHidden i0 = v.extractLsb' 0 121 := by
      intro sHidden hmem
      obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hmem
      have hjtag : leafTag j = v.extractLsb' 128 64 := by
        rw [← hjv]; exact (leafCall0Prefix_tag j (sHidden j)).symm
      have hji : j = i0 := leafTag_injective (hjtag.trans htag0.symm)
      subst hji
      rw [← hjv]; exact (leafCall0Prefix_salt j (sHidden j)).symm
    have hle : (prEvent ((fun sHidden : Index → Salt121 => v ∈ hiddenPrefixes positions sHidden) <$>
        ($ᵗ (Index → Salt121)))) ≤
        (prEvent ((fun sHidden : Index → Salt121 => sHidden i0 = v.extractLsb' 0 121) <$>
          ($ᵗ (Index → Salt121)))) :=
      prEvent_mono_of_support _ _ _ (fun s _ h => himp s h)
    refine hle.trans (prEvent_uniform_coord_le (D := Index) (R := Salt121) i0
      (fun fresh => fresh = v.extractLsb' 0 121) ?_)
    rw [prEvent_uniform_eq_target, Fintype.card_bitVec 121]
    simp only [Nat.cast_pow, Nat.cast_ofNat, le_refl]
  · have hzero : (prEvent ((fun sHidden : Index → Salt121 => v ∈ hiddenPrefixes positions sHidden) <$>
        ($ᵗ (Index → Salt121)))) = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro s _ hmem
      obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hmem
      apply hex
      exact ⟨j, hj, by rw [← hjv]; exact (leafCall0Prefix_tag j (s j)).symm⟩
    rw [hzero]; exact zero_le

theorem list_prefix_hit_121 (positions : Positions) (vs : List (BitVec 192)) :
    (prEvent ((fun sHidden : Index → Salt121 => ∃ v ∈ vs, v ∈ hiddenPrefixes positions sHidden) <$>
      ($ᵗ (Index → Salt121)))) ≤ (vs.length : ENNReal) / 2 ^ 121 := by
  induction vs with
  | nil =>
    have hz : (prEvent ((fun s : Index → Salt121 => ∃ v ∈ ([] : List (BitVec 192)), v ∈ hiddenPrefixes positions s) <$>
        ($ᵗ (Index → Salt121)))) = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ ⟨_, hv, _⟩ => List.not_mem_nil hv)
    rw [hz]; exact zero_le
  | cons v rest ih =>
    have hunion : (prEvent ((fun s => ∃ u ∈ v :: rest, u ∈ hiddenPrefixes positions s) <$> ($ᵗ (Index → Salt121)))) ≤
        (prEvent ((fun s => v ∈ hiddenPrefixes positions s) <$> ($ᵗ (Index → Salt121)))) +
        (prEvent ((fun s => ∃ u ∈ rest, u ∈ hiddenPrefixes positions s) <$> ($ᵗ (Index → Salt121)))) := by
      have hle := prEvent_or_le ($ᵗ (Index → Salt121))
        (fun s => v ∈ hiddenPrefixes positions s)
        (fun s => ∃ u ∈ rest, u ∈ hiddenPrefixes positions s)
      refine (prEvent_mono_of_support _ _ _ ?_).trans hle
      intro s _ ⟨u, hu, hmem⟩
      rcases List.mem_cons.mp hu with rfl | hrest
      · exact Or.inl hmem
      · exact Or.inr ⟨u, hrest, hmem⟩
    refine (hunion.trans (add_le_add (single_prefix_hit_121 positions v) ih)).trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ENNReal.add_div]
    rw [add_comm]

/-- Message-independent cache-key hit predicate! -/
def cacheKeysHitPrefix (cache : CompressionCache) (positions : Positions)
    (sHidden : Index → Salt121) : Prop :=
  ∃ k, cache k ≠ none ∧ k.extractLsb' 0 192 ∈ hiddenPrefixes positions sHidden

theorem cache_keys_hit_prefix_121 (positions : Positions) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys) :
    (prEvent ((fun sHidden : Index → Salt121 => cacheKeysHitPrefix cache positions sHidden) <$>
      ($ᵗ (Index → Salt121)))) ≤ (keys.card : ENNReal) / 2 ^ 121 := by
  have hle : (prEvent ((fun sHidden => cacheKeysHitPrefix cache positions sHidden) <$> ($ᵗ (Index → Salt121)))) ≤
      (prEvent ((fun sHidden => ∃ v ∈ keys.toList.map (fun k => k.extractLsb' 0 192),
        v ∈ hiddenPrefixes positions sHidden) <$> ($ᵗ (Index → Salt121)))) := by
    apply prEvent_mono_of_support
    intro sHidden _ ⟨k, hne, hmem⟩
    exact ⟨k.extractLsb' 0 192, List.mem_map.mpr ⟨k, Finset.mem_toList.mpr (covered k hne), rfl⟩, hmem⟩
  exact hle.trans (by simpa only [List.length_map, Finset.length_toList] using
    list_prefix_hit_121 positions (keys.toList.map (fun k => k.extractLsb' 0 192)))

/-- Message-independent query marking predicate: marks any compression query whose low 192 bits
match a hidden `(leafTag i, sHidden i)` prefix. -/
def marksPrefix (positions : Positions) (sHidden : Index → Salt121) : World.Domain → Bool
  | .inr (.inl x) => decide (x.extractLsb' 0 192 ∈ hiddenPrefixes positions sHidden)
  | _ => false

theorem flaggedRun_marksPrefix_trace {α : Type} (o : Oracle) (positions : Positions)
    (sH : Index → Salt121) (comp : OracleComp World α) (f : Bool) :
    flaggedRun o (marksPrefix positions sH) comp f =
      (fun r : α × List (BitVec COMPRESSION_INPUT_LENGTH) =>
        (r.1, (), f || r.2.any (fun x => decide (x.extractLsb' 0 192 ∈ hiddenPrefixes positions sH)))) <$>
        fixedOracleRun o (traceCompression comp) := by
  induction comp using OracleComp.inductionOn generalizing f with
  | pure v =>
    simp only [flaggedRun, simulateQ_pure, StateT.run_pure, trace_compression_pure,
      fixed_oracle_run_pure, map_pure, List.any_nil, Bool.or_false]
  | query_bind q k ih =>
    rw [flagged_run_query_bind, trace_run_query_bind, map_bind]
    apply bind_congr; intro ans; rw [ih]; simp only [bind_pure_comp, Functor.map_map]
    apply congrArg (fun g => g <$> fixedOracleRun o (traceCompression (k ans)))
    funext r
    have hhd : (compressionHead q).any (fun x => decide (x.extractLsb' 0 192 ∈ hiddenPrefixes positions sH)) =
        marksPrefix positions sH q := by
      rcases q with _ | pq
      · rfl
      · rcases pq with x | permq
        · change (decide (x.extractLsb' 0 192 ∈ hiddenPrefixes positions sH) || false) = _
          exact Bool.or_false _
        · rcases permq <;> rfl
    simp only [List.any_append, hhd, Bool.or_assoc]

/-! ### 5. Conditional One-Sided Coupling for Fixed `(sHidden, cache, msg, positions)` -/

def realCondObs (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions) (sHidden : Index → Salt121)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let sOpen ← $ᵗ (Index → Salt121)
  let table ← $ᵗ Compression
  let salts := saltsMerge positions sOpen sHidden
  let tr := referenceTranscript h768 (tableExtending cache table) msg salts positions
  fixedOracleRun ⟨tableExtending cache table, permutation⟩ (observe tr.1 tr.2)

open Classical in
noncomputable def cacheKeysHitBool (cache : CompressionCache) (positions : Positions)
    (sHidden : Index → Salt121) : Bool :=
  decide (cacheKeysHitPrefix cache positions sHidden)

theorem cacheKeysHitBool_pos {cache : CompressionCache} {positions : Positions} {sHidden : Index → Salt121}
    (h : cacheKeysHitPrefix cache positions sHidden) :
    cacheKeysHitBool cache positions sHidden = true := by
  classical
  unfold cacheKeysHitBool
  exact decide_eq_true h

theorem cacheKeysHitBool_neg {cache : CompressionCache} {positions : Positions} {sHidden : Index → Salt121}
    (h : ¬ cacheKeysHitPrefix cache positions sHidden) :
    cacheKeysHitBool cache positions sHidden = false := by
  classical
  unfold cacheKeysHitBool
  exact decide_eq_false h

noncomputable def flagCondObs (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions) (sHidden : Index → Salt121)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) : ProbComp (α × Bool) := do
  let sOpen ← $ᵗ (Index → Salt121)
  let cv0 ← $ᵗ (Index → Digest)
  let table ← $ᵗ Compression
  let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
  let r ← flaggedRun ⟨tableExtending cache table, permutation⟩ (marksPrefix positions sHidden) (observe tr.1 tr.2)
  pure (r.1, cacheKeysHitBool cache positions sHidden || r.2.2)

def treeHitCond (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions) (sHidden : Index → Salt121) :
    ProbComp ((Nat → Nat → Digest) × Unit × Bool) := do
  let sOpen ← $ᵗ (Index → Salt121)
  let cv0 ← $ᵗ (Index → Digest)
  let table ← $ᵗ Compression
  flaggedRun ⟨tableExtending cache table, permutation⟩ (marksPrefix positions sHidden)
    (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))

private theorem cond_one_sided_pointwise (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions) (sHidden : Index → Salt121)
    (hkey : ¬ cacheKeysHitPrefix cache positions sHidden)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (p : α → Prop)
    (sOpen : Index → Salt121) (cv0 : Index → Digest) (table : Compression) :
    let H : Finset Index := Finset.univ \ positions
    let tbl := tableExtending cache table
    let tbl' := tableExtending cache (reprogramFinset h768 table msg sHidden cv0 H)
    let tr := ideal0Transcript h768 tbl msg sOpen cv0 positions
    let tr' := ideal0Transcript h768 tbl' msg sOpen cv0 positions
    let flagObs := (flaggedRun ⟨tbl, permutation⟩ (marksPrefix positions sHidden) (observe tr.1 tr.2)) >>=
      fun r => pure (r.1, cacheKeysHitBool cache positions sHidden || r.2.2)
    let treeRun := flaggedRun ⟨tbl, permutation⟩ (marksPrefix positions sHidden)
      (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))
    Pr{let z ← flagObs}[p z.1 ∧ z.2 = false] ≤
      Pr{let x ← fixedOracleRun ⟨tbl', permutation⟩ (observe tr'.1 tr'.2)}[p x] +
      Pr{let t ← treeRun}[t.2.2 = true] ∧
    Pr{let x ← fixedOracleRun ⟨tbl', permutation⟩ (observe tr'.1 tr'.2)}[p x] ≤
      Pr{let z ← flagObs}[p z.1 ∧ z.2 = false] +
      Pr{let z ← flagObs}[z.2 = true] +
      Pr{let t ← treeRun}[t.2.2 = true] := by
  classical
  dsimp only
  let H : Finset Index := Finset.univ \ positions
  let tbl := tableExtending cache table
  let tbl' := tableExtending cache (reprogramFinset h768 table msg sHidden cv0 H)
  let o : Oracle := ⟨tbl, permutation⟩
  let o' : Oracle := ⟨tbl', permutation⟩
  let m := marksPrefix positions sHidden
  let treeComp := queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)
  let fullComp : OracleComp World α := do
    let nodes ← treeComp
    observe (nodes 24 0) (referenceProof nodes sOpen positions)
  have htree_det : ∀ (orac : Oracle), ∃ nodes,
      fixedOracleRun orac treeComp = pure nodes ∧
      (nodes 24 0, referenceProof nodes sOpen positions) =
        ideal0Transcript h768 orac.compression msg sOpen cv0 positions := by
    intro orac
    obtain ⟨nodes, hrun, hval⟩ := queryTreeFromLeafFn_fixed h768 orac
      (ideal0LeafFn h768 msg sOpen cv0 positions)
      (ideal0Leaves (fun x => orac.compression (x.cast h768.symm)) msg sOpen cv0 positions)
      (fun i => by
        unfold ideal0LeafFn ideal0Leaves
        by_cases hi : i ∈ positions
        · simp only [hi, ite_true]; exact queryLeafOpened_fixed h768 orac i (sOpen i) (msg i)
        · simp only [hi, ite_false]; exact queryLeafFromCv0_fixed h768 orac (cv0 i) (msg i))
    refine ⟨nodes, hrun, Prod.ext (hval 24 (le_refl _) 0 (by rw [levelSize_24]; omega))
      (referenceProof_congr_nodes _ _ hval sOpen positions)⟩
  have hfull_fixed : ∀ (orac : Oracle),
      fixedOracleRun orac fullComp =
        let tr := ideal0Transcript h768 orac.compression msg sOpen cv0 positions
        fixedOracleRun orac (observe tr.1 tr.2) := by
    intro orac
    obtain ⟨nodes, hrun, htr⟩ := htree_det orac
    unfold fullComp
    rw [fixed_oracle_run_bind, hrun, pure_bind]
    have h1 : nodes 24 0 = (ideal0Transcript h768 orac.compression msg sOpen cv0 positions).1 :=
      congrArg Prod.fst htr
    have h2 : referenceProof nodes sOpen positions =
        (ideal0Transcript h768 orac.compression msg sOpen cv0 positions).2 :=
      congrArg Prod.snd htr
    rw [h1, h2]
  have hagree : ∀ query, m query = false → o.world query = o'.world query := by
    intro query hunm
    rcases query with coins | pq
    · simp only [Oracle.world, QueryImpl.add_apply_inl]
    · rcases pq with x | permq
      · simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_inj]
        have hnot : ∀ i ∈ H, hiddenCall0 h768 msg sHidden i ≠ x := by
          intro i hi heq
          subst x
          simp only [m, marksPrefix, decide_eq_false_iff_not] at hunm
          apply hunm
          unfold hiddenCall0 hiddenPrefixes
          rw [extractLsb'_cast_eq, leafCall0Input_prefix]
          exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
        change (cache x).getD (table x) = (cache x).getD (reprogramFinset h768 table msg sHidden cv0 H x)
        rw [reprogramFinset_not_mem h768 table msg sHidden cv0 H x hnot]
      · rcases permq with x | x <;> simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, o, o']
  obtain ⟨h1s_lo, h1s_hi⟩ := oracle_change_one_sided o o' m hagree fullComp p
  rw [hfull_fixed o'] at h1s_lo h1s_hi
  have hflagObs_good :
      Pr{let z ← (flaggedRun o m (observe (ideal0Transcript h768 tbl msg sOpen cv0 positions).1
          (ideal0Transcript h768 tbl msg sOpen cv0 positions).2)) >>=
          fun r => pure (r.1, cacheKeysHitBool cache positions sHidden || r.2.2)}[p z.1 ∧ z.2 = false] =
      Pr{let r ← flaggedRun o m (observe (ideal0Transcript h768 tbl msg sOpen cv0 positions).1
          (ideal0Transcript h768 tbl msg sOpen cv0 positions).2)}[p r.1 ∧ r.2.2 = false] := by
    simp only [cacheKeysHitBool_neg hkey, Bool.false_or, bind_pure_comp, prEvent_map]
  have hflagObs_bad :
      Pr{let z ← (flaggedRun o m (observe (ideal0Transcript h768 tbl msg sOpen cv0 positions).1
          (ideal0Transcript h768 tbl msg sOpen cv0 positions).2)) >>=
          fun r => pure (r.1, cacheKeysHitBool cache positions sHidden || r.2.2)}[z.2 = true] =
      Pr{let r ← flaggedRun o m (observe (ideal0Transcript h768 tbl msg sOpen cv0 positions).1
          (ideal0Transcript h768 tbl msg sOpen cv0 positions).2)}[r.2.2 = true] := by
    simp only [cacheKeysHitBool_neg hkey, Bool.false_or, bind_pure_comp, prEvent_map]
  rw [hflagObs_good, hflagObs_bad]
  have hbind_flag :
      flaggedRun o m fullComp false = (do
        let r1 ← flaggedRun o m treeComp false
        flaggedRun o m (observe (r1.1 24 0) (referenceProof r1.1 sOpen positions)) r1.2.2) := by
    simp [fullComp, flaggedRun, simulateQ_bind, StateT.run_bind]
  obtain ⟨nodes0, htree_run0, htree_tr0⟩ := htree_det o
  let obs := observe (ideal0Transcript h768 tbl msg sOpen cv0 positions).1
    (ideal0Transcript h768 tbl msg sOpen cv0 positions).2
  have hsup_nodes : ∀ r1 ∈ support (flaggedRun o m treeComp false),
      observe (r1.1 24 0) (referenceProof r1.1 sOpen positions) = obs := by
    intro r1 hr1
    have hproj : r1.1 ∈ support (Prod.fst <$> flaggedRun o m treeComp false) := by
      rw [support_map]; exact ⟨r1, hr1, rfl⟩
    rw [flagged_run_projection, htree_run0, support_pure, Set.mem_singleton_iff] at hproj
    have h1 : r1.1 24 0 = (ideal0Transcript h768 tbl msg sOpen cv0 positions).1 := by
      rw [hproj]; exact congrArg Prod.fst htree_tr0
    have h2 : referenceProof r1.1 sOpen positions =
        (ideal0Transcript h768 tbl msg sOpen cv0 positions).2 := by
      rw [hproj]; exact congrArg Prod.snd htree_tr0
    simp only [obs, h1, h2]
  have hfull_good_eq :
      Pr{let r ← flaggedRun o m fullComp false}[p r.1 ∧ r.2.2 = false] =
        Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = false] *
        Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] := by
    rw [hbind_flag, prEvent_bind_eq_tsum]
    have hterm : ∀ r1,
        Pr{let z ← flaggedRun o m treeComp false}[z = r1] *
          Pr{let r ← flaggedRun o m (observe (r1.1 24 0) (referenceProof r1.1 sOpen positions)) r1.2.2}[p r.1 ∧ r.2.2 = false] =
        (if r1.2.2 = false then Pr{let z ← flaggedRun o m treeComp false}[z = r1] else 0) *
          Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] := by
      intro r1
      by_cases hmem : r1 ∈ support (flaggedRun o m treeComp false)
      · rw [hsup_nodes r1 hmem]
        cases htf : r1.2.2
        · simp
        · simp only [Bool.true_eq_false, ite_false, zero_mul]
          have hz : Pr{let r ← flaggedRun o m obs true}[p r.1 ∧ r.2.2 = false] = 0 := by
            apply prEvent_eq_zero_of_forall_mem_support
            intro r2 hr2 hbad2
            have htr : r2.2.2 = true := by
              have hft := flaggedRun_marksPrefix_trace o positions sHidden obs true
              rw [hft, support_map] at hr2
              obtain ⟨tr, _, rfl⟩ := hr2
              simp
            rw [htr] at hbad2
            cases hbad2.2
          rw [hz, mul_zero]
      · have hz : Pr{let z ← flaggedRun o m treeComp false}[z = r1] = 0 :=
          prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz hzeq => hmem (hzeq ▸ hz))
        simp [hz]
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right]
    exact congrArg (· * Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false])
      (OracleComp.prEvent_eq_tsum_ite (flaggedRun o m treeComp false) (fun t => t.2.2 = false)).symm
  have hfull_good_le :
      Pr{let r ← flaggedRun o m fullComp false}[p r.1 ∧ r.2.2 = false] ≤
        Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] := by
    rw [hfull_good_eq]
    calc
      Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = false] *
          Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false]
        ≤ 1 * Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] :=
          mul_le_mul_of_nonneg_right (prEvent_le_one _) zero_le
      _ = Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] := one_mul _
  have hobs_good_le :
      Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] ≤
        Pr{let r ← flaggedRun o m fullComp false}[p r.1 ∧ r.2.2 = false] +
        Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] := by
    rw [hfull_good_eq]
    have hpart : Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = false] +
        Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] = 1 := by
      have h := prEvent_add_prEvent_not_eq_prEvent_true (flaggedRun o m treeComp false)
        (fun t => t.2.2 = true)
      rw [OracleComp.prEvent_true_eq_one] at h
      simpa only [Bool.not_eq_true, add_comm] using h
    calc
      Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false]
        = (Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = false] +
           Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true]) *
          Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] := by
          rw [hpart, one_mul]
      _ = Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = false] *
            Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] +
          Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] *
            Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] := add_mul _ _ _
      _ ≤ Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = false] *
            Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] +
          Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] := by
          refine add_le_add le_rfl ?_
          calc
            Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] *
                Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false]
              ≤ Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] * 1 :=
                mul_le_mul_of_nonneg_left (prEvent_le_one _) zero_le
            _ = Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] := mul_one _
  have hfull_bad_le :
      Pr{let r ← flaggedRun o m fullComp false}[r.2.2 = true] ≤
        Pr{let r ← flaggedRun o m obs false}[r.2.2 = true] +
        Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] := by
    rw [hbind_flag, add_comm]
    exact prEvent_bind_le_prEvent_add_of_support
      (flaggedRun o m treeComp false)
      (fun r1 => flaggedRun o m (observe (r1.1 24 0) (referenceProof r1.1 sOpen positions)) r1.2.2)
      (fun r1 => r1.2.2 = true) (fun r2 => r2.2.2 = true)
      (fun r1 hr1 hnot => by
        have hfalse : r1.2.2 = false := Bool.eq_false_iff.mpr hnot
        rw [hfalse, hsup_nodes r1 hr1])
  constructor
  · exact hobs_good_le.trans (add_le_add h1s_lo le_rfl)
  · calc
      Pr{let x ← fixedOracleRun o' (observe (ideal0Transcript h768 tbl' msg sOpen cv0 positions).1
          (ideal0Transcript h768 tbl' msg sOpen cv0 positions).2)}[p x]
        ≤ Pr{let r ← flaggedRun o m fullComp false}[p r.1 ∧ r.2.2 = false] +
          Pr{let r ← flaggedRun o m fullComp false}[r.2.2 = true] := h1s_hi
      _ ≤ Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] +
          (Pr{let r ← flaggedRun o m obs false}[r.2.2 = true] +
           Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true]) :=
          add_le_add hfull_good_le hfull_bad_le
      _ = Pr{let r ← flaggedRun o m obs false}[p r.1 ∧ r.2.2 = false] +
          Pr{let r ← flaggedRun o m obs false}[r.2.2 = true] +
          Pr{let t ← flaggedRun o m treeComp false}[t.2.2 = true] := (add_assoc _ _ _).symm

set_option linter.constructorNameAsVariable false in
/-- Pointwise one-sided identical-until-bad inequalities for fixed `(sHidden, cache, msg, positions)`. -/
theorem cond_one_sided_bounds (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions) (sHidden : Index → Salt121)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (p : α → Prop) :
    Pr{let z ← flagCondObs h768 permutation cache msg positions sHidden observe}[p z.1 ∧ z.2 = false] ≤
      Pr{let x ← realCondObs h768 permutation cache msg positions sHidden observe}[p x] +
      Pr{let t ← treeHitCond h768 permutation cache msg positions sHidden}[t.2.2 = true] ∧
    Pr{let x ← realCondObs h768 permutation cache msg positions sHidden observe}[p x] ≤
      Pr{let z ← flagCondObs h768 permutation cache msg positions sHidden observe}[p z.1 ∧ z.2 = false] +
      Pr{let z ← flagCondObs h768 permutation cache msg positions sHidden observe}[z.2 = true] +
      Pr{let t ← treeHitCond h768 permutation cache msg positions sHidden}[t.2.2 = true] := by
  classical
  by_cases hkey : cacheKeysHitPrefix cache positions sHidden
  · have hzero : Pr{let z ← flagCondObs h768 permutation cache msg positions sHidden observe}[p z.1 ∧ z.2 = false] = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro z hz hcond
      unfold flagCondObs at hz
      simp only [cacheKeysHitBool_pos hkey, Bool.true_or, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hz
      cases hcond.2
    have hone : Pr{let z ← flagCondObs h768 permutation cache msg positions sHidden observe}[z.2 = true] = 1 := by
      rw [← OracleComp.prEvent_true_eq_one (flagCondObs h768 permutation cache msg positions sHidden observe)]
      apply le_antisymm (prEvent_mono _ _ _ fun _ _ => trivial)
      apply prEvent_mono_of_support
      intro z hz _
      unfold flagCondObs at hz
      simp only [cacheKeysHitBool_pos hkey, Bool.true_or, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hz
      rfl
    rw [hzero, hone, zero_add]
    exact ⟨zero_le, (prEvent_le_one _).trans le_self_add⟩
  · -- When `¬ cacheKeysHitPrefix`, reprogram ALL hidden Call-0 inputs via `reprogramFinset_dist`!
    let H : Finset Index := Finset.univ \ positions
    let progCond : ProbComp α := do
      let sOpen ← $ᵗ (Index → Salt121)
      let cv0 ← $ᵗ (Index → Digest)
      let table ← $ᵗ Compression
      let tbl' := tableExtending cache (reprogramFinset h768 table msg sHidden cv0 H)
      let tr := ideal0Transcript h768 tbl' msg sOpen cv0 positions
      fixedOracleRun ⟨tbl', permutation⟩ (observe tr.1 tr.2)
    have hRealProg : 𝒟[realCondObs h768 permutation cache msg positions sHidden observe] = 𝒟[progCond] := by
      unfold realCondObs progCond
      apply _root_.evalDist_bind_congr; intro sOpen
      rw [reprogramFinset_dist h768 msg sHidden H
        (fun tbl cv =>
          let t := tableExtending cache tbl
          let tr := ideal0Transcript h768 t msg sOpen cv positions
          fixedOracleRun ⟨t, permutation⟩ (observe tr.1 tr.2))]
      rw [← OracleComp.evalDist_bind_const ($ᵗ (Index → Digest)) _]
      apply _root_.evalDist_bind_congr; intro cv0
      apply _root_.evalDist_bind_congr; intro table
      have htr : referenceTranscript h768 (tableExtending cache table) msg (saltsMerge positions sOpen sHidden) positions =
          ideal0Transcript h768 (tableExtending cache table) msg sOpen
            (fun i => if i ∈ H then table (hiddenCall0 h768 msg sHidden i) else cv0 i) positions := by
        rw [← ideal0Transcript_eq_reference_of_cv0 h768 (tableExtending cache table) msg sOpen sHidden positions]
        unfold ideal0Transcript
        have hlv : ideal0Leaves (fun x => tableExtending cache table (x.cast h768.symm)) msg sOpen
            (fun i => tableExtending cache table (hiddenCall0 h768 msg sHidden i)) positions =
            ideal0Leaves (fun x => tableExtending cache table (x.cast h768.symm)) msg sOpen
            (fun i => if i ∈ H then table (hiddenCall0 h768 msg sHidden i) else cv0 i) positions := by
          funext i
          unfold ideal0Leaves
          by_cases hi : i ∈ positions
          · simp [hi]
          · have hiH : i ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
            simp only [hi, ite_false, hiH]
            have hnone : cache (hiddenCall0 h768 msg sHidden i) = none := by
              by_contra hne
              apply hkey
              refine ⟨hiddenCall0 h768 msg sHidden i, hne, ?_⟩
              unfold hiddenCall0 hiddenPrefixes
              rw [extractLsb'_cast_eq, leafCall0Input_prefix]
              exact Finset.mem_image.mpr ⟨i, hiH, rfl⟩
            have hte : (tableExtending cache table (hiddenCall0 h768 msg sHidden i) : Digest) =
                table (hiddenCall0 h768 msg sHidden i) := by
              change (cache (hiddenCall0 h768 msg sHidden i)).getD (table _) = _; rw [hnone]; rfl
            exact congrArg
              (fun d : Digest => leafChainFromCv0 (fun x => tableExtending cache table (x.cast h768.symm)) d (msg i))
              hte
        exact congrArg
          (fun lv =>
            let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
            (nodeValFromLeaves c lv 24 0, referenceProof (nodeValFromLeaves c lv) sOpen positions))
          hlv
      dsimp only
      rw [htr]
    rw [(EvalDistEq.of_evalDist_eq hRealProg).prEvent_eq p]
    constructor
    · exact prEvent_bind_le_prEvent_add_prEvent ($ᵗ (Index → Salt121)) _ _ _ _ _ _ fun sOpen =>
        prEvent_bind_le_prEvent_add_prEvent ($ᵗ (Index → Digest)) _ _ _ _ _ _ fun cv0 =>
          prEvent_bind_le_prEvent_add_prEvent ($ᵗ Compression) _ _ _ _ _ _ fun table =>
            (cond_one_sided_pointwise h768 permutation cache msg positions sHidden hkey observe p sOpen cv0 table).1
    · exact prEvent_bind_le_prEvent_add_two ($ᵗ (Index → Salt121)) _ _ _ _ _ _ _ _ fun sOpen =>
        prEvent_bind_le_prEvent_add_two ($ᵗ (Index → Digest)) _ _ _ _ _ _ _ _ fun cv0 =>
          prEvent_bind_le_prEvent_add_two ($ᵗ Compression) _ _ _ _ _ _ _ _ fun table =>
            (cond_one_sided_pointwise h768 permutation cache msg positions sHidden hkey observe p sOpen cv0 table).2

/-! ### 6. Combined Key + Observe Bad Bound (`≤ budget / 2^121`) and Tree Hit Bound -/

/-- For fixed `(cache, msg, positions)` with `keys.card ≤ q1` and `observe` budget `obsBudget`:
`Pr_{sHidden}[flagCondObs.2 = true] ≤ (keys.card + obsBudget) / 2^121`! -/
theorem flag_bad_bound_cond (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (msg : Message) (positions : Positions)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (obsBudget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) obsBudget) :
    Pr{let z ← ($ᵗ (Index → Salt121)) >>= fun sHidden =>
        flagCondObs h768 permutation cache msg positions sHidden observe}[z.2 = true] ≤
      ((keys.card + obsBudget : Nat) : ENNReal) / 2 ^ 121 := by
  classical
  let obsOnly (sHidden : Index → Salt121) : ProbComp (α × Unit × Bool) := do
    let sOpen ← $ᵗ (Index → Salt121)
    let cv0 ← $ᵗ (Index → Digest)
    let table ← $ᵗ Compression
    let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
    flaggedRun ⟨tableExtending cache table, permutation⟩ (marksPrefix positions sHidden) (observe tr.1 tr.2)
  have hobs_hit :
      Pr{let r ← ($ᵗ (Index → Salt121)) >>= obsOnly}[r.2.2 = true] ≤ (obsBudget : ENNReal) / 2 ^ 121 := by
    have hswap :
        𝒟[($ᵗ (Index → Salt121)) >>= obsOnly] =
        𝒟[do let sOpen ← $ᵗ (Index → Salt121)
             let cv0 ← $ᵗ (Index → Digest)
             let table ← $ᵗ Compression
             let tr := ideal0Transcript h768 (tableExtending cache table) msg sOpen cv0 positions
             let traced ← fixedOracleRun ⟨tableExtending cache table, permutation⟩ (traceCompression (observe tr.1 tr.2))
             let sHidden ← $ᵗ (Index → Salt121)
             pure (traced.1, (), traced.2.any (fun x => decide (x.extractLsb' 0 192 ∈ hiddenPrefixes positions sHidden)))] := by
      unfold obsOnly
      rw [evalDist_bind_comm_any ($ᵗ (Index → Salt121)) ($ᵗ (Index → Salt121))]
      apply _root_.evalDist_bind_congr; intro sOpen
      rw [evalDist_bind_comm_any ($ᵗ (Index → Salt121)) ($ᵗ (Index → Digest))]
      apply _root_.evalDist_bind_congr; intro cv0
      rw [evalDist_bind_comm_any ($ᵗ (Index → Salt121)) ($ᵗ Compression)]
      apply _root_.evalDist_bind_congr; intro table
      simp only [flaggedRun_marksPrefix_trace, Bool.false_or, map_eq_bind_pure_comp]
      exact evalDist_bind_comm_any ($ᵗ (Index → Salt121)) _ _
    rw [(EvalDistEq.of_evalDist_eq hswap).prEvent_eq (fun r => r.2.2 = true)]
    apply prEvent_bind_le_of_forall_le_of_support; intro sOpen _
    apply prEvent_bind_le_of_forall_le_of_support; intro cv0 _
    apply prEvent_bind_le_of_forall_le_of_support; intro table _
    apply prEvent_bind_le_of_forall_le_of_support; intro traced htraced
    rw [bind_pure_comp, prEvent_map]
    have hlen := trace_run_length ⟨tableExtending cache table, permutation⟩ _ obsBudget (hobs _ _) traced htraced
    have hle : (prEvent ((fun sH => traced.2.any (fun x => decide (x.extractLsb' 0 192 ∈ hiddenPrefixes positions sH)) = true) <$>
        ($ᵗ (Index → Salt121)))) ≤
        (prEvent ((fun sH => ∃ v ∈ traced.2.map (fun x => x.extractLsb' 0 192), v ∈ hiddenPrefixes positions sH) <$>
          ($ᵗ (Index → Salt121)))) := by
      apply prEvent_mono_of_support
      intro sH _ hany
      obtain ⟨x, hx, hdec⟩ := List.any_eq_true.mp hany
      exact ⟨x.extractLsb' 0 192, List.mem_map.mpr ⟨x, hx, rfl⟩, decide_eq_true_eq.mp hdec⟩
    exact hle.trans ((list_prefix_hit_121 positions _).trans (by
      simp only [List.length_map]
      exact ENNReal.div_le_div_right (Nat.cast_le.mpr hlen) _))
  -- Split `flagCondObs` on `cacheKeysHitPrefix cache positions sHidden`!
  have hsplit :
      Pr{let z ← ($ᵗ (Index → Salt121)) >>= fun sHidden =>
          flagCondObs h768 permutation cache msg positions sHidden observe}[z.2 = true] ≤
      Pr{let sHidden ← $ᵗ (Index → Salt121)}[cacheKeysHitPrefix cache positions sHidden] +
      Pr{let r ← ($ᵗ (Index → Salt121)) >>= obsOnly}[r.2.2 = true] := by
    have hpt : ∀ sHidden : Index → Salt121,
        Pr{let z ← flagCondObs h768 permutation cache msg positions sHidden observe}[z.2 = true] ≤
          Pr{let _ ← (pure sHidden : ProbComp (Index → Salt121))}[cacheKeysHitPrefix cache positions sHidden] +
          Pr{let r ← obsOnly sHidden}[r.2.2 = true] := by
      intro sHidden
      by_cases hkey : cacheKeysHitPrefix cache positions sHidden
      · simp only [prEvent_pure, hkey, ite_true]
        exact (prEvent_le_one _).trans le_self_add
      · simp only [prEvent_pure, hkey, ite_false, zero_add]
        have heq : flagCondObs h768 permutation cache msg positions sHidden observe =
            (fun r : α × Unit × Bool => (r.1, r.2.2)) <$> obsOnly sHidden := by
          unfold flagCondObs obsOnly
          simp only [cacheKeysHitBool_neg hkey, Bool.false_or, map_bind, bind_pure_comp]
        rw [heq, prEvent_map]
    have hint := prEvent_bind_le_prEvent_add_prEvent ($ᵗ (Index → Salt121))
      (fun sHidden => flagCondObs h768 permutation cache msg positions sHidden observe)
      (fun sHidden => (pure sHidden : ProbComp (Index → Salt121)))
      obsOnly
      (fun z => z.2 = true) (fun sH => cacheKeysHitPrefix cache positions sH) (fun r => r.2.2 = true)
      hpt
    simpa only [bind_pure] using hint
  refine (hsplit.trans (add_le_add (cache_keys_hit_prefix_121 positions cache keys covered) hobs_hit)).trans ?_
  rw [← ENNReal.add_div, Nat.cast_add]

/-- Tree-hit bound for a clean cache (`¬ CacheHitsPrefix cache (hiddenPrefixes positions sH)`):
`Pr[treeHitCond.2.2 = true] ≤ (LENGTH + HONEST_TREE_BUDGET) * LENGTH / 2^192`! -/
theorem tree_hit_clean_bound (h768 : COMPRESSION_INPUT_LENGTH = 768) (permutation : Perm)
    (cache : CompressionCache) (msg : Message) (positions : Positions) (sH : Index → Salt121)
    (hclean : ¬ CacheHitsPrefix cache (hiddenPrefixes positions sH)) :
    Pr{let t ← treeHitCond h768 permutation cache msg positions sH}[t.2.2 = true] ≤
      (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  classical
  let P := hiddenPrefixes positions sH
  unfold treeHitCond
  apply prEvent_bind_le_of_forall_le_of_support
  intro sOpen _
  have hcv0_bad : (prEvent ((fun cv0 : Index → Digest => ∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P) <$>
      ($ᵗ (Index → Digest)))) ≤ (LENGTH : ENNReal) * (P.card : ENNReal) / 2 ^ 192 := by
    have hlist : ∀ (is : List Index),
        (prEvent ((fun cv0 : Index → Digest => ∃ i ∈ is, (cv0 i).extractLsb' 0 192 ∈ P) <$>
          ($ᵗ (Index → Digest)))) ≤ (is.length : ENNReal) * (P.card : ENNReal) / 2 ^ 192 := by
      intro is; induction is with
      | nil =>
        have hz : (prEvent ((fun cv0 : Index → Digest => ∃ i ∈ ([] : List Index), (cv0 i).extractLsb' 0 192 ∈ P) <$> ($ᵗ (Index → Digest)))) = 0 :=
          prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ ⟨_, hi, _⟩ => List.not_mem_nil hi)
        rw [hz]; exact zero_le
      | cons i rest ih =>
        have hu := prEvent_or_le ($ᵗ (Index → Digest))
          (fun cv0 => (cv0 i).extractLsb' 0 192 ∈ P)
          (fun cv0 => ∃ j ∈ rest, (cv0 j).extractLsb' 0 192 ∈ P)
        have hmono : (prEvent ((fun cv0 => ∃ j ∈ i :: rest, (cv0 j).extractLsb' 0 192 ∈ P) <$> ($ᵗ (Index → Digest)))) ≤ _ :=
          (prEvent_mono_of_support _ _ _ (fun cv0 _ ⟨j, hj, hm⟩ => by
            rcases List.mem_cons.mp hj with rfl | hr
            · exact Or.inl hm
            · exact Or.inr ⟨j, hr, hm⟩)).trans hu
        have hone : (prEvent ((fun cv0 : Index → Digest => (cv0 i).extractLsb' 0 192 ∈ P) <$> ($ᵗ (Index → Digest)))) ≤
            (P.card : ENNReal) / 2 ^ 192 :=
          prEvent_uniform_coord_le (D := Index) (R := Digest) i
            (fun fresh => fresh.extractLsb' 0 192 ∈ P) (uniform_digest_hits_prefix_le P)
        refine (hmono.trans (add_le_add hone ih)).trans ?_
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [add_mul, one_mul, ENNReal.add_div, add_comm]
    have hle : (prEvent ((fun cv0 => ∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P) <$> ($ᵗ (Index → Digest)))) ≤
        (prEvent ((fun cv0 => ∃ i ∈ (Finset.univ : Finset Index).toList, (cv0 i).extractLsb' 0 192 ∈ P) <$> ($ᵗ (Index → Digest)))) :=
      prEvent_mono_of_support _ _ _ (fun _ _ ⟨i, _, hm⟩ => ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), hm⟩)
    exact hle.trans (by
      simpa only [Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using
        hlist (Finset.univ : Finset Index).toList)
  have hcv0_clean : ∀ cv0 : Index → Digest, ¬ (∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P) →
      (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
        (($ᵗ Compression) >>= fun table =>
          flaggedRun ⟨tableExtending cache table, permutation⟩ (marksPrefix positions sH)
            (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))))) ≤
      (HONEST_TREE_BUDGET : ENNReal) * (P.card : ENNReal) / 2 ^ 192 := by
    intro cv0 hcv0_ok
    let comp := queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)
    have hcomp_bd : PublicQueryBound comp HONEST_TREE_BUDGET := by
      apply queryTreeFromLeafFn_bound h768
      intro i; unfold ideal0LeafFn
      by_cases hi : i ∈ positions
      · rw [if_pos hi]; exact queryLeafOpened_bound h768 i (sOpen i) (msg i)
      · rw [if_neg hi]; exact (queryLeafFromCv0_bound h768 (cv0 i) (msg i)).mono (by omega)
    have hhit_le_tr :
        (prEvent ((fun res : (Nat → Nat → Digest) × Unit × Bool => res.2.2 = true) <$>
          (($ᵗ Compression) >>= fun table =>
            flaggedRun ⟨tableExtending cache table, permutation⟩ (marksPrefix positions sH) comp))) ≤
        (prEvent ((fun res : (Nat → Nat → Digest) × CompressionReplies =>
          ∃ pair ∈ res.2, pair.2.extractLsb' 0 192 ∈ P) <$>
          (($ᵗ Compression) >>= fun table =>
            fixedOracleRun ⟨tableExtending cache table, permutation⟩ (traceCompressionReplies comp)))) := by
      simp only [map_bind, prEvent_bind_eq_tsum_prEvent]
      apply ENNReal.tsum_le_tsum; intro table
      apply mul_le_mul_of_nonneg_left _ zero_le
      let o : Oracle := ⟨tableExtending cache table, permutation⟩
      obtain ⟨nodes, tr, htr_run, hgood⟩ := queryIdeal0Tree_good_trace h768 o msg sOpen cv0 positions
      rw [htr_run]
      have hflag_tr : ∀ {β : Type} (c : OracleComp World β) (f : Bool),
          flaggedRun o (marksPrefix positions sH) c f =
          (fun res : β × CompressionReplies =>
            (res.1, (), f || res.2.any (fun p => decide (p.1.extractLsb' 0 192 ∈ P)))) <$>
            fixedOracleRun o (traceCompressionReplies c) := by
        intro β c f
        induction c using OracleComp.inductionOn generalizing f with
        | pure v =>
          change flaggedRun o (marksPrefix positions sH) (pure v) f =
            (fun res : β × CompressionReplies => _) <$> fixedOracleRun o (pure (v, []))
          rw [fixed_oracle_run_pure, map_pure]
          simp [flaggedRun]
        | query_bind q k ih =>
          rw [flagged_run_query_bind]
          rcases q with coins | pq
          · change _ = (fun res : β × CompressionReplies => _) <$>
              fixedOracleRun o ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
                traceCompressionReplies (k ans))
            rw [fixed_oracle_run_private, map_bind]
            apply bind_congr; intro ans
            rw [show marksPrefix positions sH (.inl coins) = false from rfl, Bool.or_false, ih ans f]
          · rcases pq with x | permq
            · change _ = (fun res : β × CompressionReplies => _) <$>
                fixedOracleRun o ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>= fun (ans : Digest) =>
                  traceCompressionReplies (k ans) >>= fun p => pure (p.1, (x, ans) :: p.2))
              simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_bind]
              rw [fixed_oracle_run_compress, fixed_oracle_run_bind, map_bind, ih]
              simp only [fixed_oracle_run_pure, map_pure, bind_pure_comp]
              apply congrArg (fun g => g <$> fixedOracleRun o (traceCompressionReplies (k (o.compression x))))
              funext res
              simp only [List.any_cons, marksPrefix, P, Bool.or_assoc]
            · rcases permq with x | x
              · change _ = (fun res : β × CompressionReplies => _) <$>
                  fixedOracleRun o ((liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World _) >>= fun ans =>
                    traceCompressionReplies (k ans))
                rw [fixed_oracle_run_public]
                simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_bind,
                  marksPrefix, Bool.or_false]
                exact ih (o.permutation x) f
              · change _ = (fun res : β × CompressionReplies => _) <$>
                  fixedOracleRun o ((liftM (World.query (.inr (.inr (.inr x)))) : OracleComp World _) >>= fun ans =>
                    traceCompressionReplies (k ans))
                rw [fixed_oracle_run_public]
                simp only [Oracle.world, Oracle.answer, QueryImpl.add_apply_inr, pure_bind,
                  marksPrefix, Bool.or_false]
                exact ih (o.permutation.symm x) f
      rw [hflag_tr comp false, htr_run, map_pure]
      simp only [prEvent_pure]
      split_ifs with h1 h2
      · exact le_refl 1
      · exfalso; apply h2
        simp only [Bool.false_or] at h1
        obtain ⟨p, hp, hdec⟩ := List.any_eq_true.mp h1
        have hp192 : p.1.extractLsb' 0 192 ∈ P := decide_eq_true_eq.mp hdec
        obtain ⟨i, hiH, hpi⟩ := Finset.mem_image.mp hp192
        have hi : i ∉ positions := (Finset.mem_sdiff.mp hiH).2
        have hpTag : p.1.extractLsb' 128 64 = leafTag i := by
          have ht := congrArg (fun v : BitVec 192 => v.extractLsb' 128 64) hpi
          rw [leafCall0Prefix_tag] at ht
          have hex : (p.1.extractLsb' 0 192).extractLsb' 128 64 = p.1.extractLsb' 128 64 := by
            apply BitVec.eq_of_getLsbD_eq; intro b hb
            simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
              show 128 + b < 192 by omega, Nat.zero_add]
          exact hex.symm.trans ht.symm
        rcases hgood p hp with ⟨j, hj, hjt⟩ | ⟨j, hj, hjcv⟩ | ⟨q, hq, hqeq⟩
        · have : j = i := leafTag_injective (hjt.symm.trans hpTag)
          exact False.elim (hi (this ▸ hj))
        · exact False.elim (hcv0_ok ⟨j, hj, hjcv ▸ hp192⟩)
        · exact ⟨q, hq, hqeq ▸ hp192⟩
      · exact zero_le
      · exact le_refl 0
    have heq_rom := (EvalDistEq.of_evalDist_eq
      (compression_sampling_equivalence permutation (traceCompressionReplies comp) cache)).prEvent_eq
        (fun res : (Nat → Nat → Digest) × CompressionReplies => ∃ pair ∈ res.2, pair.2.extractLsb' 0 192 ∈ P)
    simp only [Functor.map_map, Function.comp_def] at heq_rom
    rw [← heq_rom] at hhit_le_tr
    have hin_cache :
        (prEvent ((fun res : ((Nat → Nat → Digest) × CompressionReplies) × CompressionCache =>
          ∃ pair ∈ res.1.2, pair.2.extractLsb' 0 192 ∈ P) <$>
          (compressionRun permutation (traceCompressionReplies comp) cache))) ≤
        (prEvent ((fun res => CacheHitsPrefix res.2 P) <$>
          (compressionRun permutation (traceCompressionReplies comp) cache))) := by
      apply prEvent_mono_of_support
      intro res hreach ⟨pair, hmem, hpref⟩
      exact ⟨pair.1, pair.2, (traceReplies_compressionRun_cache permutation comp cache res hreach).2 pair hmem, hpref⟩
    have hrom_bd := compression_run_hits_prefix_bound permutation (traceCompressionReplies comp)
      HONEST_TREE_BUDGET (traceReplies_bound comp HONEST_TREE_BUDGET hcomp_bd) cache P hclean
    refine hhit_le_tr.trans (hin_cache.trans (hrom_bd.trans ?_))
    rw [mul_div_assoc]
  have hcomb := prEvent_bind_le_prEvent_add_of_support
    ($ᵗ (Index → Digest))
    (fun cv0 => ($ᵗ Compression) >>= fun table =>
      flaggedRun ⟨tableExtending cache table, permutation⟩ (marksPrefix positions sH)
        (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions)))
    (fun cv0 => ∃ i ∉ positions, (cv0 i).extractLsb' 0 192 ∈ P)
    (fun res => res.2.2 = true)
    (fun cv0 _ hok => hcv0_clean cv0 hok)
  refine (hcomb.trans (add_le_add hcv0_bad le_rfl)).trans ?_
  have hcard : P.card ≤ LENGTH := hiddenPrefixes_card_le positions sH
  rw [← ENNReal.add_div, ← add_mul]
  apply ENNReal.div_le_div_right
  calc
    ((LENGTH : ENNReal) + HONEST_TREE_BUDGET) * (P.card : ENNReal)
      ≤ ((LENGTH : ENNReal) + HONEST_TREE_BUDGET) * (LENGTH : ENNReal) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) zero_le
    _ = (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) := by push_cast; rfl

/-! ### 7. Step 2: `flagCondObs(m₀)` ↔ `flagCondObs(m₁)` 256-Bit Leaf-by-Leaf Hybrid -/

def hybridMessage (left right : Message) (indices : List Index) : Message :=
  fun i => if i ∈ indices then right i else left i

theorem flagCondObs_coordinate_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (msg : Message) (positions : Positions) (sHidden : Index → Salt121)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (obsBudget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) obsBudget)
    (hidden : Index) (hunopen : hidden ∉ positions) (left right : Entry) :
    measureTVDist
      (flagCondObs h768 permutation cache (Function.update msg hidden left) positions sHidden observe)
      (flagCondObs h768 permutation cache (Function.update msg hidden right) positions sHidden observe) ≤
      6 * ((keys.card + (HONEST_TREE_BUDGET + obsBudget) + 3 : Nat) : ℝ) / 2 ^ 256 := by
  classical
  let m := marksPrefix positions sHidden
  let bKey : Bool := cacheKeysHitBool cache positions sHidden
  let post (z : α × Bool) : α × Bool := (z.1, bKey || z.2)
  let obsFlag (rt : Commitment) (pf : Proof) : OracleComp World (α × Bool) :=
    flagComp m (observe rt pf) false
  have hobsFlag_bd : ∀ rt pf, PublicQueryBound (obsFlag rt pf) obsBudget :=
    fun rt pf => flagComp_bound m (observe rt pf) obsBudget (hobs rt pf) false
  let exceptComp (sOpen : Index → Salt121) (cv0 : Index → Digest) (d : Digest) : OracleComp World (α × Bool) := do
    let nodes ← queryTreeFromLeafFn h768 (fun i =>
      if i = hidden then pure d else ideal0LeafFn h768 msg sOpen cv0 positions i)
    obsFlag (nodes 24 0) (referenceProof nodes sOpen positions)
  have hexcept_bd : ∀ sOpen cv0 d, PublicQueryBound (exceptComp sOpen cv0 d) (HONEST_TREE_BUDGET + obsBudget) := by
    intro sOpen cv0 d
    apply public_query_bound_bind _ (fun nodes => hobsFlag_bd _ _)
    apply queryTreeFromLeafFn_bound h768
    intro i
    by_cases hih : i = hidden
    · rw [if_pos hih]; exact (public_query_bound_pure' d 0).mono (by omega)
    · rw [if_neg hih]; unfold ideal0LeafFn
      by_cases hi : i ∈ positions
      · rw [if_pos hi]; exact queryLeafOpened_bound h768 i (sOpen i) (msg i)
      · rw [if_neg hi]; exact (queryLeafFromCv0_bound h768 (cv0 i) (msg i)).mono (by omega)
  have hupdate_eq : ∀ (val : Entry),
      𝒟[flagCondObs h768 permutation cache (Function.update msg hidden val) positions sHidden observe] =
      𝒟[post <$> (do
          let sOpen ← $ᵗ (Index → Salt121)
          let cv0 ← $ᵗ (Index → Digest)
          let table ← $ᵗ Compression
          let fresh ← $ᵗ Digest
          let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (exceptComp sOpen cv0 (leafChainFromCv0 c fresh val)))] := by
    intro val
    unfold flagCondObs
    simp only [map_bind]
    apply _root_.evalDist_bind_congr; intro sOpen
    rw [← uniform_coordinate_bind_any hidden (fun cv0 =>
      ($ᵗ Compression) >>= fun table =>
        let tr := ideal0Transcript h768 (tableExtending cache table) (Function.update msg hidden val) sOpen cv0 positions
        flaggedRun ⟨tableExtending cache table, permutation⟩ m (observe tr.1 tr.2) >>=
          fun r => pure (r.1, bKey || r.2.2))]
    apply _root_.evalDist_bind_congr; intro cv0
    rw [evalDist_bind_comm_any ($ᵗ Digest) ($ᵗ Compression)]
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
    simp only [obsFlag, fixed_flagComp, Functor.map_map, bind_pure_comp]
    rfl
  rw [measureTVDist, hupdate_eq left, hupdate_eq right, ← measureTVDist]
  refine (measureTVDist_map_le _ _ post Measurable.of_discrete).trans ?_
  apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt121)) _ _ (by positivity)
  intro sOpen
  apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Digest)) _ _ (by positivity)
  intro cv0
  have hl := cached_chain3_distance_discrete h768 permutation cache keys covered left
    (exceptComp sOpen cv0) (HONEST_TREE_BUDGET + obsBudget) (hexcept_bd sOpen cv0)
  have hr := cached_chain3_distance_discrete h768 permutation cache keys covered right
    (exceptComp sOpen cv0) (HONEST_TREE_BUDGET + obsBudget) (hexcept_bd sOpen cv0)
  rw [measureTVDist_comm] at hr
  refine ((measureTVDist_triangle _ _ _).trans (add_le_add hl hr)).trans ?_
  exact le_of_eq (by ring)

theorem flagCondObs_hybrid_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ k, cache k ≠ none → k ∈ keys)
    (left right : Message) (positions : Positions) (sHidden : Index → Salt121)
    (hagree : ∀ i ∈ positions, left i = right i)
    {α : Type} (observe : Commitment → Proof → OracleComp World α) (obsBudget : Nat)
    (hobs : ∀ rt pf, PublicQueryBound (observe rt pf) obsBudget) :
    measureTVDist
      (flagCondObs h768 permutation cache left positions sHidden observe)
      (flagCondObs h768 permutation cache right positions sHidden observe) ≤
      (LENGTH : ℝ) * (6 * ((keys.card + (HONEST_TREE_BUDGET + obsBudget) + 3 : Nat) : ℝ) / 2 ^ 256) := by
  let stepLoss : ℝ := 6 * ((keys.card + (HONEST_TREE_BUDGET + obsBudget) + 3 : Nat) : ℝ) / 2 ^ 256
  have hnn : 0 ≤ stepLoss := by positivity
  have hgen : ∀ (indices : List Index),
      measureTVDist
        (flagCondObs h768 permutation cache left positions sHidden observe)
        (flagCondObs h768 permutation cache (hybridMessage left right indices) positions sHidden observe) ≤
        (indices.length : ℝ) * stepLoss := by
    intro indices; induction indices with
    | nil =>
      have hnil : hybridMessage left right [] = left := by funext i; simp [hybridMessage]
      simp [hnil]
    | cons i rest ih =>
      have hcons : hybridMessage left right (i :: rest) = Function.update (hybridMessage left right rest) i (right i) := by
        funext j; by_cases hj : j = i <;> simp [hybridMessage, hj]
      have hstep : measureTVDist
          (flagCondObs h768 permutation cache (hybridMessage left right rest) positions sHidden observe)
          (flagCondObs h768 permutation cache (hybridMessage left right (i :: rest)) positions sHidden observe) ≤ stepLoss := by
        rw [hcons]
        by_cases hi : i ∈ positions
        · have hsame : right i = hybridMessage left right rest i := by
            unfold hybridMessage; split
            · rfl
            · exact (hagree i hi).symm
          rw [hsame, Function.update_eq_self, measureTVDist_self]; exact hnn
        · have hchg := flagCondObs_coordinate_distance h768 permutation cache keys covered
            (hybridMessage left right rest) positions sHidden observe obsBudget hobs i hi
            (hybridMessage left right rest i) (right i)
          simpa only [Function.update_eq_self] using hchg
      refine ((measureTVDist_triangle _ _ _).trans (add_le_add ih hstep)).trans ?_
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      exact le_of_eq (by ring)
  have hall : hybridMessage left right (Finset.univ.toList : List Index) = right := by
    funext i; simp [hybridMessage]
  have hr := hgen (Finset.univ.toList : List Index)
  simpa only [hall, Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using hr

/-! ### 8. Final 121-Bit Statistical Hiding Arithmetic & Master Theorem -/

theorem moon_hiding_121_arithmetic (budget : Nat) :
    (LENGTH : ℝ) * (6 * ((budget + HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / 2 ^ 256) +
    ((budget : ℝ) / 2 ^ 121) +
    2 * ((((budget + LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) ≤
    ((budget : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS := by
  have hb : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have hL : (LENGTH : ℝ) = (2 : ℝ) ^ 24 := by norm_num [LENGTH, LOG_LENGTH]
  have hLT_nat : LENGTH + HONEST_TREE_BUDGET ≤ 2 ^ 27 := by
    unfold HONEST_TREE_BUDGET LENGTH LOG_LENGTH; omega
  have hLT : ((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) ≤ (2 : ℝ) ^ 27 := by exact_mod_cast hLT_nat
  have hT3_nat : HONEST_TREE_BUDGET + 3 ≤ 2 ^ 27 := by
    unfold HONEST_TREE_BUDGET LENGTH LOG_LENGTH; omega
  have hT3 : ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) ≤ (2 : ℝ) ^ 27 := by exact_mod_cast hT3_nat
  have h2pos : ∀ n : Nat, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  have hp121 : (2 : ℝ) ^ 121 = 2 * 2 ^ 120 := by rw [← pow_succ']
  have hp192 : (2 : ℝ) ^ 192 = 2 ^ 72 * 2 ^ 120 := by rw [← pow_add]
  have hp256 : (2 : ℝ) ^ 256 = 2 ^ 136 * 2 ^ 120 := by rw [← pow_add]
  have hA : (budget : ℝ) / (2 : ℝ) ^ 121 = (1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by
    rw [hp121]; ring
  have hB_bud : 2 * ((budget : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) ≤
      (1 / 4) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by
    have hcoeff : (2 * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 72 ≤ 1 / 4 := by
      have h72 : (2 : ℝ) ^ 72 = (2 : ℝ) ^ 25 * (2 : ℝ) ^ 47 := by rw [← pow_add]
      have h25 : 2 * (2 : ℝ) ^ 24 = (2 : ℝ) ^ 25 := by rw [← pow_succ']
      rw [h25, h72, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 25))]
      have h47 : (4 : ℝ) ≤ (2 : ℝ) ^ 47 := by
        have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        rw [h4]; exact pow_le_pow_right₀ (by norm_num) (by decide)
      exact one_div_le_one_div_of_le (by norm_num) h47
    have hEq : 2 * ((budget : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) =
        ((2 * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 72) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hB_cst : 2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) ≤
      (1 / 2) * (1 / (2 : ℝ) ^ 120) := by
    have hnum : 2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24) ≤ (2 : ℝ) ^ 52 := by
      have : (2 : ℝ) * ((2 : ℝ) ^ 27 * (2 : ℝ) ^ 24) = (2 : ℝ) ^ 52 := by rw [← pow_add, ← pow_succ']
      linarith [mul_le_mul_of_nonneg_right hLT (h2pos 24).le]
    have h52 : (2 : ℝ) ^ 52 / (2 : ℝ) ^ 72 ≤ 1 / 2 := by
      have : (2 : ℝ) ^ 72 = (2 : ℝ) ^ 52 * (2 : ℝ) ^ 20 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 52))]
      have h20 : (2 : ℝ) ≤ (2 : ℝ) ^ 20 := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 1 ≤ 20)
      exact one_div_le_one_div_of_le (by norm_num) h20
    have hEq : 2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120)) =
        (2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 72) * (1 / (2 : ℝ) ^ 120) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 72).le).trans h52) (by positivity)
  have hC_bud : (2 : ℝ) ^ 24 * (6 * (budget : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) ≤
      (1 / 4) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by
    have h6 : (6 : ℝ) * (2 : ℝ) ^ 24 ≤ (2 : ℝ) ^ 27 := by
      have : (8 : ℝ) * (2 : ℝ) ^ 24 = (2 : ℝ) ^ 27 := by
        have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        rw [h8, ← pow_add]
      linarith [h2pos 24]
    have h27 : (2 : ℝ) ^ 27 / (2 : ℝ) ^ 136 ≤ 1 / 4 := by
      have : (2 : ℝ) ^ 136 = (2 : ℝ) ^ 27 * (2 : ℝ) ^ 109 := by rw [← pow_add]
      rw [this, div_mul_eq_div_div, div_self (ne_of_gt (h2pos 27))]
      have h109 : (4 : ℝ) ≤ (2 : ℝ) ^ 109 := by
        have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        rw [h4]; exact pow_le_pow_right₀ (by norm_num) (by decide)
      exact one_div_le_one_div_of_le (by norm_num) h109
    have hEq : (2 : ℝ) ^ 24 * (6 * (budget : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) =
        (((6 : ℝ) * (2 : ℝ) ^ 24) / (2 : ℝ) ^ 136) * ((budget : ℝ) / (2 : ℝ) ^ 120) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right h6 (h2pos 136).le).trans h27) (by positivity)
  have hC_cst : (2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) ≤
      (1 / 2) * (1 / (2 : ℝ) ^ 120) := by
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
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 1 ≤ 82)
      exact one_div_le_one_div_of_le (by norm_num) h82
    have hEq : (2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) =
        (((2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ))) / (2 : ℝ) ^ 136) * (1 / (2 : ℝ) ^ 120) := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hnum (h2pos 136).le).trans h54) (by positivity)
  have hLHS :
      (LENGTH : ℝ) * (6 * ((budget + HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / 2 ^ 256) +
      ((budget : ℝ) / 2 ^ 121) +
      2 * ((((budget + LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192) =
      ((2 : ℝ) ^ 24 * (6 * (budget : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) +
       (budget : ℝ) / (2 : ℝ) ^ 121 +
       2 * ((budget : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120))) +
      ((2 : ℝ) ^ 24 * (6 * ((HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / ((2 : ℝ) ^ 136 * (2 : ℝ) ^ 120)) +
       2 * (((LENGTH + HONEST_TREE_BUDGET : Nat) : ℝ) * (2 : ℝ) ^ 24 / ((2 : ℝ) ^ 72 * (2 : ℝ) ^ 120))) := by
    push_cast
    rw [hL, hp192, hp256]
    ring
  have hRHS : ((budget : ℝ) + 1) / (2 : ℝ) ^ HIDING_SECURITY_BITS =
      ((1 / 4) * ((budget : ℝ) / (2 : ℝ) ^ 120) + (1 / 2) * ((budget : ℝ) / (2 : ℝ) ^ 120) +
       (1 / 4) * ((budget : ℝ) / (2 : ℝ) ^ 120)) +
      ((1 / 2) * (1 / (2 : ℝ) ^ 120) + (1 / 2) * (1 / (2 : ℝ) ^ 120)) := by
    unfold HIDING_SECURITY_BITS; ring
  rw [hLHS, hRHS]
  linarith [hA, hB_bud, hB_cst, hC_bud, hC_cst]

/-- Master Hiding Theorem: once `MoonCommitRef` + `MoonOpenRef` establish `HonestTranscriptRefines`,
the submitted B1-Ultra-121 RISC-V scheme satisfies the full two-stage adaptive `Hiding HIDING_ERROR` property. -/
theorem hiding_of_refines (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (href : HonestTranscriptRefines h768) :
    submission.scheme.Hiding HIDING_ERROR := by
  classical
  constructor
  · intro _ budget; unfold HIDING_ERROR; exact le_min (by norm_num) (by positivity)
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _)
    let staged (perm : Perm) (sel : Bool) : ProbComp Output := do
      let sHidden ← $ᵗ (Index → Salt121)
      let (ch, cache) ← compressionRun perm adversary.choose ∅
      realCondObs h768 perm cache (if sel then ch.message₁ else ch.message₀)
        ch.positions sHidden (adversary.observe ch.aux)
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
        let salts ← (liftM ($ᵗ (Index → Salt121)) : OracleComp World (Index → Salt121))
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
        rw [fixed_oracle_run_bind]
        have hstep1 :
            𝒟[fixedOracleRun o (honestTranscript (if sel then ch.message₁ else ch.message₀) ch.positions) >>=
                fun tr => fixedOracleRun o (adversary.observe ch.aux tr.1 tr.2)] =
            𝒟[(($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
                pure (referenceTranscript h768 o.compression (if sel then ch.message₁ else ch.message₀)
                  (splitSalts121 packed) ch.positions)) >>=
                fun tr => fixedOracleRun o (adversary.observe ch.aux tr.1 tr.2)] :=
          ((href o (if sel then ch.message₁ else ch.message₀) ch.positions).bind_left _).evalDist_eq
        rw [hstep1, bind_assoc, fixed_oracle_run_bind, fixed_oracle_run_coins]
        simp only [pure_bind]
        let msg := if sel then ch.message₁ else ch.message₀
        trans 𝒟[($ᵗ (Index → Salt121)) >>= fun salts =>
          let tr := referenceTranscript h768 o.compression msg salts ch.positions
          fixedOracleRun o (adversary.observe ch.aux tr.1 tr.2)]
        · exact splitSalts121_uniform_bind
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
      · apply _root_.evalDist_bind_congr; intro o; exact href_run o
      · simp only [Oracle.sample, bind_assoc, pure_bind]
        rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)]
        apply _root_.evalDist_bind_congr; intro perm
        unfold refComp
        rw [staged_compression_sampling]
        unfold staged realCondObs
        rw [distribution_bind_comm ($ᵗ (Index → Salt121)) (compressionRun perm adversary.choose ∅)]
        apply _root_.evalDist_bind_congr; rintro ⟨ch, cache⟩
        let msg := if sel then ch.message₁ else ch.message₀
        trans 𝒟[do let table ← $ᵗ Compression
                   let salts ← $ᵗ (Index → Salt121)
                   let tr := referenceTranscript h768 (tableExtending cache table) msg salts ch.positions
                   fixedOracleRun ⟨tableExtending cache table, perm⟩ (adversary.observe ch.aux tr.1 tr.2)]
        · apply _root_.evalDist_bind_congr; intro table
          rw [fixed_oracle_run_bind, fixed_oracle_run_coins]
          apply _root_.evalDist_bind_congr; intro salts
          let o : Oracle := ⟨tableExtending cache table, perm⟩
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
        · trans 𝒟[do let table ← $ᵗ Compression
                     let sOpen ← $ᵗ (Index → Salt121)
                     let sHidden ← $ᵗ (Index → Salt121)
                     let tr := referenceTranscript h768 (tableExtending cache table) msg
                       (saltsMerge ch.positions sOpen sHidden) ch.positions
                     fixedOracleRun ⟨tableExtending cache table, perm⟩ (adversary.observe ch.aux tr.1 tr.2)]
          · apply _root_.evalDist_bind_congr; intro table
            exact (saltsMerge_uniform_bind ch.positions _).symm
          · rw [distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Salt121))]
            trans 𝒟[do let sOpen ← $ᵗ (Index → Salt121)
                       let sHidden ← $ᵗ (Index → Salt121)
                       let table ← $ᵗ Compression
                       let tr := referenceTranscript h768 (tableExtending cache table) msg
                         (saltsMerge ch.positions sOpen sHidden) ch.positions
                       fixedOracleRun ⟨tableExtending cache table, perm⟩ (adversary.observe ch.aux tr.1 tr.2)]
            · apply _root_.evalDist_bind_congr; intro sOpen
              exact distribution_bind_comm ($ᵗ Compression) ($ᵗ (Index → Salt121)) _
            · exact distribution_bind_comm ($ᵗ (Index → Salt121)) ($ᵗ (Index → Salt121)) _
    rw [measureTVDist, hstaged_eq false, hstaged_eq true, ← measureTVDist]
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Perm) _ _ (by positivity)
    intro perm
    let flagStaged (sel : Bool) : ProbComp (Output × Bool) := do
      let sHidden ← $ᵗ (Index → Salt121)
      let (ch, cache) ← compressionRun perm adversary.choose ∅
      flagCondObs h768 perm cache (if sel then ch.message₁ else ch.message₀)
        ch.positions sHidden (adversary.observe ch.aux)
    let treeStaged (sel : Bool) : ProbComp ((Nat → Nat → Digest) × Unit × Bool) := do
      let sHidden ← $ᵗ (Index → Salt121)
      let (ch, cache) ← compressionRun perm adversary.choose ∅
      treeHitCond h768 perm cache (if sel then ch.message₁ else ch.message₀) ch.positions sHidden
    let badBound : ENNReal := (budget : ENNReal) / 2 ^ 121
    let slackBound : ENNReal := (((budget + LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192
    -- Bound 1: `Pr[flagStaged sel : z.2 = true] ≤ budget / 2^121` (using exact combined `q1 + (budget - q1) = budget`!)
    have hflag_bad : ∀ sel : Bool,
        Pr{let z ← flagStaged sel}[z.2 = true] ≤ badBound := by
      intro sel
      have hswap :
          𝒟[flagStaged sel] =
          𝒟[do let (ch, cache) ← compressionRun perm adversary.choose ∅
               let sHidden ← $ᵗ (Index → Salt121)
               flagCondObs h768 perm cache (if sel then ch.message₁ else ch.message₀)
                 ch.positions sHidden (adversary.observe ch.aux)] :=
        evalDist_bind_comm_any ($ᵗ (Index → Salt121)) (compressionRun perm adversary.choose ∅) _
      rw [(EvalDistEq.of_evalDist_eq hswap).prEvent_eq (fun z => z.2 = true)]
      apply prEvent_bind_le_of_forall_le_of_support
      rintro ⟨ch, cache⟩ hreach
      obtain ⟨q1, keys, hq1_le, hkeys_le, hcov, hobs_bd⟩ :=
        first_stage_combined_budget perm adversary bounded (ch, cache) hreach
      have hb := flag_bad_bound_cond h768 perm cache keys hcov
        (if sel then ch.message₁ else ch.message₀) ch.positions (adversary.observe ch.aux) (budget - q1) hobs_bd
      refine hb.trans ?_
      exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _
    -- Bound 2: `Pr[treeStaged sel : t.2.2 = true] ≤ (budget + LENGTH + HONEST_TREE_BUDGET) * LENGTH / 2^192`!
    have htree_bad : ∀ sel : Bool,
        Pr{let t ← treeStaged sel}[t.2.2 = true] ≤ slackBound := by
      intro sel
      unfold treeStaged
      apply prEvent_bind_le_of_forall_le_of_support
      intro sHidden _
      have hstage1_hit :
          Pr{let res ← compressionRun perm adversary.choose ∅}[CacheHitsPrefix res.2 (allPrefixes sHidden)] ≤
            (budget : ENNReal) * ((allPrefixes sHidden).card : ENNReal) / 2 ^ 192 := by
        have h := compression_run_hits_prefix_bound perm adversary.choose budget
          (hiding_choose_query_bound adversary bounded) ∅ (allPrefixes sHidden)
          (by rintro ⟨k, ans, hk, _⟩; cases hk)
        rwa [← mul_div_assoc] at h
      have hstep := prEvent_bind_le_prEvent_add_of_support
        (compressionRun perm adversary.choose ∅)
        (fun p => treeHitCond h768 perm p.2 (if sel then p.1.message₁ else p.1.message₀) p.1.positions sHidden)
        (fun p => CacheHitsPrefix p.2 (allPrefixes sHidden))
        (fun t => t.2.2 = true)
        (ε := (((LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ENNReal) / 2 ^ 192)
        (fun p _ hclean => tree_hit_clean_bound h768 perm p.2 _ p.1.positions sHidden
          (fun hhit => hclean (hhit.mono (hiddenPrefixes_subset_allPrefixes p.1.positions sHidden))))
      refine (hstep.trans (add_le_add hstage1_hit le_rfl)).trans ?_
      have hcard := allPrefixes_card_le sHidden
      have h1 : (budget : ENNReal) * ((allPrefixes sHidden).card : ENNReal) / 2 ^ 192 ≤
          ((budget * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
        apply ENNReal.div_le_div_right
        calc
          (budget : ENNReal) * ((allPrefixes sHidden).card : ENNReal)
            ≤ (budget : ENNReal) * (LENGTH : ENNReal) :=
              mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) zero_le
          _ = ((budget * LENGTH : Nat) : ENNReal) := by push_cast; rfl
      refine (add_le_add h1 le_rfl).trans ?_
      rw [← ENNReal.add_div]
      apply ENNReal.div_le_div_right
      push_cast; ring_nf; exact le_rfl
    -- Bound 3: One-sided coupling for BOTH `sel = false` and `sel = true`!
    have hcoupled : ∀ (sel : Bool) (p : Output → Prop),
        Pr{let z ← flagStaged sel}[p z.1 ∧ z.2 = false] ≤ Pr{let x ← staged perm sel}[p x] + slackBound ∧
        Pr{let x ← staged perm sel}[p x] ≤ Pr{let z ← flagStaged sel}[p z.1 ∧ z.2 = false] + badBound + slackBound := by
      intro sel p
      have hlo_int :
          Pr{let z ← flagStaged sel}[p z.1 ∧ z.2 = false] ≤
            Pr{let x ← staged perm sel}[p x] + Pr{let t ← treeStaged sel}[t.2.2 = true] :=
        prEvent_bind_le_prEvent_add_prEvent ($ᵗ (Index → Salt121)) _ _ _ _ _ _ fun sHidden =>
          prEvent_bind_le_prEvent_add_prEvent (compressionRun perm adversary.choose ∅) _ _ _ _ _ _ fun r =>
            (cond_one_sided_bounds h768 perm r.2 (if sel then r.1.message₁ else r.1.message₀)
              r.1.positions sHidden (adversary.observe r.1.aux) p).1
      have hhi_int :
          Pr{let x ← staged perm sel}[p x] ≤
            Pr{let z ← flagStaged sel}[p z.1 ∧ z.2 = false] +
            Pr{let z ← flagStaged sel}[z.2 = true] +
            Pr{let t ← treeStaged sel}[t.2.2 = true] :=
        prEvent_bind_le_prEvent_add_two ($ᵗ (Index → Salt121)) _ _ _ _ _ _ _ _ fun sHidden =>
          prEvent_bind_le_prEvent_add_two (compressionRun perm adversary.choose ∅) _ _ _ _ _ _ _ _ fun r =>
            (cond_one_sided_bounds h768 perm r.2 (if sel then r.1.message₁ else r.1.message₀)
              r.1.positions sHidden (adversary.observe r.1.aux) p).2
      exact ⟨hlo_int.trans (add_le_add le_rfl (htree_bad sel)),
        hhi_int.trans (add_le_add (add_le_add le_rfl (hflag_bad sel)) (htree_bad sel))⟩
    -- Bound 4: `measureTVDist (flagStaged false) (flagStaged true)` via `flagCondObs_hybrid_distance`!
    have hflag_tv : measureTVDist (flagStaged false) (flagStaged true) ≤
        (LENGTH : ℝ) * (6 * ((budget + HONEST_TREE_BUDGET + 3 : Nat) : ℝ) / 2 ^ 256) := by
      apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt121)) _ _ (by positivity)
      intro sHidden
      rw [bind_eq_attach_bind (compressionRun perm adversary.choose ∅)]
      rw [bind_eq_attach_bind (compressionRun perm adversary.choose ∅)]
      apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
      rintro ⟨⟨ch, cache⟩, hreach⟩
      obtain ⟨q1, keys, hq1_le, hkeys_le, hcov, hobs_bd⟩ :=
        first_stage_combined_budget perm adversary bounded (ch, cache) hreach
      have hagree : ∀ i ∈ ch.positions, ch.message₀ i = ch.message₁ i :=
        fun i hi => congrFun ch.agree ⟨i, hi⟩
      have hh := flagCondObs_hybrid_distance h768 perm cache keys hcov
        ch.message₀ ch.message₁ ch.positions sHidden hagree (adversary.observe ch.aux) (budget - q1) hobs_bd
      refine hh.trans ?_
      have hle_nat : keys.card + (HONEST_TREE_BUDGET + (budget - q1)) + 3 ≤ budget + HONEST_TREE_BUDGET + 3 := by omega
      have hle_real : ((keys.card + (HONEST_TREE_BUDGET + (budget - q1)) + 3 : Nat) : ℝ) ≤
          ((budget + HONEST_TREE_BUDGET + 3 : Nat) : ℝ) := Nat.cast_le.mpr hle_nat
      gcongr
    -- Combine via `measureTVDist_one_sided_with_slack` + `moon_hiding_121_arithmetic`!
    have h1s := measureTVDist_one_sided_with_slack
      (staged perm false) (staged perm true) (flagStaged false) (flagStaged true)
      badBound slackBound (by unfold badBound; finiteness) (by unfold slackBound; finiteness)
      (fun p => (hcoupled false p).1) (fun p => (hcoupled false p).2)
      (fun p => (hcoupled true p).1) (fun p => (hcoupled true p).2)
    refine h1s.trans ?_
    have hbad_real : badBound.toReal = (budget : ℝ) / 2 ^ 121 := by
      unfold badBound
      simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    have hslack_real : slackBound.toReal =
        (((budget + LENGTH + HONEST_TREE_BUDGET) * LENGTH : Nat) : ℝ) / 2 ^ 192 := by
      unfold slackBound
      simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    rw [hbad_real, hslack_real]
    exact (add_le_add (add_le_add hflag_tv le_rfl) le_rfl).trans (moon_hiding_121_arithmetic budget)

end CommitGolfCandidate
