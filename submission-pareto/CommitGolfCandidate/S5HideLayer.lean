import CommitGolfCandidate.HidingCoordinate
import CommitGolfCandidate.S5PermLayer
import CommitGolfCandidate.S3PermBridge
import CommitGolfCandidate.S3LeafLayout

/-! All unopened leaves at once. In the reference game with uniform nonces, the leaf layer is
the two-call hash `s5SaltFirst` (nonce and tag in the first call) applied to every leaf. The
game is the real leaf layer of `SaltFirst.layer_bound`, with the first stage `adversary.choose`
and a second stage that rebuilds the transcript from the leaf digests and the opened nonces
(group nodes by forward queries on windows whose bits 128..192 are zero, internal nodes with
the fixed compression function) and runs `adversary.observe`. The ideal layer gives every
unopened leaf a uniform digest and does not depend on the unopened values, so the two
messages of a challenge give the same ideal game. Two applications of `layer_bound` bound the
distance of the reference games for the two messages. -/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

variable {S : Type} [Fintype S] [DecidableEq S] {R X C M2 D : Type}

/-! ### Generic facts about strategies and the leaf layer -/

namespace Strat

theorem s5_exp_avg {α κ : Type} (I : Finset κ) (F : κ → α → PState S → ℝ) (st : Strat S α)
    (s : PState S) :
    st.exp s (fun a s' => avg I fun j => F j a s') = avg I fun j => st.exp s (F j) := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih =>
    simp only [exp, ih]
    exact avg_comm _ _ _
  | inv y k ih =>
    simp only [exp, ih]
    exact avg_comm _ _ _
  | rand n k ih =>
    simp only [exp, ih]
    exact avg_comm _ _ _

theorem s5_exp_iidAvg {α ι : Type} [Fintype ι] (st : Strat S α) (s : PState S) :
    ∀ (n : ℕ) (φ : α → PState S → List ι → ℝ),
      st.exp s (fun a s' => iidAvg ι n (φ a s')) = iidAvg ι n fun is => st.exp s fun a s' => φ a s' is
  | 0, _ => rfl
  | n + 1, φ => by
    simp only [iidAvg]
    rw [s5_exp_avg]
    exact avg_congr fun i _ => s5_exp_iidAvg st s n fun a s' is => φ a s' (i :: is)

theorem s5_exp_done {α : Type} (a : α) (s : PState S) (f : α → PState S → ℝ) :
    (Strat.done a : Strat S α).exp s f = f a s := rfl

theorem s5_exp_congr {α : Type} (st : Strat S α) (s : PState S) {f g : α → PState S → ℝ}
    (h : ∀ a s', f a s' = g a s') : st.exp s f = st.exp s g := by
  rw [show f = g from funext fun a => funext fun s' => h a s']

theorem s5_done_bind {α β : Type} (a : α) (f : α → Strat S β) : (Strat.done a).bind f = f a := rfl

theorem s5_bind_assoc {α β γ : Type} (st : Strat S α) (f : α → Strat S β) (g : β → Strat S γ) :
    (st.bind f).bind g = st.bind fun a => (f a).bind g := by
  induction st with
  | done a => rfl
  | fwd x k ih => simp only [bind, ih]
  | inv y k ih => simp only [bind, ih]
  | rand n k ih => simp only [bind, ih]

theorem s5_uniform_bind {α β ι : Type} [Fintype ι] [Nonempty ι] (k : ι → Strat S α)
    (f : α → Strat S β) : (Strat.uniform ι k).bind f = Strat.uniform ι fun i => (k i).bind f := rfl

end Strat

namespace SaltFirst
variable (H : SaltFirst S R X C M2 D)

/-- The layer with given salts, one per leaf in order. -/
def s5LayerWith : List (LeafSpec X M2) → List R → Strat S (List (D × R))
  | [], _ => .done []
  | _ :: _, [] => .done []
  | l :: ls, r :: rs => (H.eval r l).bind fun d =>
      (s5LayerWith ls rs).bind fun out => .done ((d, r) :: out)

/-- The real layer is the average over independent uniform salts of the layer with those salts. -/
theorem s5_layer_real_exp [Fintype R] [Nonempty R] :
    ∀ (ls : List (LeafSpec X M2)) (s : PState S) (g : List (D × R) → PState S → ℝ),
      (H.layerReal ls).exp s g = iidAvg R ls.length fun rs => (H.s5LayerWith ls rs).exp s g
  | [], _, _ => rfl
  | l :: ls, s, g => by
    simp only [layerReal, Strat.exp_uniform, Strat.exp_bind, Strat.s5_exp_done, List.length_cons,
      iidAvg, s5LayerWith]
    refine avg_congr fun r _ => ?_
    simp only [s5_layer_real_exp ls]
    exact Strat.s5_exp_iidAvg (H.eval r l) s ls.length
      (fun d s1 rs => (H.s5LayerWith ls rs).exp s1 fun out s2 => g ((d, r) :: out) s2)

/-- The real layer for a list of known length, as an average over salt tuples. -/
theorem s5_layer_real_avg [Fintype R] [Nonempty R] (ls : List (LeafSpec X M2)) (n : ℕ)
    (length : ls.length = n) (s : PState S) (g : List (D × R) → PState S → ℝ) :
    (H.layerReal ls).exp s g = avg Finset.univ fun v : Fin n → R => (H.s5LayerWith ls (List.ofFn v)).exp s g := by
  subst length
  rw [s5_layer_real_exp, iidAvg_ofFn]

theorem s5_view_cons (l : LeafSpec X M2) (ls : List (LeafSpec X M2)) (p : D × R)
    (out : List (D × R)) :
    view (l :: ls) (p :: out) = (p.1, if l.hidden then none else some p.2) :: view ls out := rfl

/-- Two leaves with the same flag that are equal when opened. -/
def s5SameOpen (l l' : LeafSpec X M2) : Prop := l.hidden = l'.hidden ∧ (l.hidden = false → l = l')

/-- The ideal layer, seen through `view`, reads only the flags and the opened leaves. -/
theorem s5_layer_ideal_congr [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] {β : Type}
    {ls ls' : List (LeafSpec X M2)} (agree : List.Forall₂ s5SameOpen ls ls') :
    ∀ (K : List (D × Option R) → Strat S β),
      (H.layerIdeal ls).bind (fun out => K (view ls out)) =
        (H.layerIdeal ls').bind (fun out => K (view ls' out)) := by
  induction agree with
  | nil => intro K; rfl
  | @cons l l' ls ls' head rest ih =>
    intro K
    obtain ⟨hidden, same⟩ := head
    simp only [layerIdeal, Strat.s5_uniform_bind, Strat.s5_bind_assoc, Strat.bind, s5_view_cons]
    cases flag : l.hidden with
    | false =>
      have equal := same flag
      subst equal
      simp only [flag, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (Strat.uniform R) (funext fun r => congrArg (Strat.bind _)
        (funext fun d => ih fun v => K ((d, some r) :: v)))
    | true =>
      have flag' : l'.hidden = true := hidden ▸ flag
      simp only [flag, flag', ↓reduceIte]
      exact congrArg (Strat.uniform R) (funext fun r => congrArg (Strat.bind _)
        (funext fun d => ih fun v => K ((d, none) :: v)))

end SaltFirst

end CommitGolfCandidate.Permutation

namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance s5HideLayerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation
open Finset

/-! ### Total variation from event probabilities -/

private theorem s5_le_add_ofReal_of_toReal {a b : ENNReal} {ε : ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hε : 0 ≤ ε) (h : a.toReal ≤ b.toReal + ε) : a ≤ b + ENNReal.ofReal ε := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + ε) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal b.toReal + ENNReal.ofReal ε := ENNReal.ofReal_add ENNReal.toReal_nonneg hε
    _ = b + ENNReal.ofReal ε := by rw [ENNReal.ofReal_toReal hb]

/-- Total variation is the largest event discrepancy. -/
theorem s5_tv_le_of_events {α : Type} (mx my : ProbComp α) (ε : ℝ) (nonneg : 0 ≤ ε)
    (close : ∀ event : α → Prop,
      |(prEvent (event <$> mx)).toReal - (prEvent (event <$> my)).toReal| ≤ ε) :
    measureTVDist mx my ≤ ε := by
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  rw [measureETVDist, MeasureTheory.Measure.etvDist]
  refine iSup_le fun set => ?_
  have left := prEvent_eq_evalDist_of_discrete mx (fun value => value ∈ set.1)
  have right := prEvent_eq_evalDist_of_discrete my (fun value => value ∈ set.1)
  simp only [Set.setOf_mem_eq] at left right
  have bound := abs_sub_le_iff.mp (close (fun value => value ∈ set.1))
  rw [← left, ← right, ENNReal.absDiff_le_iff]
  exact ⟨s5_le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg
      (by linarith [bound.1]),
    s5_le_add_ofReal_of_toReal (prEvent_ne_top _) (prEvent_ne_top _) nonneg (by linarith [bound.2])⟩

/-! ### The leaf layer at the final sizes -/

/-- Tag and first message part of a leaf's first window (window bits 128..1600), with a leaf
tag `4072 + 256 i` in its low 64 bits. -/
abbrev S5TaggedX := {x : BitVec 1472 // ∃ i < 2 ^ 24, x.toNat % 2 ^ 64 = 4072 + 256 * i}

/-- The final leaf hash as a salt-first two-call hash: `W1 = nonce | x`, `W2 = chop (P W1) | m`,
digest = low 256 bits of `P W2`. -/
def s5SaltFirst : SaltFirst PermState (BitVec 128) S5TaggedX (BitVec 512) (BitVec 1088) (BitVec 256)
    where
  enc1 p := BitVec.ofNat 1600 (p.1.toNat + p.2.val.toNat * 2 ^ 128)
  enc1_inj := by
    intro a b h
    have e := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at e
    have ha1 := a.1.isLt
    have hb1 := b.1.isLt
    have ha2 := a.2.val.isLt
    have hb2 := b.2.val.isLt
    apply Prod.ext
    · apply BitVec.eq_of_toNat_eq
      omega
    · apply Subtype.ext
      apply BitVec.eq_of_toNat_eq
      omega
  chop o := BitVec.ofNat 512 (o.toNat / 2 ^ 1088)
  enc2 p := BitVec.ofNat 1600 (p.1.toNat + p.2.toNat * 2 ^ 512)
  enc2_inj := by
    intro a b h
    have e := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at e
    have ha1 := a.1.isLt
    have hb1 := b.1.isLt
    have ha2 := a.2.isLt
    have hb2 := b.2.isLt
    apply Prod.ext
    · apply BitVec.eq_of_toNat_eq
      omega
    · apply BitVec.eq_of_toNat_eq
      omega
  trunc o := BitVec.ofNat 256 o.toNat

/-- The first-call part of a tagged leaf after its nonce: the tag, then leaf bytes 0..176. -/
def s5HideX (index : Index) (value : Entry) : BitVec 1472 :=
  BitVec.ofNat 1472 (s6Tag index + (value.toNat % 2 ^ 1408) * 2 ^ 64)

/-- The second message part of a leaf: leaf bytes 120..256. -/
def s5HideM (value : Entry) : BitVec 1088 := BitVec.ofNat 1088 (value.toNat / 2 ^ 960)

theorem s5_hide_index_lt (index : Index) : index.val < 2 ^ 24 := index.isLt

theorem s5_hide_x_tag (index : Index) (value : Entry) :
    (s5HideX index value).toNat % 2 ^ 64 = s6Tag index := by
  have hi := s5_hide_index_lt index
  have hvalue : value.toNat < 2 ^ 2048 := value.isLt
  simp only [s5HideX, s6Tag, BitVec.toNat_ofNat]
  omega

theorem s5_hide_x_index {index index' : Index} {value value' : Entry}
    (h : s5HideX index value = s5HideX index' value') : index = index' := by
  have e := congrArg (fun x : BitVec 1472 => x.toNat % 2 ^ 64) h
  simp only [s5_hide_x_tag, s6Tag] at e
  exact Fin.ext (by omega)

theorem s5_hide_group_tag (d0 d1 d2 d3 : BitVec 256) :
    (s6GroupInput d0 d1 d2 d3).toNat / 2 ^ 128 % 2 ^ 64 = 0 := by
  simp only [s6GroupInput, BitVec.toNat_ofNat, PERMUTATION_WIDTH]
  omega

/-- A state is shaped when its bits 128..192 hold a leaf tag. -/
def s5Shape (s : PermState) : Prop := ∃ i < 2 ^ 24, s.toNat / 2 ^ 128 % 2 ^ 64 = 4072 + 256 * i

theorem s5_shape_enc1 (r : BitVec 128) (x : S5TaggedX) : s5Shape (s5SaltFirst.enc1 (r, x)) := by
  obtain ⟨i, inside, tag⟩ := x.property
  refine ⟨i, inside, ?_⟩
  have hr := r.isLt
  have hx := x.val.isLt
  change (BitVec.ofNat 1600 (r.toNat + x.val.toNat * 2 ^ 128)).toNat / 2 ^ 128 % 2 ^ 64 = _
  rw [BitVec.toNat_ofNat]
  omega

theorem s5_group_unshaped (d0 d1 d2 d3 : Digest) : ¬ s5Shape (s6GroupInput d0 d1 d2 d3) := by
  rintro ⟨i, _, tag⟩
  rw [s5_hide_group_tag] at tag
  omega

theorem s5_trunc_regular (d : BitVec 256) :
    (Finset.univ.filter fun s : PermState => s5SaltFirst.trunc s = d).card = 2 ^ 1344 :=
  s3_trunc_exact d

theorem s5_chop_fiber (c : BitVec 512) :
    (Finset.univ.filter fun s : PermState => s5SaltFirst.chop s = c).card ≤ 2 ^ 1088 :=
  s3_chop_fiber c

/-- The `x` part of leaf `index` with value `value`. -/
def s5TaggedLeaf (index : Index) (value : Entry) : S5TaggedX :=
  ⟨s5HideX index value, index.val, s5_hide_index_lt index, by rw [s5_hide_x_tag]; rfl⟩

def s5Spec (index : Index) (value : Entry) (hidden : Bool) : LeafSpec S5TaggedX (BitVec 1088) :=
  ⟨s5TaggedLeaf index value, s5HideM value, hidden⟩

/-- The leaves of the tree in position order; unopened leaves are hidden. -/
def s5Specs (message : Message) (positions : Positions) : List (LeafSpec S5TaggedX (BitVec 1088)) :=
  (List.finRange LENGTH).map fun index => s5Spec index (message index) (decide (index ∉ positions))

theorem s5_specs_length (message : Message) (positions : Positions) :
    (s5Specs message positions).length = LENGTH := by
  rw [s5Specs, List.length_map, List.length_finRange]

theorem s5_specs_getElem (message : Message) (positions : Positions) (j : Nat)
    (inside : j < (s5Specs message positions).length) :
    (s5Specs message positions)[j] =
      s5Spec ⟨j, by rwa [s5_specs_length] at inside⟩ (message ⟨j, by rwa [s5_specs_length] at inside⟩)
        (decide ((⟨j, by rwa [s5_specs_length] at inside⟩ : Index) ∉ positions)) := by
  simp only [s5Specs, List.getElem_map, List.getElem_finRange]
  rfl

theorem s5_specs_nodup (message : Message) (positions : Positions) :
    ((s5Specs message positions).map LeafSpec.x).Nodup := by
  unfold s5Specs
  rw [List.map_map]
  refine (List.nodup_finRange LENGTH).map ?_
  intro index index' equal
  have values := congrArg Subtype.val equal
  exact s5_hide_x_index values

theorem s5_specs_same (message message' : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, message index = message' index) :
    List.Forall₂ SaltFirst.s5SameOpen (s5Specs message positions) (s5Specs message' positions) := by
  unfold s5Specs
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro index _
  refine ⟨rfl, fun opened => ?_⟩
  have member : index ∈ positions := by
    by_contra absent
    simp [s5Spec, absent] at opened
  simp only [s5Spec, agree index member]

attribute [irreducible] s5Specs

theorem s5_enc1_leaf (index : Index) (value : Entry) (nonce : BitVec 128) :
    s5SaltFirst.enc1 (nonce, s5TaggedLeaf index value) = s3First (expandTagged index nonce) value := by
  have hi := s5_hide_index_lt index
  have hn := nonce.isLt
  have hvalue : value.toNat < 2 ^ 2048 := value.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [s5SaltFirst, s5TaggedLeaf, s5HideX, s3First, expandTagged, s6Tag, BitVec.toNat_ofNat,
    PERMUTATION_WIDTH]
  omega

theorem s5_enc2_leaf (reply : PermState) (value : Entry) :
    s5SaltFirst.enc2 (s5SaltFirst.chop reply, s5HideM value) = s3Second reply value := by
  have hreply : reply.toNat < 2 ^ 1600 := reply.isLt
  have hvalue : value.toNat < 2 ^ 2048 := value.isLt
  have h1 : reply.toNat / 2 ^ 1088 % 2 ^ 512 = reply.toNat / 2 ^ 1088 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hreply))
  have h2 : value.toNat / 2 ^ 960 % 2 ^ 1088 = value.toNat / 2 ^ 960 :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hvalue))
  simp only [s5SaltFirst, s5HideM, s3Second, BitVec.toNat_ofNat, h1, h2]
  rfl

/-- The digest of a leaf spec under a fixed permutation. -/
def s5Digest (permutation : Perm) (l : LeafSpec S5TaggedX (BitVec 1088)) (r : BitVec 128) : Digest :=
  s5SaltFirst.trunc (permutation (s5SaltFirst.enc2
    (s5SaltFirst.chop (permutation (s5SaltFirst.enc1 (r, l.x))), l.m)))

theorem s5_digest_spec (permutation : Perm) (index : Index) (value : Entry) (hidden : Bool)
    (nonce : BitVec 128) :
    s5Digest permutation (s5Spec index value hidden) nonce =
      s3LeafDigest permutation (expandTagged index nonce) value := by
  unfold s5Digest s5Spec
  simp only
  rw [s5_enc1_leaf, s5_enc2_leaf]
  rfl

/-! ### The real layer through the oracle -/

/-- Every leaf in order: a forward query on its first window, then one on its second window. -/
def s5QueryLayer : List (LeafSpec S5TaggedX (BitVec 1088)) → List (BitVec 128) →
    OracleComp World (List (Digest × BitVec 128))
  | [], _ => pure []
  | _ :: _, [] => pure []
  | l :: ls, r :: rs => s5Forward (s5SaltFirst.enc1 (r, l.x)) >>= fun first =>
      s5Forward (s5SaltFirst.enc2 (s5SaltFirst.chop first, l.m)) >>= fun second =>
        s5QueryLayer ls rs >>= fun out => pure ((s5SaltFirst.trunc second, r) :: out)

theorem to_strat_s5_forward (compression : Compression) (input : PermState) {α : Type}
    (next : PermState → OracleComp World α) :
    toStrat compression (s5Forward input >>= next) =
      Strat.fwd input fun answer => toStrat compression (next answer) := rfl

theorem to_strat_s5_compress (compression : Compression) (input : BitVec (256 + 256)) {α : Type}
    (next : Digest → OracleComp World α) :
    toStrat compression (s5Compress input >>= next) = toStrat compression (next (compression input)) :=
  rfl

theorem to_strat_s5_query_layer (compression : Compression) :
    ∀ (ls : List (LeafSpec S5TaggedX (BitVec 1088))) (rs : List (BitVec 128)),
      toStrat compression (s5QueryLayer ls rs) = s5SaltFirst.s5LayerWith ls rs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l :: ls, r :: rs => by
    simp only [s5QueryLayer, to_strat_s5_forward, to_strat_bind, to_strat_pure,
      to_strat_s5_query_layer compression ls rs]
    rfl

theorem fixed_s5_query_layer (oracle : Oracle) {α : Type} :
    ∀ (ls : List (LeafSpec S5TaggedX (BitVec 1088))) (rs : List (BitVec 128))
      (next : List (Digest × BitVec 128) → OracleComp World α),
      fixedOracleRun oracle (s5QueryLayer ls rs >>= next) =
        fixedOracleRun oracle (next (List.zipWith (fun l r => (s5Digest oracle.permutation l r, r)) ls rs))
  | [], _, next => by rw [s5QueryLayer, pure_bind]; rfl
  | _ :: _, [], next => by rw [s5QueryLayer, pure_bind]; rfl
  | l :: ls, r :: rs, next => by
    simp only [s5QueryLayer, bind_assoc]
    rw [fixed_s5_forward, fixed_s5_forward, fixed_s5_query_layer oracle ls rs]
    simp only [pure_bind, List.zipWith_cons_cons]
    rfl

/-! ### What the second stage sees, for the real layer -/

attribute [local irreducible] List.ofFn List.finRange

/-- Leaf digests from a view (zero outside it). -/
def s5ViewLeaf (view : List (Digest × Option (BitVec 128))) (index : Nat) : Digest :=
  (view.getD index (0, none)).1

/-- The salt field of an opened leaf from a view (zero for an unopened one). -/
def s5ViewSalt (view : List (Digest × Option (BitVec 128))) (index : Index) : Digest :=
  match (view.getD index.val (0, none)).2 with
  | some nonce => expandTagged index nonce
  | none => 0

theorem s5_view_leaf_apply (view : List (Digest × Option (BitVec 128))) (index : Nat) :
    s5ViewLeaf view index = (view.getD index (0, none)).1 := rfl

theorem s5_view_salt_apply (view : List (Digest × Option (BitVec 128))) (index : Index) :
    s5ViewSalt view index = match (view.getD index.val (0, none)).2 with
      | some nonce => expandTagged index nonce
      | none => 0 := rfl

theorem s5_real_view (permutation : Perm) (message : Message) (positions : Positions)
    (nonce : Index → Nonce128) (j : Nat) :
    (SaltFirst.view (s5Specs message positions)
        (List.zipWith (fun l r => (s5Digest permutation l r, r)) (s5Specs message positions)
          (List.ofFn nonce))).getD j (0, none) =
      if inside : j < LENGTH then
        (s3LeafDigest permutation (expandTagged ⟨j, inside⟩ (nonce ⟨j, inside⟩)) (message ⟨j, inside⟩),
          if (⟨j, inside⟩ : Index) ∉ positions then none else some (nonce ⟨j, inside⟩))
      else (0, none) := by
  unfold SaltFirst.view
  split
  · rename_i inside
    have length : (List.zipWith (fun l p => (p.1, if l.hidden then none else some p.2))
        (s5Specs message positions) (List.zipWith (fun l r => (s5Digest permutation l r, r))
          (s5Specs message positions) (List.ofFn nonce))).length = LENGTH := by
      simp only [List.length_zipWith, s5_specs_length, List.length_ofFn, min_self]
    rw [List.getD_eq_getElem _ _ (by rw [length]; exact inside), List.getElem_zipWith,
      List.getElem_zipWith, List.getElem_ofFn, s5_specs_getElem]
    rw [s5_digest_spec]
    simp only [s5Spec, decide_eq_true_eq]
  · rename_i outside
    rw [List.getD_eq_default _ _ (by
      simp only [List.length_zipWith, s5_specs_length, List.length_ofFn, min_self]
      omega)]

theorem s5_real_view_leaf (permutation : Perm) (message : Message) (positions : Positions)
    (nonce : Index → Nonce128) :
    s5ViewLeaf (SaltFirst.view (s5Specs message positions)
        (List.zipWith (fun l r => (s5Digest permutation l r, r)) (s5Specs message positions)
          (List.ofFn nonce))) =
      s6LeafValues permutation message (expandTaggedVector nonce) := by
  funext j
  rw [s5_view_leaf_apply, s5_real_view, s6LeafValues]
  by_cases inside : j < LENGTH
  · rw [dif_pos inside, dif_pos inside]
    rfl
  · rw [dif_neg inside, dif_neg inside]

theorem s5_real_view_salt (permutation : Perm) (message : Message) (positions : Positions)
    (nonce : Index → Nonce128) (index : Index) (opened : index ∈ positions) :
    s5ViewSalt (SaltFirst.view (s5Specs message positions)
        (List.zipWith (fun l r => (s5Digest permutation l r, r)) (s5Specs message positions)
          (List.ofFn nonce))) index =
      expandTaggedVector nonce index := by
  rw [s5_view_salt_apply, s5_real_view, dif_pos index.isLt]
  have member : (⟨index.val, index.isLt⟩ : Index) ∈ positions := opened
  rw [if_neg (not_not.mpr member)]
  rfl

/-! ### The two stages -/

variable {State Output : Type} {openingSize : Nat}

/-- Second stage: the transcript from the view, then the observer. -/
def s5Next (adversary : Hiding.HidingAdversary State Output openingSize)
    (challenge : Hiding.HidingChallenge State openingSize)
    (view : List (Digest × Option (BitVec 128))) : OracleComp World Output :=
  s5QueryTail (s5ViewLeaf view) (s5ViewSalt view) challenge.positions >>= fun transcript =>
    adversary.observe challenge.aux transcript.1 transcript.2

/-- The reference game for one nonce vector, as a single oracle computation. -/
def s5RealComp (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) (nonce : Index → Nonce128) :
    OracleComp World Output :=
  adversary.choose >>= fun challenge =>
    s5QueryLayer (s5Specs (message challenge) challenge.positions) (List.ofFn nonce) >>= fun out =>
      s5Next adversary challenge (SaltFirst.view (s5Specs (message challenge) challenge.positions) out)

theorem fixed_s5_real_comp (compression : Compression) (permutation : Perm)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) (nonce : Index → Nonce128) :
    fixedOracleRun ⟨compression, permutation⟩ (s5RealComp adversary message nonce) =
      (fixedOracleRun ⟨compression, permutation⟩ adversary.choose >>= fun challenge =>
        observeTranscript ⟨compression, permutation⟩ (message challenge) (expandTaggedVector nonce)
          challenge.positions (adversary.observe challenge.aux)) := by
  rw [s5RealComp, fixed_oracle_run_bind]
  refine bind_congr fun challenge => ?_
  rw [fixed_s5_query_layer, s5Next, fixed_oracle_run_bind, fixed_s5_query_tail, pure_bind, s5_real_view_leaf,
    s6_transcript_of_salt_congr compression _ _ _ (expandTaggedVector nonce) _
      (s5_real_view_salt _ (message challenge) challenge.positions nonce)]
  rfl

/-- First stage of the lazy-model game: the challenge and the leaf list of the message. -/
noncomputable def s5A1 (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) :
    Strat PermState (List (LeafSpec S5TaggedX (BitVec 1088)) × Hiding.HidingChallenge State openingSize) :=
  (toStrat compression adversary.choose).bind fun challenge =>
    .done (s5Specs (message challenge) challenge.positions, challenge)

open Classical in
/-- Second stage of the lazy-model game, reporting whether the event holds. -/
noncomputable def s5A2 (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize) (event : Output → Prop)
    (challenge : Hiding.HidingChallenge State openingSize)
    (view : List (Digest × Option (BitVec 128))) : Strat PermState Bool :=
  (toStrat compression (s5Next adversary challenge view)).bind fun output => .done (decide (event output))

/-- The real lazy-model game for one message. -/
noncomputable def s5RealStrat (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) (event : Output → Prop) :
    Strat PermState Bool :=
  (s5A1 compression adversary message).bind fun a =>
    (s5SaltFirst.layerReal a.1).bind fun out => s5A2 compression adversary event a.2 (SaltFirst.view a.1 out)

/-- The ideal lazy-model game for one message. -/
noncomputable def s5IdealStrat (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) (event : Output → Prop) :
    Strat PermState Bool :=
  (s5A1 compression adversary message).bind fun a =>
    (s5SaltFirst.layerIdeal a.1).bind fun out => s5A2 compression adversary event a.2 (SaltFirst.view a.1 out)

theorem s5_real_comp_prob (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) (event : Output → Prop) :
    avg univ (fun nonce : Index → Nonce128 =>
        (toStrat compression (s5RealComp adversary message nonce)).prob PState.init
          fun output _ => event output) =
      (s5RealStrat compression adversary message event).prob PState.init (fun b _ => b = true) := by
  classical
  have right : (s5RealStrat compression adversary message event).prob PState.init
      (fun b _ => b = true) =
      (toStrat compression adversary.choose).exp PState.init (fun challenge s =>
        avg univ fun nonce : Fin LENGTH → BitVec 128 =>
          (s5SaltFirst.s5LayerWith (s5Specs (message challenge) challenge.positions)
            (List.ofFn nonce)).exp s fun out s' =>
              (s5A2 compression adversary event challenge
                (SaltFirst.view (s5Specs (message challenge) challenge.positions) out)).exp s'
                fun b _ => ind (b = true)) := by
    rw [s5RealStrat, s5A1, Strat.prob, Strat.exp_bind, Strat.exp_bind]
    refine Strat.s5_exp_congr _ _ fun challenge s => ?_
    rw [Strat.s5_exp_done, Strat.exp_bind]
    exact SaltFirst.s5_layer_real_avg s5SaltFirst _ LENGTH (s5_specs_length _ _) s _
  have left (nonce : Index → Nonce128) :
      (toStrat compression (s5RealComp adversary message nonce)).prob PState.init
        (fun output _ => event output) =
      (toStrat compression adversary.choose).exp PState.init (fun challenge s =>
        (s5SaltFirst.s5LayerWith (s5Specs (message challenge) challenge.positions)
          (List.ofFn nonce)).exp s fun out s' =>
            (s5A2 compression adversary event challenge
              (SaltFirst.view (s5Specs (message challenge) challenge.positions) out)).exp s'
              fun b _ => ind (b = true)) := by
    rw [s5RealComp, Strat.prob, to_strat_bind, Strat.exp_bind]
    refine Strat.s5_exp_congr _ _ fun challenge s => ?_
    rw [to_strat_bind, to_strat_s5_query_layer, Strat.exp_bind]
    refine Strat.s5_exp_congr _ _ fun out s' => ?_
    rw [s5A2, Strat.exp_bind]
    refine Strat.s5_exp_congr _ _ fun output s'' => ?_
    rw [Strat.s5_exp_done, decide_eq_true_eq]
  rw [right, Strat.s5_exp_avg]
  exact avg_congr fun nonce _ => left nonce

/-- The real game as an event probability of the lazy-model game. -/
theorem s5_real_game_event (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) (event : Output → Prop) :
    prEvent (event <$> (do
        let permutation ← $ᵗ Perm
        let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
        let nonce ← $ᵗ (Index → Nonce128)
        observeTranscript ⟨compression, permutation⟩ (message challenge) (expandTaggedVector nonce)
          challenge.positions (adversary.observe challenge.aux))) =
      ENNReal.ofReal ((s5RealStrat compression adversary message event).prob PState.init
        fun b _ => b = true) := by
  have reordered : 𝒟[do
        let permutation ← $ᵗ Perm
        let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
        let nonce ← $ᵗ (Index → Nonce128)
        observeTranscript ⟨compression, permutation⟩ (message challenge) (expandTaggedVector nonce)
          challenge.positions (adversary.observe challenge.aux)] =
      𝒟[do let nonce ← $ᵗ (Index → Nonce128)
           let permutation ← $ᵗ Perm
           fixedOracleRun ⟨compression, permutation⟩ (s5RealComp adversary message nonce)] := by
    simp only [fixed_s5_real_comp]
    trans 𝒟[do let permutation ← $ᵗ Perm
                let nonce ← $ᵗ (Index → Nonce128)
                let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
                observeTranscript ⟨compression, permutation⟩ (message challenge)
                  (expandTaggedVector nonce) challenge.positions (adversary.observe challenge.aux)]
    · apply _root_.evalDist_bind_congr
      intro permutation
      exact (distribution_bind_comm ($ᵗ (Index → Nonce128))
        (fixedOracleRun ⟨compression, permutation⟩ adversary.choose) _).symm
    · exact distribution_bind_comm ($ᵗ Perm) ($ᵗ (Index → Nonce128)) _
  rw [(EvalDistEq.of_evalDist_eq reordered).prEvent_eq event, ← s5_real_comp_prob]
  rw [prEvent_bind_eq_sum_fintype, ← sum_inv_card_mul_ofReal _ fun nonce => Strat.prob_nonneg _ _ _]
  refine Finset.sum_congr rfl fun nonce _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, perm_sampling_prob]

/-- The ideal game does not depend on the unopened values. -/
theorem s5_ideal_same (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize) (event : Output → Prop) :
    s5IdealStrat compression adversary (fun challenge => challenge.message₀) event =
      s5IdealStrat compression adversary (fun challenge => challenge.message₁) event := by
  have agree (challenge : Hiding.HidingChallenge State openingSize) :
      List.Forall₂ SaltFirst.s5SameOpen (s5Specs challenge.message₀ challenge.positions)
        (s5Specs challenge.message₁ challenge.positions) :=
    s5_specs_same challenge.message₀ challenge.message₁ challenge.positions
      fun index opened => congrFun challenge.agree ⟨index, opened⟩
  rw [s5IdealStrat, s5IdealStrat, s5A1, s5A1, Strat.s5_bind_assoc, Strat.s5_bind_assoc]
  refine congrArg (Strat.bind _) (funext fun challenge => ?_)
  rw [Strat.s5_done_bind, Strat.s5_done_bind]
  exact SaltFirst.s5_layer_ideal_congr s5SaltFirst (agree challenge) (s5A2 compression adversary event challenge)

/-! ### One application of the layer bound -/

theorem s5_card_bitvec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

theorem s5_fqb_groups (compression : Compression) (leaf : Nat → Digest) {α : Type}
    (next : (Nat → Digest) → OracleComp World α) (budget : Nat)
    (bounded : ∀ heap, (toStrat compression (next heap)).FQB s5Shape budget) :
    ∀ (count : Nat) (heap : Nat → Digest),
      (toStrat compression (s5QueryGroups leaf count heap >>= next)).FQB s5Shape budget
  | 0, heap => by
    rw [s5QueryGroups, pure_bind]
    exact bounded heap
  | count+1, heap => by
    rw [s5QueryGroups, bind_assoc]
    unfold s5QueryGroup
    simp only [bind_assoc, pure_bind]
    rw [to_strat_s5_forward]
    exact Strat.FQB_fwd_of_not (s5_group_unshaped _ _ _ _) fun _ =>
      s5_fqb_groups compression leaf next budget bounded count _

theorem s5_fqb_parents (compression : Compression) {α : Type}
    (next : (Nat → Digest) → OracleComp World α) (budget : Nat)
    (bounded : ∀ heap, (toStrat compression (next heap)).FQB s5Shape budget) :
    ∀ (count : Nat) (heap : Nat → Digest),
      (toStrat compression (s5QueryParents count heap >>= next)).FQB s5Shape budget
  | 0, heap => by
    rw [s5QueryParents, pure_bind]
    exact bounded heap
  | count+1, heap => by
    rw [s5QueryParents, bind_assoc, to_strat_s5_compress]
    exact s5_fqb_parents compression next budget bounded count _

theorem s5_fqb_tail_gen (compression : Compression) (leaf : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) {α : Type} (next : Commitment × Proof → OracleComp World α) (budget : Nat)
    (bounded : ∀ transcript, (toStrat compression (next transcript)).FQB s5Shape budget)
    (groupCount parentCount : Nat) (start : Nat → Digest) :
    (toStrat compression ((s5QueryGroups leaf groupCount start >>= fun groups =>
      s5QueryParents parentCount groups >>= fun heap =>
        pure (s5TreeTranscript heap leaf salt positions)) >>= next)).FQB s5Shape budget := by
  rw [bind_assoc]
  refine s5_fqb_groups compression leaf _ budget (fun groups => ?_) groupCount start
  rw [bind_assoc]
  refine s5_fqb_parents compression _ budget (fun heap => ?_) parentCount groups
  rw [pure_bind]
  exact bounded _

theorem s5_fqb_tail (compression : Compression) (leaf : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) {α : Type} (next : Commitment × Proof → OracleComp World α) (budget : Nat)
    (bounded : ∀ transcript, (toStrat compression (next transcript)).FQB s5Shape budget) :
    (toStrat compression (s5QueryTail leaf salt positions >>= next)).FQB s5Shape budget := by
  rw [s5QueryTail]
  exact s5_fqb_tail_gen compression leaf salt positions next budget bounded (2^22) (2^22-1) fun _ => 0

theorem s5_a2_bounds (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (event : Output → Prop) (challenge : Hiding.HidingChallenge State openingSize)
    (view : List (Digest × Option (BitVec 128))) :
    (s5A2 compression adversary event challenge view).QB (2 ^ 23 + budget) ∧
      (s5A2 compression adversary event challenge view).FQB s5Shape budget := by
  classical
  constructor
  · exact (to_strat_QB compression (public_query_bound_bind (s5_query_tail_bound _ _ _)
      fun transcript => observeBound challenge.aux transcript.1 transcript.2)).bind
        fun _ => Strat.QB.done _ 0
  · refine Strat.FQB.bind (m := 0) ?_ (fun _ => trivial)
    exact s5_fqb_tail compression _ _ _ _ budget fun transcript =>
      Strat.FQB_of_QB (to_strat_QB compression
        (observeBound challenge.aux transcript.1 transcript.2))

theorem s5_a1_bounds (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (message : Hiding.HidingChallenge State openingSize → Message) :
    (s5A1 compression adversary message).QB budget ∧
      (s5A1 compression adversary message).post PState.init fun a _ =>
        a.1.length ≤ LENGTH ∧ (a.1.map LeafSpec.x).Nodup := by
  constructor
  · exact (to_strat_QB compression chooseBound).bind fun _ => Strat.QB.done _ 0
  · refine Strat.post_bind (Strat.post_mono (fun challenge _ _ => ?_)
      (Strat.post_suffix (toStrat compression adversary.choose) PState.init))
    exact ⟨le_of_eq (s5_specs_length _ _), s5_specs_nodup _ _⟩

theorem s5_layer_arith (budget : Nat) (small : budget < 2 ^ 125) :
    2 * ((budget + budget : ℕ) : ℝ) / (Fintype.card (BitVec 128) : ℝ) +
        8 * (LENGTH : ℝ) * ((budget + (2 ^ 23 + budget) + 2 * LENGTH : ℕ) : ℝ) *
          (((2 ^ 1088 : ℕ) : ℝ) + (Fintype.card (BitVec 256) : ℝ)) / (Fintype.card PermState : ℝ) ≤
      4 * (budget : ℝ) / 2 ^ 128 + 1 / 2 ^ 131 := by
  rw [s5_card_bitvec, s5_card_bitvec, show Fintype.card PermState = 2 ^ 1600 from s5_card_bitvec _]
  have hb : (budget : ℝ) < 2 ^ 125 := by exact_mod_cast small
  have hb0 : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have first : 2 * ((budget + budget : ℕ) : ℝ) / ((2 ^ 128 : ℕ) : ℝ) = 4 * (budget : ℝ) / 2 ^ 128 := by
    push_cast
    ring
  have count : ((budget + (2 ^ 23 + budget) + 2 * LENGTH : ℕ) : ℝ) ≤ 2 ^ 127 := by
    push_cast
    norm_num [LENGTH, LOG_LENGTH]
    linarith
  have count0 : (0 : ℝ) ≤ ((budget + (2 ^ 23 + budget) + 2 * LENGTH : ℕ) : ℝ) := Nat.cast_nonneg _
  have length : (LENGTH : ℝ) = 2 ^ 24 := by norm_num [LENGTH, LOG_LENGTH]
  have second : 8 * (LENGTH : ℝ) * ((budget + (2 ^ 23 + budget) + 2 * LENGTH : ℕ) : ℝ) *
      (((2 ^ 1088 : ℕ) : ℝ) + ((2 ^ 256 : ℕ) : ℝ)) / ((2 ^ 1600 : ℕ) : ℝ) ≤ 1 / 2 ^ 131 := by
    rw [length]
    calc 8 * (2 : ℝ) ^ 24 * ((budget + (2 ^ 23 + budget) + 2 * LENGTH : ℕ) : ℝ) *
          (((2 ^ 1088 : ℕ) : ℝ) + ((2 ^ 256 : ℕ) : ℝ)) / ((2 ^ 1600 : ℕ) : ℝ) ≤
        8 * (2 : ℝ) ^ 24 * 2 ^ 127 * (((2 ^ 1088 : ℕ) : ℝ) + ((2 ^ 256 : ℕ) : ℝ)) /
          ((2 ^ 1600 : ℕ) : ℝ) := by gcongr
      _ ≤ 1 / 2 ^ 131 := by norm_num
  rw [first]
  linarith

theorem s5_layer_step (compression : Compression)
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (message : Hiding.HidingChallenge State openingSize → Message) (event : Output → Prop)
    (small : budget < 2 ^ 125) :
    |(s5RealStrat compression adversary message event).prob PState.init (fun b _ => b = true) -
        (s5IdealStrat compression adversary message event).prob PState.init (fun b _ => b = true)| ≤
      4 * (budget : ℝ) / 2 ^ 128 + 1 / 2 ^ 131 := by
  obtain ⟨firstBound, listed⟩ := s5_a1_bounds compression adversary budget chooseBound message
  have bound := s5SaltFirst.layer_bound (2 ^ 1344) (2 ^ 1088) s5_trunc_regular s5_chop_fiber
    s5Shape s5_shape_enc1 (s5A1 compression adversary message) (s5A2 compression adversary event)
    LENGTH budget budget (2 ^ 23 + budget) firstBound listed
    (s5_a2_bounds compression adversary budget observeBound event)
  exact bound.trans (s5_layer_arith budget small)

/-! ### All unopened leaves at once -/

/-- Hiding of the reference game with uniform nonces: all unopened leaves at once. -/
theorem hiding_game_distance (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget) :
    measureTVDist (hidingGame adversary fun challenge => challenge.message₀)
      (hidingGame adversary fun challenge => challenge.message₁) ≤ 8 * (budget : ℝ) / 2 ^ 128 + 1 / 2 ^ 130 := by
  by_cases small : budget < 2 ^ 125
  · unfold hidingGame
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro compression
    apply s5_tv_le_of_events _ _ _ (by positivity)
    intro event
    rw [s5_real_game_event, s5_real_game_event, ENNReal.toReal_ofReal (Strat.prob_nonneg _ _ _),
      ENNReal.toReal_ofReal (Strat.prob_nonneg _ _ _)]
    have left := s5_layer_step compression adversary budget chooseBound observeBound
      (fun challenge => challenge.message₀) event small
    have right := s5_layer_step compression adversary budget chooseBound observeBound
      (fun challenge => challenge.message₁) event small
    rw [s5_ideal_same] at left
    have half : (1 : ℝ) / 2 ^ 131 + 1 / 2 ^ 131 = 1 / 2 ^ 130 := by norm_num
    rw [abs_le] at left right ⊢
    constructor <;> linarith [left.1, left.2, right.1, right.2]
  · refine (measureTVDist_le_one _ _).trans ?_
    have big : (2 : ℝ) ^ 125 ≤ budget := by exact_mod_cast not_lt.mp small
    have scale : (2 : ℝ) ^ 128 = 8 * 2 ^ 125 := by norm_num
    have one : (1 : ℝ) ≤ 8 * (budget : ℝ) / 2 ^ 128 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have tail : (0 : ℝ) ≤ 1 / 2 ^ 130 := by positivity
    linarith

end CommitGolfCandidate
