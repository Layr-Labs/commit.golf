import CommitGolfCandidate.PermLean.Bridge

/-! # PL-B permutation leaf: first-occurrence analysis, hazard sizes, budget, detector

Layout (little-endian bytes, byte `j` = bits `[8j, 8j+8)`), for the
256-byte value `m`, the 16-byte salt `s` and the 8-byte tag `T` (`LE64(4096 + 256 i + 56)` at
position `i`; any `T` here):

* `X = 0^8 ‖ m[0..192)`, `y₁ = P X`,
* `W = T ‖ y₁[168..200) ‖ s ‖ m[112..256)` (32-byte link; `m[112..192)`, 80 bytes, is read by
  both calls),
* digest `P(W)[0..32)`, used directly as the leaf of the compression tree.

The case analysis is the generic `Layout.chain_collision` of `Leaf.lean` with the slices of `vB`:
digest `y[0..32)`, link `y₁[168..200)` / `W[8..40)`, and as overlap the 32 bytes `m[112..144)`,
i.e. `X[120..152)` / `W[56..88)` (the other 48 shared bytes are not needed). Every hazard is a
256-bit condition, so the hazard sets have the same bound `(3k+1)·2^1344` as PL-A and the budget is
`leaf_budget` verbatim. The tag is not used by the binding proof. -/

namespace PermLean
open CommitGolf OracleComp
open scoped ENNReal

/-! ## Bit access -/

theorem bit_low {n m : ℕ} (a : BitVec n) (b : BitVec m) {i : ℕ} (h : i < m) :
    (a ++ b).getLsbD i = b.getLsbD i := by
  simp [BitVec.getLsbD_append, h]

theorem bit_high {n m : ℕ} (a : BitVec n) (b : BitVec m) {i : ℕ} (h : m ≤ i) :
    (a ++ b).getLsbD i = a.getLsbD (i - m) := by
  simp [BitVec.getLsbD_append, Nat.not_lt.mpr h]

theorem bit_extract {n : ℕ} (x : BitVec n) (start len : ℕ) {i : ℕ} (h : i < len) :
    (x.extractLsb' start len).getLsbD i = x.getLsbD (start + i) := by
  simp [h]

theorem bit_index {n : ℕ} (x : BitVec n) {a b : ℕ} (h : a = b) : x.getLsbD a = x.getLsbD b :=
  h ▸ rfl

/-! ## The PL-B chain -/

/-- PL-B slices: digest `y[0..32)`, link `y₁[168..200)` and `W[8..40)`, overlap `X[120..152)` and
`W[56..88)` (both `m[112..144)`). -/
def vB : Layout 256 where
  digest y := y.extractLsb' 0 256
  link₁ y := y.extractLsb' 1344 256
  link₂ x := x.extractLsb' 64 256
  overlap₁ x := x.extractLsb' 960 256
  overlap₂ x := x.extractLsb' 448 256

/-- First input `X = 0^8 ‖ m[0..192)`. -/
def leafXB1 (m : BitVec 2048) : Word := m.extractLsb' 0 1536 ++ (0 : BitVec 64)

/-- Second input `W = T ‖ y₁[168..200) ‖ s ‖ m[112..256)`. -/
def leafXB2 (T : BitVec 64) (s : BitVec 128) (m : BitVec 2048) (y₁ : Word) : Word :=
  m.extractLsb' 896 1152 ++ s ++ y₁.extractLsb' 1344 256 ++ T

/-- The PL-B leaf digest `P(W)[0..32)`. -/
def leafHashB (σ : Perm) (T : BitVec 64) (s : BitVec 128) (m : BitVec 2048) : BitVec 256 :=
  vB.digest (σ (leafXB2 T s m (σ (leafXB1 m))))

theorem vB_link (T : BitVec 64) (s : BitVec 128) (m : BitVec 2048) (y₁ : Word) :
    vB.link₂ (leafXB2 T s m y₁) = vB.link₁ y₁ := by
  show (m.extractLsb' 896 1152 ++ s ++ y₁.extractLsb' 1344 256 ++ T :
      BitVec (1152 + 128 + 256 + 64)).extractLsb' 64 256 = (y₁ : BitVec 1600).extractLsb' 1344 256
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) only [bit_extract, bit_high, bit_low, Nat.add_sub_cancel_left]

theorem vB_overlap (T : BitVec 64) (s : BitVec 128) (m : BitVec 2048) (y₁ : Word) :
    vB.overlap₂ (leafXB2 T s m y₁) = vB.overlap₁ (leafXB1 m) := by
  show (m.extractLsb' 896 1152 ++ s ++ y₁.extractLsb' 1344 256 ++ T :
      BitVec (1152 + 128 + 256 + 64)).extractLsb' 448 256 =
    (m.extractLsb' 0 1536 ++ (0 : BitVec 64) : BitVec (1536 + 64)).extractLsb' 960 256
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) only [bit_extract, bit_high]
  exact bit_index _ (by omega)

/-- The two permutation inputs determine the value and the salt (whatever the tags). -/
theorem leafB_inputs_injective {m m' : BitVec 2048} {T T' : BitVec 64} {s s' : BitVec 128}
    {y y' : Word} (first : leafXB1 m = leafXB1 m')
    (second : leafXB2 T s m y = leafXB2 T' s' m' y') : m = m' ∧ s = s' := by
  have first' : (m.extractLsb' 0 1536 ++ (0 : BitVec 64) : BitVec (1536 + 64)) =
      (m'.extractLsb' 0 1536 ++ (0 : BitVec 64) : BitVec (1536 + 64)) := first
  have second' : (m.extractLsb' 896 1152 ++ s ++ y.extractLsb' 1344 256 ++ T :
        BitVec (1152 + 128 + 256 + 64)) =
      (m'.extractLsb' 896 1152 ++ s' ++ y'.extractLsb' 1344 256 ++ T' :
        BitVec (1152 + 128 + 256 + 64)) := second
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases low : i < 1536
    · have bit := congrArg (fun w : BitVec (1536 + 64) => w.getLsbD (64 + i)) first'
      simp (disch := omega) only [bit_extract, bit_high, Nat.add_sub_cancel_left,
        Nat.zero_add] at bit
      exact bit
    · have bit := congrArg (fun w : BitVec (1152 + 128 + 256 + 64) => w.getLsbD (i - 448)) second'
      simp (disch := omega) only [bit_extract, bit_high] at bit
      have index : 896 + (i - 448 - 64 - 256 - 128) = i := by omega
      rw [index] at bit
      exact bit
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have bit := congrArg (fun w : BitVec (1152 + 128 + 256 + 64) => w.getLsbD (320 + i)) second'
    simp (disch := omega) only [bit_high, bit_low] at bit
    have index : 320 + i - 64 - 256 = i := by omega
    rw [index] at bit
    exact bit

/-- **PL-B leaf lemma (log form).** Different (value, salt) pairs with equal digests, whose four
permutation evaluations are logged, make the log unclean. -/
theorem leafB_unclean {log : Log Word} (clean : vB.Clean log) {T T' : BitVec 64}
    {s s' : BitVec 128} {m m' : BitVec 2048} (different : (m, s) ≠ (m', s'))
    {e₁ e₂ e₁' e₂' : Entry Word}
    (mem₁ : e₁ ∈ log) (mem₂ : e₂ ∈ log) (mem₁' : e₁' ∈ log) (mem₂' : e₂' ∈ log)
    (in₁ : e₁.input = leafXB1 m) (in₂ : e₂.input = leafXB2 T s m e₁.output)
    (in₁' : e₁'.input = leafXB1 m') (in₂' : e₂'.input = leafXB2 T' s' m' e₁'.output)
    (same : vB.digest e₂.output = vB.digest e₂'.output) : False := by
  refine vB.chain_collision clean mem₁ mem₂ mem₁' mem₂' (by rw [in₂, vB_link])
    (by rw [in₂', vB_link]) (by rw [in₂, in₁, vB_overlap]) (by rw [in₂', in₁', vB_overlap]) ?_ same
  by_contra both
  rw [not_or, not_not, not_not] at both
  obtain ⟨hm, hs⟩ := leafB_inputs_injective (in₁.symm.trans (both.1.trans in₁'))
    (in₂.symm.trans (both.2.trans in₂'))
  exact different (by rw [hm, hs])

/-- **PL-B leaf lemma (oracle form).** For a log consistent with `σ` that contains both chains,
equal digests force equal (value, salt), unless the log is unclean. -/
theorem leafHashB_injective_of_clean {σ : Perm} {log : Log Word} (clean : vB.Clean log)
    (consistent : ∀ e ∈ log, σ e.input = e.output) {T T' : BitVec 64} {s s' : BitVec 128}
    {m m' : BitVec 2048}
    (logged : leafXB1 m ∈ log.inputs ∧ leafXB2 T s m (σ (leafXB1 m)) ∈ log.inputs ∧
      leafXB1 m' ∈ log.inputs ∧ leafXB2 T' s' m' (σ (leafXB1 m')) ∈ log.inputs)
    (same : leafHashB σ T s m = leafHashB σ T' s' m') : (m, s) = (m', s') := by
  by_contra different
  have entry : ∀ x ∈ log.inputs, ∃ e ∈ log, e.input = x ∧ e.output = σ x := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact ⟨e, he, rfl, (consistent e he).symm⟩
  obtain ⟨l₁, l₂, l₁', l₂'⟩ := logged
  obtain ⟨e₁, mem₁, i₁, o₁⟩ := entry _ l₁
  obtain ⟨e₂, mem₂, i₂, o₂⟩ := entry _ l₂
  obtain ⟨e₁', mem₁', i₁', o₁'⟩ := entry _ l₁'
  obtain ⟨e₂', mem₂', i₂', o₂'⟩ := entry _ l₂'
  exact leafB_unclean clean different mem₁ mem₂ mem₁' mem₂' i₁ (by rw [i₂, o₁]) i₁'
    (by rw [i₂', o₁']) (by rw [o₂, o₂']; exact same)

/-! ## Hazard sets and sizes -/

theorem fits_link₂B : 64 + 256 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega
theorem fits_overlap₁B : 960 + 256 ≤ PERMUTATION_WIDTH := by unfold PERMUTATION_WIDTH; omega

open Classical in
theorem forward_card_leB (log : Log Word) :
    (Finset.univ.filter fun y => vB.forwardBad log y).card ≤ (3 * log.length + 1) * wide := by
  classical
  have hA := card_filter_slice_mem PERMUTATION_WIDTH 0 256 fits_digest
    (log.map fun e => vB.digest e.output)
  have hB := card_filter_slice_mem PERMUTATION_WIDTH 1344 256 fits_overlap₁
    (log.map fun e => vB.link₂ e.input)
  have hC := card_filter_slice_mem PERMUTATION_WIDTH 1344 256 fits_overlap₁
    (log.map fun e => vB.link₁ e.output)
  rw [List.length_map, ← wide_eq] at hA hB hC
  have sub : (Finset.univ.filter fun y => vB.forwardBad log y) ⊆
      ((Finset.univ.filter fun x : Word => x.extractLsb' 0 256 ∈
          log.map fun e => vB.digest e.output) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 1344 256 ∈
          log.map fun e => vB.link₂ e.input)) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 1344 256 ∈
          log.map fun e => vB.link₁ e.output) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  calc _ ≤ _ := Finset.card_le_card sub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ log.length * wide + log.length * wide + log.length * wide :=
        Nat.add_le_add (Nat.add_le_add hA hB) hC
    _ ≤ (3 * log.length + 1) * wide := three_slices _ _

open Classical in
theorem inverse_card_leB (log : Log Word) (y : Word) :
    (Finset.univ.filter fun x => vB.inverseBad log y x).card ≤ (3 * log.length + 1) * wide := by
  classical
  have hA := card_extract_fiber PERMUTATION_WIDTH 64 256 fits_link₂B (vB.link₁ y)
  have hB := card_filter_slice_mem PERMUTATION_WIDTH 64 256 fits_link₂B
    (log.map fun e => vB.link₁ e.output)
  have hC := card_filter_slice_mem PERMUTATION_WIDTH 960 256 fits_overlap₁B
    (log.map fun e => vB.overlap₂ e.input)
  have hD := card_filter_slice_mem PERMUTATION_WIDTH 960 256 fits_overlap₁B
    (log.map fun e => vB.overlap₁ e.input)
  rw [← wide_eq] at hA
  rw [List.length_map, ← wide_eq] at hB hC hD
  have sub : (Finset.univ.filter fun x => vB.inverseBad log y x) ⊆
      (((Finset.univ.filter fun x : Word => x.extractLsb' 64 256 = vB.link₁ y) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 64 256 ∈
          log.map fun e => vB.link₁ e.output)) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 960 256 ∈
          log.map fun e => vB.overlap₂ e.input)) ∪
        (Finset.univ.filter fun x : Word => x.extractLsb' 960 256 ∈
          log.map fun e => vB.overlap₁ e.input) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
    rcases hx with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  calc _ ≤ _ := Finset.card_le_card sub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ wide + log.length * wide + log.length * wide + log.length * wide :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA.le hB) hC) hD
    _ ≤ (3 * log.length + 1) * wide := four_slices _ _

open Classical in
/-- **The PL-B hazard.** Same size bound as `leafHazard`. -/
noncomputable def leafHazardB : Hazard where
  forward log _ := Finset.univ.filter fun y => vB.forwardBad log y
  inverse log y := Finset.univ.filter fun x => vB.inverseBad log y x
  bound k := (3 * k + 1) * wide
  forward_card log _ := forward_card_leB log
  inverse_card log y := inverse_card_leB log y

theorem clean_leafB {log : Log Word} (clean : Clean leafHazardB log) : vB.Clean log := by
  intro pre e post split
  obtain ⟨fwd, inv⟩ := clean pre e post split
  refine ⟨fun dir bad => fwd dir ?_, fun dir bad => inv dir ?_⟩
  · simp only [leafHazardB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact bad
  · simp only [leafHazardB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact bad

/-! ## Budget -/

/-- The budget depends on the hazard only through its size bound. -/
theorem hazardBudget_congr {H H' : Hazard} (same : H.bound = H'.bound) (k q : ℕ) :
    hazardBudget H k q = hazardBudget H' k q := by
  unfold hazardBudget rate
  rw [same]

/-- **(E) for PL-B.** With at most `2^64` extra queries, the PL-B hazard has probability at most
`q / 2^121` for `1 ≤ q ≤ 2^120` (for larger `q` the binding target `q/2^120 ≥ 1` is trivial). -/
theorem leafB_budget (q extra : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (overhead : extra ≤ 2 ^ 64) :
    hazardBudget leafHazardB 0 (q + extra) ≤ (q : ℝ≥0∞) / 2 ^ 121 := by
  have same : leafHazardB.bound = leafHazard.bound := by
    funext k
    show (3 * k + 1) * wide = (3 * k + 1) * wide
    rfl
  rw [hazardBudget_congr same]
  exact leaf_budget q extra positive small overhead

/-! ## The PL-B detector -/

/-- A PL-B permutation collision, read from returned replies only: the four evaluations of two
different (value, salt) pairs whose digests agree. -/
def PermCollisionB (replies : List (Word × Word)) : Prop :=
  ∃ (T T' : BitVec 64) (s s' : BitVec 128) (m m' : BitVec 2048), (m, s) ≠ (m', s') ∧
    ∃ y₁ y₂ y₁' y₂' : Word,
      (leafXB1 m, y₁) ∈ replies ∧ (leafXB2 T s m y₁, y₂) ∈ replies ∧
      (leafXB1 m', y₁') ∈ replies ∧ (leafXB2 T' s' m' y₁', y₂') ∈ replies ∧
      vB.digest y₂ = vB.digest y₂'

/-- Logged true replies with a PL-B collision raise the `leafHazardB` flag. -/
theorem perm_collision_flagB (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β)
    (r : β × State) (hr : r ∈ support (run leafHazardB C σ comp ([], false)))
    (replies : List (Word × Word))
    (logged : ∀ p ∈ replies, p.1 ∈ r.2.1.inputs ∧ p.2 = σ p.1)
    (collision : PermCollisionB replies) : r.2.2 = true := by
  apply flag_of_unclean leafHazardB C σ comp r hr
  intro clean
  have entry : ∀ p ∈ replies, ∃ e ∈ r.2.1, e.input = p.1 ∧ e.output = p.2 := by
    intro p hp
    obtain ⟨member, value⟩ := logged p hp
    obtain ⟨e, he, hx⟩ := List.mem_map.mp member
    refine ⟨e, he, hx, ?_⟩
    rw [value, ← hx, run_consistent leafHazardB C σ comp r hr e he]
  obtain ⟨T, T', s, s', m, m', different, y₁, y₂, y₁', y₂', p₁, p₂, p₁', p₂', same⟩ := collision
  obtain ⟨e₁, mem₁, i₁, o₁⟩ := entry _ p₁
  obtain ⟨e₂, mem₂, i₂, o₂⟩ := entry _ p₂
  obtain ⟨e₁', mem₁', i₁', o₁'⟩ := entry _ p₁'
  obtain ⟨e₂', mem₂', i₂', o₂'⟩ := entry _ p₂'
  exact leafB_unclean (clean_leafB clean) different mem₁ mem₂ mem₁' mem₂' i₁ (by rw [i₂, o₁]) i₁'
    (by rw [i₂', o₁']) (by rw [o₂, o₂']; exact same)

/-- **Permutation half of the PL-B mixed detector.** Any search whose returned replies are, on
every reachable hazard run, logged true evaluations: a PL-B collision among them has probability
at most `q / 2^121` over the uniform permutation, for every compression table. -/
theorem perm_collision_boundB_of_logged (C : Compression) {β : Type}
    (search : OracleComp World β) (replies : β → List (Word × Word)) (q extra : ℕ)
    (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (overhead : extra ≤ 2 ^ 64)
    (bounded : PublicQueryBound search (q + extra))
    (replied : ∀ (σ : Perm) (r : β × State), r ∈ support (run leafHazardB C σ search ([], false)) →
      ∀ p ∈ replies r.1, p.1 ∈ r.2.1.inputs ∧ p.2 = σ p.1) :
    Pr{let x ← ($ᵗ Perm >>= fun σ => Prod.fst <$> (⟨C, σ⟩ : Oracle).run search)}[
      PermCollisionB (replies x)] ≤ (q : ℝ≥0∞) / 2 ^ 121 :=
  (perm_event_bound leafHazardB C search (q + extra) bounded (fun x => PermCollisionB (replies x))
    fun σ r hr collision => perm_collision_flagB C σ search r hr (replies r.1)
      (replied σ r hr) collision).trans (leafB_budget q extra positive small overhead)

end PermLean
