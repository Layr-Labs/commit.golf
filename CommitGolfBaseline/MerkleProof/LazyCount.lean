import CommitGolf
import ToMathlib.Data.BitVec

/-! # Counting permutations consistent with a table

For a list `T` of pairs, `Ext T` is the set of permutations `π` with `π x = y` for every pair
`(x, y)` of `T`. Fixing one more value `π x = y` (or `π⁻¹ y = x`) splits `Ext T` into parts of
equal size, one per free value; this is what makes the answer to a fresh query uniform. The main
result, `sum_le_of_fibers`, bounds a sum over `Ext T` by splitting it along such a part. -/

namespace CommitGolf.Baseline

set_option linter.constructorNameAsVariable false

/-- One fixed `Fintype` structure on permutations, so that every `Finset.univ : Finset Perm` below
is literally the same term: comparing two different structures would unfold the enumeration of
all `(2 ^ 1600)!` permutations. -/
noncomputable instance (priority := high) fintypePerm : Fintype Perm := inferInstance

/-- Permutations that agree with every pair of `T`. -/
@[irreducible] noncomputable def Ext (T : List (State × State)) : Finset Perm :=
  Finset.univ.filter fun π => ∀ p ∈ T, π p.1 = p.2

theorem mem_Ext {T : List (State × State)} {π : Perm} : π ∈ Ext T ↔ ∀ p ∈ T, π p.1 = p.2 := by
  unfold Ext
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem Ext_cons (x y : State) (T : List (State × State)) :
    Ext ((x, y) :: T) = (Ext T).filter fun π => π x = y := by
  ext π; simp [mem_Ext, and_comm]

theorem Ext_cons_inv (x y : State) (T : List (State × State)) :
    Ext ((x, y) :: T) = (Ext T).filter fun π => π.symm y = x := by
  rw [Ext_cons]; congr 1; ext π; constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem Ext_cons_of_mem {p : State × State} {T : List (State × State)} (hp : p ∈ T) :
    Ext (p :: T) = Ext T := by
  ext π; simp only [mem_Ext, List.mem_cons, forall_eq_or_imp, and_iff_right_iff_imp]
  intro h; exact h p hp

/-- The number of states is `2 ^ 1600`. -/
theorem card_state : Fintype.card State = 2 ^ 1600 := by
  exact Fintype.card_bitVec 1600

/-- Values not taken by `f` on the list `T`: at least `2 ^ 1600 - |T|` of them. -/
theorem card_free_ge (T : List (State × State)) (f : State × State → State) :
    2 ^ 1600 - T.length ≤ (Finset.univ.filter fun z : State => ∀ p ∈ T, f p ≠ z).card := by
  have hsub : (Finset.univ.filter fun z : State => ∀ p ∈ T, f p ≠ z)ᶜ ⊆ (T.map f).toFinset := by
    intro z hz
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
      not_not] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h1 := Finset.card_le_card hsub
  have h2 : (T.map f).toFinset.card ≤ T.length :=
    (List.toFinset_card_le _).trans (by simp)
  have h3 := Finset.card_compl_add_card (Finset.univ.filter fun z : State => ∀ p ∈ T, f p ≠ z)
  rw [card_state] at h3
  omega

/-- **Equal parts.** Abstractly: if the fibers of `φ` over `s` are empty off a set `F` of at least
`D` values, and all of the same size on `F`, then each fiber has at most `|s| / D` elements. -/
theorem card_fiber_mul_le (s : Finset Perm) (φ : Perm → State) (F : Finset State) (D : Nat)
    (hD : D ≤ F.card) (hout : ∀ z ∉ F, s.filter (fun π => φ π = z) = ∅)
    (heq : ∀ z ∈ F, ∀ z' ∈ F,
      (s.filter fun π => φ π = z).card = (s.filter fun π => φ π = z').card)
    (z : State) : (s.filter fun π => φ π = z).card * D ≤ s.card := by
  by_cases hz : z ∈ F
  · have hsum : ∑ z' ∈ F, (s.filter fun π => φ π = z').card = s.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := φ) (t := F)]
      intro π hπ
      by_contra h
      have := hout (φ π) h
      have hmem : π ∈ s.filter (fun π' => φ π' = φ π) := Finset.mem_filter.mpr ⟨hπ, rfl⟩
      rw [this] at hmem; simp at hmem
    rw [Finset.sum_congr rfl fun z' hz' => heq z' hz' z hz, Finset.sum_const, smul_eq_mul]
      at hsum
    calc (s.filter fun π => φ π = z).card * D
        ≤ (s.filter fun π => φ π = z).card * F.card := Nat.mul_le_mul_left _ hD
      _ = s.card := by rw [mul_comm]; exact hsum
  · rw [hout z hz]; simp

/-- Fibers of `π ↦ π x` over `Ext T`, for `x` outside the domain of `T`. -/
theorem card_Ext_cons_mul_le (T : List (State × State)) (x : State)
    (hx : ∀ p ∈ T, p.1 ≠ x) (y : State) :
    (Ext ((x, y) :: T)).card * (2 ^ 1600 - T.length) ≤ (Ext T).card := by
  rw [Ext_cons]
  refine card_fiber_mul_le (Ext T) (fun π => π x)
    (Finset.univ.filter fun z : State => ∀ p ∈ T, p.2 ≠ z) _ (card_free_ge T Prod.snd) ?_ ?_ y
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    ext π
    simp only [Finset.mem_filter, mem_Ext, Finset.notMem_empty, iff_false, not_and]
    intro h hπ
    exact hx p hp (π.injective (by rw [hπ, h p hp]))
  · intro z hz z' hz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    refine Finset.card_bij' (fun π _ => Equiv.swap z z' * π) (fun π _ => Equiv.swap z z' * π)
      ?_ ?_ ?_ ?_
    · intro π hπ
      simp only [Finset.mem_filter, mem_Ext] at hπ ⊢
      refine ⟨fun p hp => ?_, ?_⟩
      · simp [hπ.1 p hp, Equiv.swap_apply_of_ne_of_ne (hz p hp) (hz' p hp)]
      · simp [hπ.2]
    · intro π hπ
      simp only [Finset.mem_filter, mem_Ext] at hπ ⊢
      refine ⟨fun p hp => ?_, ?_⟩
      · simp [hπ.1 p hp, Equiv.swap_apply_of_ne_of_ne (hz p hp) (hz' p hp)]
      · simp [hπ.2]
    · intro π _; simp [← mul_assoc]
    · intro π _; simp [← mul_assoc]

/-- Fibers of `π ↦ π⁻¹ y` over `Ext T`, for `y` outside the range of `T`. -/
theorem card_Ext_cons_mul_le_inv (T : List (State × State)) (y : State)
    (hy : ∀ p ∈ T, p.2 ≠ y) (x : State) :
    (Ext ((x, y) :: T)).card * (2 ^ 1600 - T.length) ≤ (Ext T).card := by
  rw [Ext_cons_inv]
  refine card_fiber_mul_le (Ext T) (fun π => π.symm y)
    (Finset.univ.filter fun z : State => ∀ p ∈ T, p.1 ≠ z) _ (card_free_ge T Prod.fst) ?_ ?_ x
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    ext π
    simp only [Finset.mem_filter, mem_Ext, Finset.notMem_empty, iff_false, not_and]
    intro h hπ
    apply hy p hp
    rw [← h p hp, ← hπ, Equiv.apply_symm_apply]
  · intro z hz z' hz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    refine Finset.card_bij' (fun π _ => π * Equiv.swap z z') (fun π _ => π * Equiv.swap z z')
      ?_ ?_ ?_ ?_
    · intro π hπ
      simp only [Finset.mem_filter, mem_Ext] at hπ ⊢
      refine ⟨fun p hp => ?_, ?_⟩
      · simp [Equiv.swap_apply_of_ne_of_ne (hz p hp) (hz' p hp), hπ.1 p hp]
      · rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hπ.2, Equiv.symm_swap,
          Equiv.swap_apply_left]
    · intro π hπ
      simp only [Finset.mem_filter, mem_Ext] at hπ ⊢
      refine ⟨fun p hp => ?_, ?_⟩
      · simp [Equiv.swap_apply_of_ne_of_ne (hz p hp) (hz' p hp), hπ.1 p hp]
      · rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hπ.2, Equiv.symm_swap,
          Equiv.swap_apply_right]
    · intro π _; simp [mul_assoc]
    · intro π _; simp [mul_assoc]

/-- **One fresh query.** Split a sum over `s` by the value `φ π`. On a bad value the summand is at
most `1`; on any other value the part's sum is at most its size times `R`. If every part has at
most `|s| / D` elements and there are at most `M` bad values, the sum is at most
`|s| · (M / D + R)`. -/
theorem sum_le_of_fibers (s : Finset Perm) (φ : Perm → State) (D M : Nat) (hM : 0 < M)
    (hcard : ∀ z, (s.filter fun π => φ π = z).card * D ≤ s.card)
    (Bad : Finset State) (hBad : Bad.card ≤ M) (R : ENNReal) (g : State → Perm → ENNReal)
    (hg : ∀ z π, g z π ≤ 1)
    (hgood : ∀ z ∉ Bad,
      ∑ π ∈ s.filter (fun π => φ π = z), g z π ≤ (s.filter fun π => φ π = z).card * R) :
    ∑ π ∈ s, g (φ π) π ≤ s.card * ((M : ENNReal) / (D : ENNReal) + R) := by
  set c : State → Nat := fun z => (s.filter fun π => φ π = z).card with hc
  rw [← Finset.sum_fiberwise s φ]
  have hpart : ∀ z, ∑ π ∈ s.filter (fun π => φ π = z), g (φ π) π ≤
      (if z ∈ Bad then (c z : ENNReal) else 0) + (c z : ENNReal) * R := by
    intro z
    have hrw : ∑ π ∈ s.filter (fun π => φ π = z), g (φ π) π =
        ∑ π ∈ s.filter (fun π => φ π = z), g z π :=
      Finset.sum_congr rfl fun π hπ => by rw [(Finset.mem_filter.mp hπ).2]
    rw [hrw]
    by_cases hz : z ∈ Bad
    · rw [if_pos hz]
      calc ∑ π ∈ s.filter (fun π => φ π = z), g z π
          ≤ ∑ π ∈ s.filter (fun π => φ π = z), (1 : ENNReal) := Finset.sum_le_sum fun π _ => hg z π
        _ = c z := by simp [hc]
        _ ≤ c z + c z * R := le_self_add
    · rw [if_neg hz, zero_add]; exact hgood z hz
  refine (Finset.sum_le_sum fun z _ => hpart z).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  have htot : ∑ z, (c z : ENNReal) = s.card := by
    have : ∑ z, c z = s.card := by
      rw [hc]
      exact (Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ) (s := s)
        (by simp)).symm
    exact_mod_cast this
  rw [htot]
  gcongr
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  by_cases hs : s.card = 0
  · have : ∀ z, c z = 0 := fun z => by
      simp only [hc, Finset.card_eq_zero] at hs ⊢; simp [hs]
    simp [this]
  have hnat : (∑ z ∈ Bad, c z) * D ≤ M * s.card := by
    rw [Finset.sum_mul]
    calc ∑ z ∈ Bad, c z * D ≤ ∑ z ∈ Bad, s.card := Finset.sum_le_sum fun z _ => hcard z
      _ = Bad.card * s.card := by simp
      _ ≤ M * s.card := Nat.mul_le_mul_right _ hBad
  have hne : ((M : ENNReal) * s.card) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]; omega
  have hnt : ((M : ENNReal) * s.card) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  rw [← mul_div_assoc, mul_comm (s.card : ENNReal), ENNReal.le_div_iff_mul_le (Or.inr hne)
    (Or.inr hnt)]
  exact_mod_cast hnat

end CommitGolf.Baseline
