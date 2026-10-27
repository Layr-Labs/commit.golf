import CommitGolfCandidate.Xof.Compression
import ToMathlib.Data.BitVec

/-! # Counting random functions consistent with a transcript

A fresh input has equally many extensions for every output, even after arbitrary previous
answers. This proves the conditional uniformity used in the adaptive collision bound. -/
namespace CommitGolf.CompressionBaseline
open scoped Classical
set_option exponentiation.threshold 2000
set_option linter.constructorNameAsVariable false
namespace HashCount
noncomputable scoped instance (priority := high) fintypeHash : Fintype Hash := inferInstance
end HashCount
open scoped HashCount

@[irreducible] noncomputable def Ext (T : List (Input × Digest)) : Finset Hash :=
  Finset.univ.filter fun H => ∀ p ∈ T, H p.1 = p.2

theorem mem_Ext {T : List (Input × Digest)} {H : Hash} :
    H ∈ Ext T ↔ ∀ p ∈ T, H p.1 = p.2 := by
  unfold Ext
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem Ext_cons (x : Input) (y : Digest) (T : List (Input × Digest)) :
    Ext ((x, y) :: T) = (Ext T).filter fun H => H x = y := by
  unfold Ext
  ext H; simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
    forall_eq_or_imp]; tauto

theorem Ext_cons_of_mem {p : Input × Digest} {T : List (Input × Digest)} (hp : p ∈ T) :
    Ext (p :: T) = Ext T := by
  unfold Ext
  ext H; simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
    forall_eq_or_imp, and_iff_right_iff_imp]
  intro h; exact h p hp

theorem card_fiber_mul_le (s : Finset Hash) (φ : Hash → Digest) (F : Finset Digest) (D : Nat)
    (hD : D ≤ F.card) (hout : ∀ z ∉ F, s.filter (fun π => φ π = z) = ∅)
    (heq : ∀ z ∈ F, ∀ z' ∈ F,
      (s.filter fun π => φ π = z).card = (s.filter fun π => φ π = z').card)
    (z : Digest) : (s.filter fun π => φ π = z).card * D ≤ s.card := by
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

/-- Every output is equally likely at a fresh input. -/
theorem card_Ext_cons_mul_le (T : List (Input × Digest)) (x : Input)
    (hx : ∀ p ∈ T, p.1 ≠ x) (y : Digest) :
    (Ext ((x, y) :: T)).card * (2 ^ 256) ≤ (Ext T).card := by
  rw [Ext_cons]
  refine card_fiber_mul_le (Ext T) (fun H => H x) Finset.univ _ ?_ ?_ ?_ y
  · rw [Finset.card_univ, Fintype.card_bitVec]; rfl
  · intro z hz; simp at hz
  · intro z _ z' _
    refine Finset.card_bij' (fun H _ => Function.update H x z')
      (fun H _ => Function.update H x z) ?_ ?_ ?_ ?_
    · intro H hH
      obtain ⟨hT, _⟩ := Finset.mem_filter.mp hH
      apply Finset.mem_filter.mpr
      refine ⟨mem_Ext.mpr ?_, by simp⟩
      intro p hp
      rw [Function.update_of_ne (hx p hp)]
      exact mem_Ext.mp hT p hp
    · intro H hH
      obtain ⟨hT, _⟩ := Finset.mem_filter.mp hH
      apply Finset.mem_filter.mpr
      refine ⟨mem_Ext.mpr ?_, by simp⟩
      intro p hp
      rw [Function.update_of_ne (hx p hp)]
      exact mem_Ext.mp hT p hp
    · intro H hH
      have h := (Finset.mem_filter.mp hH).2
      funext a
      by_cases ha : a = x
      · subst a; simpa using h.symm
      · simp [Function.update_of_ne ha]
    · intro H hH
      have h := (Finset.mem_filter.mp hH).2
      funext a
      by_cases ha : a = x
      · subst a; simpa using h.symm
      · simp [Function.update_of_ne ha]

/-- **One fresh query.** Split a sum over `s` by the value `φ π`. On a bad value the summand is at
most `1`; on any other value the part's sum is at most its size times `R`. If every part has at
most `|s| / D` elements and there are at most `M` bad values, the sum is at most
`|s| · (M / D + R)`. -/
theorem sum_le_of_fibers (s : Finset Hash) (φ : Hash → Digest) (D M : Nat) (hM : 0 < M)
    (hcard : ∀ z, (s.filter fun π => φ π = z).card * D ≤ s.card)
    (Bad : Finset Digest) (hBad : Bad.card ≤ M) (R : ENNReal) (g : Digest → Hash → ENNReal)
    (hg : ∀ z π, g z π ≤ 1)
    (hgood : ∀ z ∉ Bad,
      ∑ π ∈ s.filter (fun π => φ π = z), g z π ≤ (s.filter fun π => φ π = z).card * R) :
    ∑ π ∈ s, g (φ π) π ≤ s.card * ((M : ENNReal) / (D : ENNReal) + R) := by
  set c : Digest → Nat := fun z => (s.filter fun π => φ π = z).card with hc
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

end CommitGolf.CompressionBaseline
