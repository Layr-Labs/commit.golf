import CommitGolfCandidate.ProjectedCollisionProduct

/-! Collisions in the stored internal digests: the low 238 bits of compression
replies. The sampled oracle still returns the full 256 bits to every adversary.

`low240` keeps its 240-bit type (the 30-byte serialized width) but forces its
top two bits to zero, so a stored internal digest carries 238 reply bits. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 4096

/-- The 238 low reply bits, zero-extended to the 240-bit serialized width. -/
def low240 (value : BitVec 256) : BitVec 240 := (0 : BitVec 2) ++ lowBits 238 value

theorem low240_eq_iff (a b : BitVec 256) : low240 a = low240 b ↔ lowBits 238 a = lowBits 238 b := by
  constructor
  · intro same
    have := congrArg (fun v : BitVec 240 => v.extractLsb' 0 238) same
    simp only [low240, BitVec.extractLsb'_append_eq_right] at this
    exact this
  · intro same
    simp [low240, same]

abbrev ProjectedCompressionSpec := BitVec 512 →ₒ BitVec 240

def projectCache (cache : CompressionCache) : ProjectedCompressionSpec.QueryCache :=
  ⟨fun key => (cache key).map low240⟩

def ProjectedCollision (cache : CompressionCache) : Prop := CacheHasCollision (projectCache cache)

/-- A collision of the zero-extended projection is a low-238 collision. -/
theorem projected_collision_width (cache : CompressionCache) (hit : ProjectedCollision cache) :
    ProjectedCollisionW 238 cache := by
  obtain ⟨x, y, u, v, different, left, right, same⟩ := hit
  change Option.map low240 (cache x) = some u at left
  change Option.map low240 (cache y) = some v at right
  cases hx : cache x with
  | none => rw [hx] at left; cases left
  | some a =>
    cases hy : cache y with
    | none => rw [hy] at right; cases right
    | some b =>
      have left' : low240 a = u := by rw [hx] at left; exact Option.some.inj left
      have right' : low240 b = v := by rw [hy] at right; exact Option.some.inj right
      subst left' right'
      refine ⟨x, y, lowBits 238 a, lowBits 238 b, different, ?_, ?_, heq_of_eq ?_⟩
      · change Option.map (lowBits 238) (cache x) = some _
        rw [hx]; rfl
      · change Option.map (lowBits 238) (cache y) = some _
        rw [hy]; rfl
      · exact (low240_eq_iff a b).mp (eq_of_heq same)

/-- Product-form birthday bound for the stored internal digests. Up to 2^31
paid checks and probes leave `q/2^124` of the binding target for the leaf event. -/
theorem projected_collision_target (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) (bounded : PublicQueryBound computation calls) :
    (prEvent ((fun result => ProjectedCollision result.2) <$> (compressionRun permutation computation ∅))) ≤
      15 * (q : ENNReal) / 2 ^ 124 :=
  (prEvent_mono_of_support _ _ _ (fun result _ hit => projected_collision_width result.2 hit)).trans
    (projected_width_target 238 (Or.inl rfl) permutation computation q calls positive small withReplay bounded)

end CommitGolfCandidate
