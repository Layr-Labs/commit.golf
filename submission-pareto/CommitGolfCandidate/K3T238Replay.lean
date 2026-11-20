import CommitGolfCandidate.K3T238Witness
import CommitGolfCandidate.K3T238Birthday
import CommitGolfCandidate.K3T238Budget
import CommitGolfCandidate.K3T238Leaf
import CommitGolfCandidate.K3T238Quad
import CommitGolfCandidate.TwoPermutationBindingBridge

/-!
# Replay evidence with 238-bit internal nodes

The tree witness of a 238-bit tree is a compression collision on the low 238 bits of two replies
(`CompressionWitness238`; a 240-bit collision is one). Its probability is the product-form birthday bound at
238 bits, which fits `255·q/2^128`; the sharp leaf and quartet bounds take `q/2^129` each, so the three
witnesses together stay within `q/2^120` (same shape as `quad_replay_bound_of_layout`).
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
set_option maxRecDepth 8192

private theorem projected238_witness_stored (rows : List PublicRow) (cache : CompressionCache)
    (stores : ∀ row ∈ rows, compressionStored cache row) (hit : CompressionWitness238 rows) :
    ProjectedCollision238 cache := by
  obtain ⟨x, y, a, b, left, right, different, equal⟩ := hit
  have query₀ : cache x = some a := stores _ left
  have query₁ : cache y = some b := stores _ right
  refine ⟨x, y, low238 a, low238 b, different, ?_, ?_, heq_of_eq equal⟩
  · change Option.map low238 (cache x) = some (low238 a)
    rw [query₀]
    rfl
  · change Option.map low238 (cache y) = some (low238 b)
    rw [query₁]
    rfl

private theorem t238_room (q calls : Nat) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31) :
    calls ≤ 2 ^ 237 := by
  have top : q + 2 ^ 31 ≤ 2 ^ 120 + 2 ^ 31 := Nat.add_le_add_right small _
  have room : (2 : Nat) ^ 120 + 2 ^ 31 ≤ 2 ^ 237 := by norm_num
  exact withReplay.trans (top.trans room)

theorem fixed_permutation_projected238_bound {α : Type} (p : Perm) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (withReplay : calls ≤ q + 2 ^ 31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let compress ← $ᵗ Compression; fixedOracleRun ⟨compress, p⟩ (recordRows program))}[
      CompressionWitness238 result.2] ≤ 255 * (q : ENNReal) / 2^128 := by
  have equivalent := (EvalDistEq.of_evalDist_eq (compression_sampling_empty p (recordRows program))).prEvent_eq
    (fun result => CompressionWitness238 result.2)
  rw [← equivalent, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ (fun result reached hit => ?_)).trans
    ((projected238_collision_exp p (recordRows program) calls bounded (t238_room q calls small withReplay)).trans
      (t238_tree_budget q calls positive small withReplay))
  exact projected238_witness_stored result.1.2 result.2 (compression_replay_stored p program ∅ result reached) hit

def QuadReplayEvidence238 (rows : List PublicRow) : Prop :=
  CompressionWitness238 rows ∨ PinnedLeafWitness rows ∨ QuadWitness rows

theorem QuadReplayEvidence.to238 {rows : List PublicRow} (hit : QuadReplayEvidence rows) :
    QuadReplayEvidence238 rows := by
  rcases hit with comp | rest
  · exact Or.inl comp.to238
  · exact Or.inr rest

theorem quad_evidence238_mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : QuadReplayEvidence238 earlier) : QuadReplayEvidence238 later := by
  rcases evidence with comp | leaf | quad
  · exact Or.inl (comp.mono contained)
  · have small : PinnedReplayEvidence earlier := Or.inr leaf
    rcases small.mono contained with c | l
    · exact Or.inl c.to238
    · exact Or.inr (Or.inl l)
  · obtain ⟨g, x, y, h, ax, ay, rx, ry, equal⟩ := quad
    exact Or.inr (Or.inr ⟨g, x, y, h, ax, ay, contained _ rx, contained _ ry, equal⟩)

theorem t238_budget_sum (q : Nat) :
    255 * (q : ENNReal) / 2^128 + ((q : ENNReal)/2^129 + (q : ENNReal)/2^129) = (q : ENNReal)/2^120 := by
  have halves : (q : ENNReal)/2^129 + (q : ENNReal)/2^129 = (q : ENNReal)/2^128 := by
    rw [← ENNReal.add_div, ← two_mul,
      show (2 : ENNReal)^129 = 2 * 2^128 by rw [show (129 : Nat) = 1+128 by decide, pow_add]; norm_num]
    exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)
  rw [halves, ← ENNReal.add_div, show 255 * (q : ENNReal) + q = 2^8 * q by ring,
    show (2 : ENNReal)^128 = 2^8 * 2^120 by rw [show (128 : Nat) = 8+120 by decide, pow_add]]
  exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

/-- Binding replay bound with 238-bit internal nodes: tree `255·q/2^128` (product-form birthday), leaf
`q/2^129`, quartet `q/2^129`. -/
theorem quad_replay_bound_t238_of_layout {α : Type} (layout : PeerLeafLayoutSharp) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      QuadReplayEvidence238 result.2] ≤ (q : ENNReal)/2^120 := by
  let execution := Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program)
  let A : (α × List PublicRow) → Prop := fun result => CompressionWitness238 result.2
  let B : (α × List PublicRow) → Prop := fun result => PinnedLeafWitness result.2
  let C : (α × List PublicRow) → Prop := fun result => QuadWitness result.2
  change Pr{let result ← execution}[A result ∨ B result ∨ C result] ≤ _
  have termA : Pr{let result ← execution}[A result] ≤ 255 * (q : ENNReal) / 2^128 := by
    have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress,perm⟩ (recordRows program)))
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq A]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected238_bound p program q calls positive small replayed bounded
  have termB : Pr{let result ← execution}[B result] ≤ (q : ENNReal)/2^129 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      layout.bound compress program q calls positive small replayed bounded
  have termC : Pr{let result ← execution}[C result] ≤ (q : ENNReal)/2^129 := by
    simp only [execution, Oracle.sample, bind_assoc, pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      fixed_compression_quad_bound_sharp compress program q calls positive small replayed bounded
  exact (prEvent_or_le execution A (fun r => B r ∨ C r)).trans
    ((add_le_add termA ((prEvent_or_le execution B C).trans (add_le_add termB termC))).trans_eq
      (t238_budget_sum q))

/-- The K3-lite (K1 leaves) binding replay bound with 238-bit internal nodes. -/
theorem quad_replay_bound_t238 {α : Type} (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      QuadReplayEvidence238 result.2] ≤ (q : ENNReal)/2^120 :=
  quad_replay_bound_t238_of_layout k1_peer_leaf_layout_sharp program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
