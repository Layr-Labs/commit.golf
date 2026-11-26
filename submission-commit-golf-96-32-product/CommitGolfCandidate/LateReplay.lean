import CommitGolfCandidate.LateBinding
import CommitGolfCandidate.Binding
import CommitGolfCandidate.Counting

namespace CommitGolfCandidate.Late
open CommitGolf OracleComp

theorem parent_compatible (h : Compression) (a b : Digest) :
    h (parentBlock a b) = combine h a b := by
  exact congrArg h (BitVec.append_assoc (x₁ := (0 : Digest)) (x₂ := b) (x₃ := a))

def replay (odd : Bool) (s : Salt) (v : Entry) : OracleComp World (Digest × List Block) := do
  let x := firstBlock v
  let u ← hash x
  let y := middleBlock v u
  let a ← hash y
  let z := lastBlock v
  let b ← hash z
  let f := finalBlock odd s a b
  let root ← hash f
  pure (root, [x,y,z,f])

theorem replay_run (o : Oracle) (odd : Bool) (s : Salt) (v : Entry) :
    o.run (replay odd s v) = pure ((leaf o.compression odd s v, inputs o.compression odd s v), 4) := by
  simp only [replay, hash, oracle_run_public_bind, oracle_run_pure, pure_bind]
  rfl

def recordInputs (h : Compression) (odd : Bool) (s : Salt) (v : Entry)
    (path : List (Bool × Digest)) :=
  inputs h odd s v ++ pathInputs h (leaf h odd s v) path

theorem record_collision (h : Compression) (odd : Bool) (s t : Salt) (v w : Entry)
    (p q : List (Bool × Digest)) (position : p.map Prod.fst = q.map Prod.fst)
    (different : v ≠ w)
    (root : climb h (leaf h odd s v) p = climb h (leaf h odd t w) q) :
    ∃ x ∈ recordInputs h odd s v p, ∃ y ∈ recordInputs h odd t w q, x ≠ y ∧ h x = h y := by
  by_cases eq : leaf h odd s v = leaf h odd t w
  · obtain ⟨x, hx, y, hy, coll⟩ := leaf_collision h odd s t v w different eq
    exact ⟨x, List.mem_append_left _ hx, y, List.mem_append_left _ hy, coll⟩
  · obtain ⟨x, hx, y, hy, coll⟩ := collision_of_climb_eq h _ _ p q position eq root
    exact ⟨x, List.mem_append_right _ hx, y, List.mem_append_right _ hy, coll⟩

theorem record_inputs_length (h : Compression) (odd : Bool) (s : Salt) (v : Entry)
    (p : List (Bool × Digest)) :
    (recordInputs h odd s v p).length = 4+p.length := by
  simp [recordInputs, inputs, pathInputs_length]
  omega

end CommitGolfCandidate.Late
