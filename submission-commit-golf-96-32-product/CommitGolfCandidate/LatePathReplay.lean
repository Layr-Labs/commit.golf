import CommitGolfCandidate.LateCheckSound
import CommitGolfCandidate.QueryBudget
namespace CommitGolfCandidate.Late.Check
open CommitGolf OracleComp OracleSpec
/-- Replay a bottom-up authentication path, retaining its compression inputs. -/
def replayPath : Digest → List (Bool × Digest) → OracleComp World (Digest × List (BitVec COMPRESSION_INPUT_LENGTH))
  | node, [] => pure (node, [])
  | node, (right, sibling) :: rest => do
      let input := if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node))
      let next ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let (root, inputs) ← replayPath next rest
      return (root, input :: inputs)

/-- Replay the binary subtree of `referenceHeap compress 128 cap` rooted at `node`
with `height` levels above the 128 leaves at slots `128..255`. Uses `2 ^ height - 1` calls. -/
def replayCapNode (cap : Nat → Digest) : Nat → Nat → OracleComp World Digest
  | 0, node => pure (cap (node - 128))
  | height + 1, node => do
      let left ← replayCapNode cap height (2 * node)
      let right ← replayCapNode cap height (2 * node + 1)
      let out ← (liftM (World.query (.inr (.inl (padInput (right ++ left))))) : OracleComp World Digest)
      pure out

def replayCapUpperLevel (cap : Nat → Digest) (index : Index) (h : Nat) :
    OracleComp World (Bool × Digest) := do
  let sibling ← replayCapNode cap h (((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1)
  return (index.val.testBit (17 + h), sibling)

/-- Replay all 7 upper siblings of a cap-mode record (heights 0..6, 120 calls total). -/
def replayCapUpper (cap : Nat → Digest) (index : Index) :
    OracleComp World (Fin 7 → Bool × Digest) := do
  let s0 ← replayCapUpperLevel cap index 0
  let s1 ← replayCapUpperLevel cap index 1
  let s2 ← replayCapUpperLevel cap index 2
  let s3 ← replayCapUpperLevel cap index 3
  let s4 ← replayCapUpperLevel cap index 4
  let s5 ← replayCapUpperLevel cap index 5
  let s6 ← replayCapUpperLevel cap index 6
  return fun k =>
    match k.val with
    | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5 | _ => s6

theorem replay_path_run (oracle : Oracle) (node : Digest) (path : List (Bool × Digest)) :
    oracle.run (replayPath node path) =
      pure ((climb oracle.compression node path,
        pathInputs oracle.compression node path), path.length) := by
  induction path generalizing node with
  | nil => exact oracle_run_pure _ _
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [replayPath]
    erw [oracle_run_public_bind oracle (.inl (if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node))))]
    erw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure]
    cases right <;> simp [Oracle.answer, pathInputs, climb, combine, Nat.add_comm] <;> exact ⟨rfl, rfl⟩

theorem replay_cap_node_run (oracle : Oracle) (cap : Nat → Digest) (height node : Nat)
    (lo : 128 ≤ 2 ^ height * node) (hi : 2 ^ height * (node + 1) ≤ 256) :
    oracle.run (replayCapNode cap height node) =
      pure (referenceHeap oracle.compression 128 cap node, 2 ^ height - 1) := by
  induction height generalizing node with
  | zero =>
    rw [replayCapNode, oracle_run_pure]
    have hLeaf : referenceHeap oracle.compression 128 cap node = cap (node - 128) := by
      have h := reference_heap_leaf oracle.compression 128 cap (node - 128) (by simp at lo hi; omega)
      rw [show 128 + (node - 128) = node by simp at lo hi; omega] at h
      exact h
    rw [hLeaf]; rfl
  | succ height ih =>
    have hPow : 2 ^ (height + 1) = 2 * 2 ^ height := by rw [Nat.pow_succ]; omega
    have pos1 : 1 ≤ 2 ^ height := Nat.one_le_two_pow
    have hNodePos : 0 < node := by
      by_contra h0; have : node = 0 := by omega
      subst node; simp at lo
    have hNodeLt : node < 128 := by
      rw [hPow, Nat.mul_comm 2, Nat.mul_assoc] at hi
      have := Nat.mul_le_mul_right (2 * (node + 1)) pos1
      omega
    have leftLo : 128 ≤ 2 ^ height * (2 * node) := by rw [hPow] at lo; linarith
    have leftHi : 2 ^ height * (2 * node + 1) ≤ 256 := by rw [hPow] at hi; nlinarith
    have rightLo : 128 ≤ 2 ^ height * (2 * node + 1) := by rw [hPow] at lo; nlinarith
    have rightHi : 2 ^ height * (2 * node + 1 + 1) ≤ 256 := by rw [hPow] at hi; linarith
    simp only [replayCapNode]
    erw [oracle_run_bind, ih (2 * node) leftLo leftHi]
    simp only [pure_bind]
    erw [oracle_run_bind, ih (2 * node + 1) rightLo rightHi]
    simp only [pure_bind]
    erw [oracle_run_public_bind oracle (.inl (padInput _))]
    erw [oracle_run_pure]
    simp only [pure_bind, Oracle.answer]
    have hRef := (reference_heap_parent oracle.compression 128 cap node hNodePos hNodeLt).symm
    change pure (combine oracle.compression _ _, (2 ^ height - 1) + ((2 ^ height - 1) + (1 + 0))) = _
    rw [hRef]
    congr 2; omega

private theorem cap_sibling_node_bounds (index : Index) (h : Nat) (hh : h < 7) :
    128 ≤ 2 ^ h * (((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1) ∧
    2 ^ h * ((((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1) + 1) ≤ 256 := by
  have hlt : index.val < 2 ^ 24 := index.isLt
  have hq : index.val / 2 ^ 17 < 128 := by omega
  let x := (128 + index.val / 2 ^ 17) / 2 ^ h
  have hEvenPow : 2 ^ (7 - h) % 2 = 0 := by
    have : 7 - h = (6 - h) + 1 := by omega
    rw [this, Nat.pow_succ]; omega
  have hpow : 2 ^ h * 2 ^ (7 - h) = 128 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have xLo : 2 ^ (7 - h) ≤ x :=
    (Nat.le_div_iff_mul_le (by positivity)).mpr (by rw [Nat.mul_comm, hpow]; omega)
  have xHi : x < 2 * 2 ^ (7 - h) :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by
      have : 2 * 2 ^ (7 - h) * 2 ^ h = 256 := by
        rw [Nat.mul_assoc, Nat.mul_comm (2 ^ (7 - h)), hpow]
      omega)
  have sxBounds : 2 ^ (7 - h) ≤ x ^^^ 1 ∧ (x ^^^ 1) + 1 ≤ 2 * 2 ^ (7 - h) := by
    by_cases even : x % 2 = 0
    · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]; omega
    · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]; omega
  constructor
  · calc 128 = 2 ^ h * 2 ^ (7 - h) := hpow.symm
      _ ≤ 2 ^ h * (x ^^^ 1) := Nat.mul_le_mul_left _ sxBounds.1
  · calc 2 ^ h * ((x ^^^ 1) + 1) ≤ 2 ^ h * (2 * 2 ^ (7 - h)) := Nat.mul_le_mul_left _ sxBounds.2
      _ = 2 * (2 ^ h * 2 ^ (7 - h)) := by ring
      _ = 256 := by rw [hpow]

theorem replay_cap_upper_level_run (oracle : Oracle) (cap : Nat → Digest)
    (index : Index) (h : Nat) (hh : h < 7) :
    oracle.run (replayCapUpperLevel cap index h) =
      pure ((index.val.testBit (17 + h),
        referenceHeap oracle.compression 128 cap (((128 + index.val / 2 ^ 17) / 2 ^ h) ^^^ 1)),
        2 ^ h - 1) := by
  have bounds := cap_sibling_node_bounds index h hh
  simp only [replayCapUpperLevel, oracle_run_bind, replay_cap_node_run oracle cap h _ bounds.1 bounds.2,
    pure_bind, oracle_run_pure, Nat.add_zero]

theorem replay_cap_upper_run (oracle : Oracle) (cap : Nat → Digest) (index : Index) :
    oracle.run (replayCapUpper cap index) =
      pure (fun k : Fin 7 => (index.val.testBit (17 + k.val),
        referenceHeap oracle.compression 128 cap (((128 + index.val / 2 ^ 17) / 2 ^ k.val) ^^^ 1)),
        120) := by
  simp only [replayCapUpper, oracle_run_bind,
    replay_cap_upper_level_run oracle cap index 0 (by decide),
    replay_cap_upper_level_run oracle cap index 1 (by decide),
    replay_cap_upper_level_run oracle cap index 2 (by decide),
    replay_cap_upper_level_run oracle cap index 3 (by decide),
    replay_cap_upper_level_run oracle cap index 4 (by decide),
    replay_cap_upper_level_run oracle cap index 5 (by decide),
    replay_cap_upper_level_run oracle cap index 6 (by decide),
    pure_bind, oracle_run_pure]
  congr 1
  refine Prod.ext ?_ ?_
  · funext ⟨k, hk⟩
    interval_cases k <;> rfl
  · norm_num

theorem replay_path_query_bound (node : Digest) (path : List (Bool × Digest)) :
    IsTotalQueryBound (replayPath node path) path.length := by
  induction path generalizing node with
  | nil => trivial
  | cons head rest ih =>
    rcases head with ⟨right, sibling⟩
    simp only [replayPath, bind_pure_comp]
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl
      (if right then (padInput (node ++ sibling)) else (padInput (sibling ++ node)))))) : OracleComp World Digest) >>= _)
      (rest.length + 1)
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun next => ?_⟩
    simpa only [Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using ih next

theorem replay_cap_node_query_bound (cap : Nat → Digest) (height node : Nat) :
    IsTotalQueryBound (replayCapNode cap height node) (2 ^ height - 1) := by
  induction height generalizing node with
  | zero => trivial
  | succ height ih =>
    unfold replayCapNode
    have eqPow : 2 ^ (height + 1) - 1 = (2 ^ height - 1) + ((2 ^ height - 1) + 1) := by
      have pos : 1 ≤ 2 ^ height := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    rw [eqPow]
    apply isTotalQueryBound_bind (ih (2 * node))
    intro left
    apply isTotalQueryBound_bind (ih (2 * node + 1))
    intro right
    change IsTotalQueryBound ((liftM (World.query (.inr (.inl (padInput (right ++ left))))) :
      OracleComp World Digest) >>= pure) 1
    erw [isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => trivial⟩

theorem replay_cap_upper_level_query_bound (cap : Nat → Digest) (index : Index) (h : Nat) :
    IsTotalQueryBound (replayCapUpperLevel cap index h) (2 ^ h - 1) := by
  unfold replayCapUpperLevel
  simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  exact replay_cap_node_query_bound cap h _

theorem replay_cap_upper_query_bound (cap : Nat → Digest) (index : Index) :
    IsTotalQueryBound (replayCapUpper cap index) 120 := by
  unfold replayCapUpper
  change IsTotalQueryBound (_ >>= _) (0 + (1 + (3 + (7 + (15 + (31 + (63 + 0)))))))
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 0); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 1); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 2); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 3); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 4); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 5); intro _
  apply isTotalQueryBound_bind (replay_cap_upper_level_query_bound cap index 6); intro _
  trivial


theorem replay_bound (odd : Bool) (s : Salt) (v : Entry) : IsTotalQueryBound (Late.replay odd s v) 4 := by
  unfold Late.replay Late.hash
  repeat first | apply (isTotalQueryBound_query_bind_iff).mpr; constructor; decide | intro _
  trivial

end CommitGolfCandidate.Late.Check
