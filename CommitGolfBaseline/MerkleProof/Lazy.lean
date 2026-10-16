import CommitGolfBaseline.MerkleProof.Tree
import CommitGolfBaseline.MerkleProof.LazyCount

/-! # Collisions under an ideal permutation

A generic bound, for any computation `B` querying a uniform permutation in both directions: the
probability that its queries contain two different zero-capacity inputs with equal truncated
outputs, within `n` calls.

**Bookkeeping.** `logRun π B s` runs `B` against `π` and records every permutation call as a pair
`(x, π x)`, prepended to the table `s`; forward and inverse calls alike. A table is `Good` when
no two different zero-capacity inputs in it have equal truncated outputs.

**The argument.** The permutations consistent with a table `T` are split according to the answer
to the next fresh query; all parts have the same size (compose with a transposition). A fresh
forward call `x` is answered by a uniform state outside the table's range, and it breaks
goodness only if `trunc (π x)` is one of at most `|T|` values: probability at most
`|T| · 2^1344 / (2^1600 - |T|)`. A fresh inverse call is answered by a uniform state outside the
table's domain, and it breaks goodness only if that state has zero capacity: probability at most
`2^512 / (2^1600 - |T|)`. Summing over the calls gives the bound. -/

namespace CommitGolf.Baseline
open OracleComp OracleSpec

/-- Pairs `(x, π x)` recorded during a run, most recent first. -/
abbrev Table := List (State × State)

/-- No two different zero-capacity inputs in the table have equal truncated outputs. -/
def Good (table : Table) : Prop :=
  ∀ p ∈ table, ∀ p' ∈ table, ZeroCap p.1 → ZeroCap p'.1 → trunc p.2 = trunc p'.2 → p.1 = p'.1

variable (π : Perm)

/-- Answer permutation queries with `π`, recording each call. -/
def permLog : QueryImpl PermSpec (StateT Table ProbComp)
  | .inl x => fun table => pure (π x, (x, π x) :: table)
  | .inr y => fun table => pure (π.symm y, (π.symm y, y) :: table)

/-- Coins forwarded; permutation calls answered by `π` and recorded. -/
def logImpl : QueryImpl World (StateT Table ProbComp) :=
  (fun n => (liftM (unifSpec.query n : ProbComp _) : StateT Table ProbComp _)) + permLog π

/-- Run `B` against `π` from the table `table`, recording every permutation call. -/
def logRun {α : Type} (B : OracleComp World α) (table : Table) : ProbComp (α × Table) :=
  (simulateQ (logImpl π) B).run table

theorem logRun_bind {α β : Type} (oa : OracleComp World α) (f : α → OracleComp World β)
    (table : Table) :
    logRun π (oa >>= f) table = logRun π oa table >>= fun p => logRun π (f p.1) p.2 := by
  simp [logRun]

@[simp] theorem logRun_pure {α : Type} (a : α) (table : Table) :
    logRun π (pure a : OracleComp World α) table = pure (a, table) := by
  simp [logRun]

theorem logRun_coin_bind {α : Type} (n : Nat) (k : Fin (n + 1) → OracleComp World α)
    (table : Table) :
    logRun π ((liftM (World.query (Sum.inl n)) : OracleComp World _) >>= k) table =
      (unifSpec.query n : ProbComp _) >>= fun u => logRun π (k u) table := by
  simp [logRun, logImpl]

theorem logRun_fwd_bind {α : Type} (x : State) (k : State → OracleComp World α)
    (table : Table) :
    logRun π ((liftM (World.query (Sum.inr (Sum.inl x)))) >>= k) table =
      logRun π (k (π x)) ((x, π x) :: table) := by
  simp [logRun, logImpl, permLog]
  rfl

theorem logRun_inv_bind {α : Type} (y : State) (k : State → OracleComp World α)
    (table : Table) :
    logRun π ((liftM (World.query (Sum.inr (Sum.inr y)))) >>= k) table =
      logRun π (k (π.symm y)) ((π.symm y, y) :: table) := by
  simp [logRun, logImpl, permLog]
  rfl

theorem run_coin_bind {α : Type} (n : Nat) (k : Fin (n + 1) → OracleComp World α) :
    π.run ((liftM (World.query (Sum.inl n)) : OracleComp World _) >>= k) =
      (unifSpec.query n : ProbComp _) >>= fun u => π.run (k u) := by
  simp [Perm.run, Perm.counted, Perm.world, Perm.callCost]
  rfl

theorem map_logRun {α : Type} (B : OracleComp World α) (table : Table) :
    (fun p => (p.1, p.2.length)) <$> logRun π B table =
      (fun p => (p.1, table.length + p.2)) <$> π.run B := by
  induction B using OracleComp.inductionOn generalizing table with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | x | y
    · rw [logRun_coin_bind, run_coin_bind]
      simp only [map_bind]
      exact bind_congr fun u => ih u table
    · rw [logRun_fwd_bind]
      erw [Perm.run_perm_query_bind (t := Sum.inl x)]
      rw [ih]
      simp only [Functor.map_map]
      congr 1
      funext p
      simp only [List.length_cons]
      congr 1
      omega
    · rw [logRun_inv_bind]
      erw [Perm.run_perm_query_bind (t := Sum.inr y)]
      rw [ih]
      simp only [Functor.map_map]
      congr 1
      funext p
      simp only [List.length_cons]
      congr 1
      omega

/-- The number of calls is the number of recorded pairs. -/
theorem run_eq_logRun {α : Type} (B : OracleComp World α) :
    π.run B = (fun p => (p.1, p.2.length)) <$> logRun π B [] := by
  rw [map_logRun]
  simp

theorem logRun_liftM_fwd_bind {α : Type} (x : State) (k : State → OracleComp PermSpec α)
    (table : Table) :
    logRun π (liftM ((PermSpec.query (Sum.inl x) : OracleComp PermSpec State) >>= k) :
        OracleComp World α) table =
      logRun π (liftM (k (π x))) ((x, π x) :: table) := by
  rw [liftM_bind, ← OracleComp.liftComp_eq_liftM (mx := liftM _), OracleComp.liftComp_query]
  exact logRun_fwd_bind π x (fun y => liftM (k y)) table

theorem logRun_liftM_compress (l r : Digest) (table : Table) :
    logRun π (liftM (compress l r) : OracleComp World Digest) table =
      pure (C π l r, (cin l r, π (cin l r)) :: table) := by
  unfold compress
  rw [logRun_liftM_fwd_bind]
  simp [C, cin, trunc]

theorem logRun_liftM_foldlM (siblings : List Digest) (m index : Nat) (node : Digest)
    (table : Table) :
    logRun π (liftM ((siblings.zipIdx m).foldlM (fun node (sibling, level) =>
        if (index >>> level) % 2 = 0 then compress node sibling else compress sibling node)
          node) : OracleComp World Digest) table =
      pure (pClimb π (index >>> m) node siblings,
        ((climbInputs π (index >>> m) node siblings).map fun x => (x, π x)).reverse ++
          table) := by
  induction siblings generalizing m node table with
  | nil => simp [pClimb, climbInputs]
  | cons s rest ih =>
    rw [List.zipIdx_cons, List.foldlM_cons, liftM_bind, logRun_bind]
    have hstep : (if (index >>> m) % 2 = 0 then compress node s else compress s node) =
        compress (children (index >>> m) node s).1 (children (index >>> m) node s).2 := by
      unfold children; split_ifs <;> rfl
    simp only [hstep, logRun_liftM_compress, pure_bind, ih]
    have hshift : index >>> (m + 1) = (index >>> m) >>> 1 := by
      rw [Nat.shiftRight_add]
    simp [pClimb, climbInputs, hshift]

/-- A coin-free computation records exactly its own path; for `climb`, one pair per level. -/
theorem logRun_liftM_climb (index : Nat) (leaf : Digest) (siblings : List Digest)
    (table : Table) :
    logRun π (liftM (climb index leaf siblings) : OracleComp World Digest) table =
      pure (pClimb π index leaf siblings,
        ((climbInputs π index leaf siblings).map fun x => (x, π x)).reverse ++ table) := by
  have h := logRun_liftM_foldlM π siblings 0 index leaf table
  rw [Nat.shiftRight_zero] at h
  exact h

/-! ### Counting bad answers -/

section Bound
open scoped Classical

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

/-- At most `2 ^ 1344` states have given low 256 bits. -/
theorem card_trunc_le (c : Digest) :
    (Finset.univ.filter fun y : State => trunc y = c).card ≤ 2 ^ 1344 := by
  have h : (Finset.univ.filter fun y : State => trunc y = c).card ≤
      (Finset.range (2 ^ 1344)).card := by
    apply Finset.card_le_card_of_injOn (fun y : State => y.toNat / 2 ^ 256)
    · intro y _
      simp only [Finset.coe_range, Set.mem_Iio]
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      exact y.isLt
    · intro y hy y' hy' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
      have hm : y.toNat % 2 ^ 256 = y'.toNat % 2 ^ 256 := by
        have := congrArg BitVec.toNat (hy.trans hy'.symm)
        simpa [trunc, DIGEST_BITS, DIGEST_BYTES] using this
      apply BitVec.eq_of_toNat_eq
      have h' : y.toNat / 2 ^ 256 = y'.toNat / 2 ^ 256 := h
      rw [← Nat.div_add_mod y.toNat (2 ^ 256), ← Nat.div_add_mod y'.toNat (2 ^ 256), h', hm]
  simpa using h

/-- At most `2 ^ 512` states have zero capacity. -/
theorem card_zeroCap_le : (Finset.univ.filter fun x : State => ZeroCap x).card ≤ 2 ^ 512 := by
  have h : (Finset.univ.filter fun x : State => ZeroCap x).card ≤
      (Finset.range (2 ^ 512)).card := by
    apply Finset.card_le_card_of_injOn (fun x : State => x.toNat)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      simpa [ZeroCap, DIGEST_BITS, DIGEST_BYTES] using hx
    · intro x _ x' _ h
      exact BitVec.eq_of_toNat_eq h
  simpa using h

theorem good_cons_of_mem {p : State × State} {T : Table} (hp : p ∈ T) (hT : Good T) :
    Good (p :: T) := by
  intro a ha b hb
  have ha' : a ∈ T := by rcases List.mem_cons.mp ha with rfl | h <;> assumption
  have hb' : b ∈ T := by rcases List.mem_cons.mp hb with rfl | h <;> assumption
  exact hT a ha' b hb'

/-- A new pair `(x, y)` breaks goodness only if `x` has zero capacity and `trunc y` is already the
truncated output of some pair. -/
theorem of_not_good_cons {x y : State} {T : Table} (hT : Good T)
    (h : ¬ Good ((x, y) :: T)) : ZeroCap x ∧ ∃ p ∈ T, trunc p.2 = trunc y := by
  simp only [Good, not_forall] at h
  obtain ⟨a, ha, b, hb, hza, hzb, htr, hne⟩ := h
  rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
  · exact absurd rfl hne
  · exact ⟨hza, b, hb, htr.symm⟩
  · exact ⟨hzb, a, ha, htr⟩
  · exact absurd (hT a ha b hb hza hzb htr) hne

theorem length_le_of_mem_support {α : Type} {B : OracleComp World α} {table : Table}
    {p : α × Table} (hp : p ∈ support (logRun π B table)) : table.length ≤ p.2.length := by
  have hmem : (p.1, p.2.length) ∈
      support ((fun p => (p.1, p.2.length)) <$> logRun π B table) := by
    rw [support_map]; exact ⟨p, hp, rfl⟩
  rw [map_logRun, support_map] at hmem
  obtain ⟨q, _, hq⟩ := hmem
  simp only [Prod.mk.injEq] at hq
  omega

/-- The bound for one call made with `L` recorded pairs. -/
@[irreducible] noncomputable def pL (L : Nat) : ENNReal :=
  ((L * 2 ^ 1344 + 2 ^ 512 : Nat) : ENNReal) / ((2 ^ 1600 - L : Nat) : ENNReal)

theorem pL_def (L : Nat) :
    pL L = ((L * 2 ^ 1344 + 2 ^ 512 : Nat) : ENNReal) / ((2 ^ 1600 - L : Nat) : ENNReal) := by
  unfold pL; rfl

theorem sum_pL_succ (L n : Nat) :
    ∑ j ∈ Finset.range (n + 1), pL (L + j) =
      pL L + ∑ j ∈ Finset.range n, pL ((L + 1) + j) := by
  rw [Finset.sum_range_succ', add_comm, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [add_assoc, add_comm 1 j]

theorem sum_pL_mono (L n : Nat) :
    ∑ j ∈ Finset.range n, pL ((L + 1) + j) ≤ ∑ j ∈ Finset.range (n + 1), pL (L + j) := by
  rw [sum_pL_succ]; exact le_add_self

/-- **The induction.** Summed over the permutations consistent with a good table `T`, the
probability of losing goodness within `n` more calls is at most `|Ext T|` times
`∑_{j < n} pL (|T| + j)`. -/
theorem sum_Ext_probEvent_le {α : Type} (B : OracleComp World α) :
    ∀ (T : Table) (n : Nat), Good T →
      ∑ π ∈ Ext T, Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ T.length + n | logRun π B T] ≤
        (Ext T).card * ∑ j ∈ Finset.range n, pL (T.length + j) := by
  induction B using OracleComp.inductionOn with
  | pure a =>
    intro T n hT
    refine le_of_eq_of_le (Finset.sum_eq_zero fun π _ => ?_) bot_le
    rw [logRun_pure]
    refine probEvent_eq_zero fun p hp hE => ?_
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact hE.1 hT
  | query_bind t k ih =>
    intro T n hT
    rcases t with m | x | y
    · -- a coin: average over its value
      simp_rw [logRun_coin_bind, probEvent_bind_eq_tsum, tsum_fintype]
      rw [Finset.sum_comm]
      calc ∑ u, ∑ π ∈ Ext T, Pr[= u | (unifSpec.query m : ProbComp _)] *
              Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ T.length + n | logRun π (k u) T]
          = ∑ u, Pr[= u | (unifSpec.query m : ProbComp _)] *
              ∑ π ∈ Ext T, Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ T.length + n |
                logRun π (k u) T] := by simp_rw [Finset.mul_sum]
        _ ≤ ∑ u, Pr[= u | (unifSpec.query m : ProbComp _)] *
              ((Ext T).card * ∑ j ∈ Finset.range n, pL (T.length + j)) :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (ih u T n hT) zero_le
        _ = (∑ u, Pr[= u | (unifSpec.query m : ProbComp _)]) *
              ((Ext T).card * ∑ j ∈ Finset.range n, pL (T.length + j)) := by
            rw [Finset.sum_mul]
        _ ≤ 1 * ((Ext T).card * ∑ j ∈ Finset.range n, pL (T.length + j)) := by
            gcongr
            have h1 := tsum_probOutput_le_one (mx := (unifSpec.query m : ProbComp _))
            rwa [tsum_fintype] at h1
        _ = _ := one_mul _
    · -- a forward call `π x`
      simp_rw [logRun_fwd_bind]
      rcases n with _ | n
      · refine le_of_eq_of_le (Finset.sum_eq_zero fun π _ => ?_) bot_le
        refine probEvent_eq_zero fun p hp hE => ?_
        have := length_le_of_mem_support π hp
        simp at this; omega
      by_cases hx : ∃ p ∈ T, p.1 = x
      · -- `x` was already queried: its answer is fixed by `T`
        obtain ⟨p, hp, rfl⟩ := hx
        have hfix : ∀ π ∈ Ext T, π p.1 = p.2 := fun π hπ => mem_Ext.mp hπ p hp
        rw [Finset.sum_congr rfl fun π hπ => by rw [hfix π hπ]]
        have hthr : T.length + (n + 1) = (p :: T).length + n := by simp; omega
        simp only [hthr, Prod.mk.eta]
        refine (ih p.2 (p :: T) n (good_cons_of_mem hp hT)).trans_eq' ?_ |>.trans ?_
        · rw [Ext_cons_of_mem hp]
        · rw [Ext_cons_of_mem hp, List.length_cons]
          gcongr
          exact sum_pL_mono _ _
      · -- `x` is fresh: its answer is uniform outside the range of `T`
        push Not at hx
        rw [sum_pL_succ, pL_def]
        refine sum_le_of_fibers (Ext T) (fun π => π x) (2 ^ 1600 - T.length)
          (T.length * 2 ^ 1344 + 2 ^ 512) (by positivity) ?_
          (Finset.univ.filter fun z => ¬ Good ((x, z) :: T)) ?_ _
          (fun z π => Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ T.length + (n + 1) |
            logRun π (k z) ((x, z) :: T)]) (fun _ _ => probEvent_le_one) ?_
        · intro z; rw [← Ext_cons]; exact card_Ext_cons_mul_le T x hx z
        · calc (Finset.univ.filter fun z => ¬ Good ((x, z) :: T)).card
              ≤ (T.toFinset.biUnion fun p =>
                  Finset.univ.filter fun z : State => trunc z = trunc p.2).card := by
                apply Finset.card_le_card
                intro z hz
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
                obtain ⟨_, p, hp, htr⟩ := of_not_good_cons hT hz
                simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter,
                  Finset.mem_univ, true_and]
                exact ⟨p, hp, htr.symm⟩
            _ ≤ ∑ p ∈ T.toFinset, 2 ^ 1344 :=
                Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => card_trunc_le _)
            _ = T.toFinset.card * 2 ^ 1344 := by simp
            _ ≤ T.length * 2 ^ 1344 + 2 ^ 512 := by
                exact (Nat.mul_le_mul_right _ (List.toFinset_card_le T)).trans
                  (Nat.le_add_right _ _)
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hz
          rw [← Ext_cons]
          have hthr : T.length + (n + 1) = ((x, z) :: T).length + n := by simp; omega
          simp only [hthr]
          simpa using ih z ((x, z) :: T) n hz
    · -- an inverse call `π⁻¹ y`
      simp_rw [logRun_inv_bind]
      rcases n with _ | n
      · refine le_of_eq_of_le (Finset.sum_eq_zero fun π _ => ?_) bot_le
        refine probEvent_eq_zero fun p hp hE => ?_
        have := length_le_of_mem_support π hp
        simp at this; omega
      by_cases hy : ∃ p ∈ T, p.2 = y
      · -- `y` was already answered: its preimage is fixed by `T`
        obtain ⟨p, hp, rfl⟩ := hy
        have hfix : ∀ π ∈ Ext T, π.symm p.2 = p.1 := fun π hπ => by
          rw [← mem_Ext.mp hπ p hp, Equiv.symm_apply_apply]
        rw [Finset.sum_congr rfl fun π hπ => by rw [hfix π hπ]]
        have hthr : T.length + (n + 1) = (p :: T).length + n := by simp; omega
        simp only [hthr, Prod.mk.eta]
        refine (ih p.1 (p :: T) n (good_cons_of_mem hp hT)).trans_eq' ?_ |>.trans ?_
        · rw [Ext_cons_of_mem hp]
        · rw [Ext_cons_of_mem hp, List.length_cons]
          gcongr
          exact sum_pL_mono _ _
      · -- `y` is fresh: its preimage is uniform outside the domain of `T`
        push Not at hy
        rw [sum_pL_succ, pL_def]
        refine sum_le_of_fibers (Ext T) (fun π => π.symm y) (2 ^ 1600 - T.length)
          (T.length * 2 ^ 1344 + 2 ^ 512) (by positivity) ?_
          (Finset.univ.filter fun z => ¬ Good ((z, y) :: T)) ?_ _
          (fun z π => Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ T.length + (n + 1) |
            logRun π (k z) ((z, y) :: T)]) (fun _ _ => probEvent_le_one) ?_
        · intro z; rw [← Ext_cons_inv]; exact card_Ext_cons_mul_le_inv T y hy z
        · calc (Finset.univ.filter fun z => ¬ Good ((z, y) :: T)).card
              ≤ (Finset.univ.filter fun z : State => ZeroCap z).card := by
                apply Finset.card_le_card
                intro z hz
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
                exact (of_not_good_cons hT hz).1
            _ ≤ 2 ^ 512 := card_zeroCap_le
            _ ≤ T.length * 2 ^ 1344 + 2 ^ 512 := Nat.le_add_left _ _
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hz
          rw [← Ext_cons_inv]
          have hthr : T.length + (n + 1) = ((z, y) :: T).length + n := by simp; omega
          simp only [hthr]
          simpa using ih z ((z, y) :: T) n hz

end Bound

/-- **The collision bound.** Within `n` calls, the recorded table of any computation stops being
`Good` with probability at most `∑_{j < n} (j · 2^1344 + 2^512) / (2^1600 - j)`. -/
theorem probEvent_not_good_le {α : Type} (B : OracleComp World α) (n : Nat) :
    Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ n | do
        let π ← $ᵗ Perm
        logRun π B []] ≤
      ∑ j ∈ Finset.range n,
        ((j * 2 ^ 1344 + 2 ^ 512 : Nat) : ENNReal) / ((2 ^ 1600 - j : Nat) : ENNReal) := by
  have hmain := sum_Ext_probEvent_le B [] n (by simp [Good])
  have hExt : Ext [] = Finset.univ := by ext π; simp [mem_Ext]
  rw [hExt, Finset.card_univ] at hmain
  simp only [List.length_nil, zero_add] at hmain
  rw [probEvent_bind_eq_tsum, tsum_fintype]
  simp only [probOutput_uniformSample]
  rw [← Finset.mul_sum]
  have h0 : (Fintype.card Perm : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht : (Fintype.card Perm : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (Fintype.card Perm : ENNReal)⁻¹ * ∑ π, Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ n |
          logRun π B []]
      ≤ (Fintype.card Perm : ENNReal)⁻¹ *
          ((Fintype.card Perm : ENNReal) * ∑ j ∈ Finset.range n, pL j) :=
        by gcongr
    _ = ∑ j ∈ Finset.range n, pL j := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ = _ := Finset.sum_congr rfl fun j _ => pL_def j

end CommitGolf.Baseline
