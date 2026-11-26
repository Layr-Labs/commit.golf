import CommitGolfCandidate.ReconstructedBindingChains

namespace CommitGolfCandidate.Reconstruction.Binding

/-- A binary seed recognized by the high 16 bits of its right operand. The left
operand can be arbitrary; this includes every canonical parent input. -/
structure Seed where
  depth : Fin 24
  key : Key
  domain : key.2.2 >>> 48 = tag (depth.val+1)

theorem Seed.ext_key (a b : Seed) (eq : a.key = b.key) : a = b := by
  have tagEq := a.domain.symm.trans ((congrArg (fun k : Key => k.2.2 >>> 48) eq).trans b.domain)
  have inj : ∀ i j : Fin 24, tag (i.val+1) = tag (j.val+1) → i = j := by decide
  have d := inj _ _ tagEq
  cases a; cases b; simp_all

def Seed.ofPair (d : Fin 24) (l r : Digest) (cr : Canonical (d.val+1) r) : Seed :=
  ⟨d, pairKey (d.val+1) l r, marked_tag ⟨d.val+1, by omega⟩ (by simp) r cr⟩

theorem Seed.not_unary (s : Seed) (y : Digest) : s.key ≠ unary y := by
  intro eq
  have nozero : ∀ i : Fin 24, tag (i.val + 1) ≠ 0#64 := by decide
  have z := congrArg (fun k : Key => k.2.2 >>> 48) eq
  exact nozero s.depth (s.domain.symm.trans (by simpa [unary, zeroDigest] using z))

/-- Two completed chains never share any key under the full-output
collision-free condition, even when one has more continuation calls. -/
theorem disjoint_slots (rows : History) (C : Compress) (safe : ¬ FullCollision rows)
    (a b : Seed) (i j : Nat) (ca : recorded rows C a.key i) (cb : recorded rows C b.key j)
    (eq : lastKey C a.key i = lastKey C b.key j) : a = b ∧ i = j := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact ⟨Seed.ext_key _ _ eq,rfl⟩
    | succ j => exact False.elim (a.not_unary _ eq)
  | succ i ih =>
    cases j with
    | zero => exact False.elim (b.not_unary _ eq.symm)
    | succ j =>
      have answer : C (lastKey C a.key i) = C (lastKey C b.key j) := congrArg Prod.fst eq
      have k : lastKey C a.key i = lastKey C b.key j := by
        apply Classical.byContradiction
        intro ne
        exact safe ⟨_,_,_,ne, ca i (by omega), answer ▸ cb j (by omega)⟩
      have r := ih j (fun n h => ca n (by omega)) (fun n h => cb n (by omega)) k
      exact ⟨r.1,congrArg Nat.succ r.2⟩

def slots (C : Compress) (s : Seed) : List Key :=
  (List.range (work s.depth)).map (lastKey C s.key)

def Complete (rows : History) (C : Compress) (s : Seed) :=
  recorded rows C s.key (work s.depth-1)

private theorem seen_prefix {rows C s} (h : Complete rows C s) {j : Nat}
    (inRange : j ∈ List.range (work s.depth)) : recorded rows C s.key j := by
  have jlt := List.mem_range.1 inRange
  exact fun n hn => h n (by omega)

private theorem slots_nodup {C rows} (safe : ¬ FullCollision rows) (s : Seed)
    (h : Complete rows C s) : (slots C s).Nodup := by
  unfold slots List.Nodup
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem (R := (· ≠ ·)) _ List.nodup_range
  intro i j hi hj different same
  exact different (disjoint_slots rows C safe s s i j (seen_prefix h hi) (seen_prefix h hj) same).2

private theorem flatten_nodup {C rows} (safe : ¬ FullCollision rows)
    (seeds : List Seed) (nd : seeds.Nodup) (complete : ∀ s ∈ seeds, Complete rows C s) :
    (seeds.flatMap (slots C)).Nodup := by
  induction seeds with
  | nil => simp
  | cons s ss ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.1 nd
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨slots_nodup safe _ (complete _ (by simp)),ih tail (fun s h => complete s (by simp [h])),?_⟩
    intro x hx y hy same
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 hx
    obtain ⟨t,ht,mem⟩ := List.mem_flatMap.1 hy
    obtain ⟨j,hj,rfl⟩ := List.mem_map.1 mem
    have both := disjoint_slots rows C safe s t i j
      (seen_prefix (complete s (by simp)) hi) (seen_prefix (complete t (by simp [ht])) hj) same
    exact fresh (both.1 ▸ ht)

/-- The sum of scheduled work for deduplicated completed seeds is bounded
by the actual number of compression rows in the recorded transcript. -/
theorem total_paid_work {C rows} (safe : ¬ FullCollision rows) (seeds : List Seed)
    (nd : seeds.Nodup) (complete : ∀ s ∈ seeds, Complete rows C s) :
    (seeds.map (fun s => work s.depth)).sum ≤ rows.length := by
  have enters : seeds.flatMap (slots C) ⊆ rows.map Prod.fst := by
    intro k hk
    obtain ⟨s,hs,mem⟩ := List.mem_flatMap.1 hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.1 mem
    have row := (seen_prefix (complete s hs) hj) j (Nat.le_refl _)
    exact List.mem_map.2 ⟨_,row,rfl⟩
  have h := (flatten_nodup safe seeds nd complete).length_le_of_subset enters
  simpa [List.length_flatMap, slots, Function.comp_def] using h

end CommitGolfCandidate.Reconstruction.Binding
