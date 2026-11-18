import CommitGolfCandidate.PermLean.Leaf

/-! # Bridge from the hazard run to the contract's `Oracle.run` (B1–B4)

* (B1) `run_fst`: forgetting the hazard state, `run` is the contract's runner `Oracle.run` with its
  call count dropped (the record's `fixedOracleRun`).
* (B2) `step_spec`, `run_spec`, `run_consistent`: the log only grows, stays consistent with `σ`, and a final flag
  `false` means the final log is `Clean`.
* (B3) `flag_of_unclean`: an unclean final log raises the flag.
* (B4) `probePerm`: a paid replay of forward permutation queries whose returned pairs are all in
  the final log (the permutation analogue of the record's `probeInputs`).
* `perm_event_bound`: any event of the contract run that, on every reachable hazard run, forces
  the flag, has probability at most `hazardBudget H 0 q` over the uniform permutation, for every
  fixed compression table.

The unfolding lemmas for `Oracle.run` are the baseline certificate's (`Counting.lean`,
`CountingCoins.lean`), restated here because this file cannot import the submission. -/

namespace PermLean
open CommitGolf OracleComp OracleSpec
open scoped ENNReal

/-! ## Unfolding the contract runner (from the baseline `Counting.lean`) -/

theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

theorem oracle_run_bind (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    oracle.run (computation >>= continuation) =
      (do let (value, first) ← oracle.run computation
          let (result, second) ← oracle.run (continuation value)
          return (result, first + second)) := by
  simp only [Oracle.run, simulateQ_bind, WriterT.run_bind, map_eq_bind_pure_comp]
  rfl

theorem oracle_run_public (oracle : Oracle) (query : PublicSpec.Domain) :
    oracle.run (liftM (World.query (.inr query)) : OracleComp World (PublicSpec.Range query)) =
      pure (oracle.answer (m := Id) query, 1) := by
  rcases query with input | input
  · simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
      QueryImpl.withAddCost, QueryImpl.withCost]
    rfl
  · rcases input with input | input <;>
      simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
        QueryImpl.withAddCost, QueryImpl.withCost] <;> rfl

theorem oracle_run_private (oracle : Oracle) (query : unifSpec.Domain) :
    oracle.run (liftM (World.query (.inl query)) : OracleComp World (unifSpec.Range query)) =
      (fun answer => (answer, 0)) <$> (liftM (unifSpec.query query) : ProbComp _) := by
  simp [Oracle.run, Oracle.world, Oracle.callCost, QueryImpl.withAddCost, QueryImpl.withCost]
  rfl

/-! ## (B1) The hazard run is the contract run -/

theorem run_fst (H : Hazard) (C : Compression) (σ : Perm) {β : Type}
    (comp : OracleComp World β) (s : State) :
    Prod.fst <$> run H C σ comp s = Prod.fst <$> (⟨C, σ⟩ : Oracle).run comp := by
  induction comp using OracleComp.inductionOn generalizing s with
  | pure value =>
    rw [run_pure, oracle_run_pure]
    simp
  | query_bind t next ih =>
    rw [run_query_bind, oracle_run_bind]
    rcases t with coins | publicQuery
    · rw [oracle_run_private]
      simp only [step, map_bind, bind_map_left, ih]
      simp only [map_eq_bind_pure_comp, Function.comp_apply, pure_bind]
      rfl
    · rw [oracle_run_public]
      rcases publicQuery with x | permQuery
      · simp only [step, pure_bind, ih]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      · rcases permQuery with x | y
        · simp only [step, pure_bind, ih]
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
          rfl
        · simp only [step, pure_bind, ih]
          simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
          rfl

/-! ## (B2) Invariants of the hazard run -/

theorem hit_false {S : Finset Word} {w : Word} (h : hit S w = false) : w ∉ S := by
  unfold hit at h
  exact of_decide_eq_false h

theorem clean_nil (H : Hazard) : Clean H [] := by
  intro pre e post split
  simp at split

/-- Appending a hazard-free entry keeps a log clean. -/
theorem clean_append {H : Hazard} {log : Log Word} (clean : Clean H log) (e : Entry Word)
    (fresh : (e.inverse = false → e.output ∉ H.forward log e.input) ∧
      (e.inverse = true → e.input ∉ H.inverse log e.output)) :
    Clean H (log ++ [e]) := by
  intro pre e' post split
  rcases List.eq_nil_or_concat post with rfl | ⟨rest, last, rfl⟩
  · have both : log = pre ∧ e = e' := by simpa using split
    obtain ⟨rfl, rfl⟩ := both
    exact fresh
  · have split' : log ++ [e] = (pre ++ e' :: rest) ++ [last] := by rw [split]; simp
    obtain ⟨same, _⟩ := List.append_inj' split' rfl
    exact clean pre e' rest same

/-- The run's invariant: every entry is consistent with `σ`, and a clear flag means clean. -/
def Inv (H : Hazard) (σ : Perm) (s : State) : Prop :=
  (∀ e ∈ s.1, σ e.input = e.output) ∧ (s.2 = false → Clean H s.1)

theorem step_spec (H : Hazard) (C : Compression) (σ : Perm) (s : State) (t : World.Domain)
    (r : World.Range t × State) (hr : r ∈ support (step H C σ s t)) :
    (Inv H σ s → Inv H σ r.2) ∧ s.1 <+: r.2.1 := by
  rcases t with coins | publicQuery
  · simp only [step, support_map, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact ⟨id, List.prefix_refl _⟩
  · rcases publicQuery with x | permQuery
    · simp only [step, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨id, List.prefix_refl _⟩
    · rcases permQuery with x | y
      · simp only [step, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        by_cases known : x ∈ s.1.inputs
        · simp only [known, ite_true]
          exact ⟨id, List.prefix_refl _⟩
        · simp only [known, ite_false]
          refine ⟨fun inv => ⟨?_, ?_⟩, List.prefix_append _ _⟩
          · intro e he
            rcases List.mem_append.mp he with old | new
            · exact inv.1 e old
            · rw [List.mem_singleton.mp new]
          · intro clear
            rw [Bool.or_eq_false_iff] at clear
            exact clean_append (inv.2 clear.1) _
              ⟨fun _ => hit_false clear.2, fun impossible => by simp at impossible⟩
      · simp only [step, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        by_cases known : y ∈ s.1.outputs
        · simp only [known, ite_true]
          exact ⟨id, List.prefix_refl _⟩
        · simp only [known, ite_false]
          refine ⟨fun inv => ⟨?_, ?_⟩, List.prefix_append _ _⟩
          · intro e he
            rcases List.mem_append.mp he with old | new
            · exact inv.1 e old
            · rw [List.mem_singleton.mp new]
              exact Equiv.apply_symm_apply σ y
          · intro clear
            rw [Bool.or_eq_false_iff] at clear
            exact clean_append (inv.2 clear.1) _
              ⟨fun impossible => by simp at impossible, fun _ => hit_false clear.2⟩

theorem run_spec (H : Hazard) (C : Compression) (σ : Perm) {β : Type}
    (comp : OracleComp World β) :
    ∀ (s : State) (r : β × State), r ∈ support (run H C σ comp s) →
      (Inv H σ s → Inv H σ r.2) ∧ s.1 <+: r.2.1 := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro s r hr
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨id, List.prefix_refl _⟩
  | query_bind t next ih =>
    intro s r hr
    rw [run_query_bind] at hr
    obtain ⟨mid, hmid, hr'⟩ := (mem_support_bind_iff _ _ _).mp hr
    obtain ⟨inv₁, pre₁⟩ := step_spec H C σ s t mid hmid
    obtain ⟨inv₂, pre₂⟩ := ih mid.1 mid.2 r hr'
    exact ⟨fun inv => inv₂ (inv₁ inv), pre₁.trans pre₂⟩

/-- (B3) A final log that is not clean has raised the flag. -/
theorem flag_of_unclean (H : Hazard) (C : Compression) (σ : Perm) {β : Type}
    (comp : OracleComp World β) (r : β × State)
    (hr : r ∈ support (run H C σ comp ([], false))) (unclean : ¬ Clean H r.2.1) :
    r.2.2 = true := by
  have inv := (run_spec H C σ comp ([], false) r hr).1
    ⟨fun e he => by simp at he, fun _ => clean_nil H⟩
  by_contra clear
  exact unclean (inv.2 (by simpa using clear))

/-- Every final log entry is a true evaluation of `σ`. -/
theorem run_consistent (H : Hazard) (C : Compression) (σ : Perm) {β : Type}
    (comp : OracleComp World β) (r : β × State)
    (hr : r ∈ support (run H C σ comp ([], false))) :
    ∀ e ∈ r.2.1, σ e.input = e.output :=
  ((run_spec H C σ comp ([], false) r hr).1
    ⟨fun e he => by simp at he, fun _ => clean_nil H⟩).1

/-- The hazard run respects sequencing. -/
theorem run_bind (H : Hazard) (C : Compression) (σ : Perm) {α β : Type}
    (comp : OracleComp World α) (f : α → OracleComp World β) (s : State) :
    run H C σ (comp >>= f) s = run H C σ comp s >>= fun r => run H C σ (f r.1) r.2 := by
  induction comp using OracleComp.inductionOn generalizing s with
  | pure value =>
    rw [pure_bind, run_pure, pure_bind]
  | query_bind t next ih =>
    rw [bind_assoc, run_query_bind, run_query_bind, bind_assoc]
    congr 1
    funext r
    exact ih r.1 r.2

/-! ## (B4) Paid replay of forward permutation queries -/

/-- Query `P` on each input and return the pairs. -/
def probePerm : List Word → OracleComp World (List (Word × Word))
  | [] => pure []
  | x :: rest => do
      let y ← (liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World Word)
      let replies ← probePerm rest
      return (x, y) :: replies

/-- Every replayed input is in the final log, and the replies are the true evaluations. -/
theorem probePerm_logged (H : Hazard) (C : Compression) (σ : Perm) :
    ∀ (xs : List Word) (s : State) (r : List (Word × Word) × State),
      r ∈ support (run H C σ (probePerm xs) s) →
        r.1 = xs.map (fun x => (x, σ x)) ∧ ∀ x ∈ xs, x ∈ r.2.1.inputs := by
  intro xs
  induction xs with
  | nil =>
    intro s r hr
    simp only [probePerm] at hr
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp
  | cons x rest ih =>
    intro s r hr
    simp only [probePerm] at hr
    rw [run_query_bind] at hr
    obtain ⟨mid, hmid, hr'⟩ := (mem_support_bind_iff _ _ _).mp hr
    simp only [step, support_pure, Set.mem_singleton_iff] at hmid
    subst hmid
    set s' : State := if x ∈ s.1.inputs then s
      else (s.1 ++ [⟨x, σ x, false⟩], s.2 || hit (H.forward s.1 x) (σ x)) with hs'
    have logged : x ∈ s'.1.inputs := by
      by_cases known : x ∈ s.1.inputs
      · simp only [hs', known, ite_true]
      · simp only [hs', known, ite_false, Log.inputs, List.map_append, List.mem_append]
        simp
    rw [run_bind] at hr'
    obtain ⟨inner, hinner, hfinal⟩ := (mem_support_bind_iff _ _ _).mp hr'
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hfinal
    subst hfinal
    obtain ⟨replies, inputs⟩ := ih s' inner hinner
    have grows := (run_spec H C σ (probePerm rest) s' inner hinner).2
    refine ⟨by simp [replies], ?_⟩
    intro x' hx'
    rcases List.mem_cons.mp hx' with rfl | later
    · obtain ⟨e, he, hx⟩ := List.mem_map.mp logged
      exact List.mem_map.mpr ⟨e, grows.subset he, hx⟩
    · exact inputs x' later

/-! ## Probability of a detected event -/

/-- **Bridge to the contract.** For a fixed compression table, an event of the contract run that
raises the hazard flag on every reachable hazard run has probability at most `hazardBudget`. -/
theorem perm_event_bound (H : Hazard) (C : Compression) {β : Type} (comp : OracleComp World β)
    (q : ℕ) (bounded : PublicQueryBound comp q) (event : β → Prop)
    (detect : ∀ (σ : Perm) (r : β × State), r ∈ support (run H C σ comp ([], false)) →
      event r.1 → r.2.2 = true) :
    Pr{let x ← ($ᵗ Perm >>= fun σ => Prod.fst <$> (⟨C, σ⟩ : Oracle).run comp)}[event x] ≤
      hazardBudget H 0 q := by
  refine le_trans ?_ (hazard_bound H C comp q bounded)
  apply prEvent_bind_mono_of_forall_le_of_support
  intro σ _
  rw [← run_fst H C σ comp ([], false), prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun r hr hev => detect σ r hr hev

/-! ## The spec v1 detector -/

/-- A permutation collision of spec v1, read from returned replies only: the four evaluations of
two different values whose `h` agree. -/
def PermCollision (replies : List (Word × Word)) : Prop :=
  ∃ v v' : BitVec 2048, v ≠ v' ∧ ∃ y₁ y₂ y₁' y₂' : Word,
    (leafX1 v, y₁) ∈ replies ∧ (leafX2 v y₁, y₂) ∈ replies ∧
    (leafX1 v', y₁') ∈ replies ∧ (leafX2 v' y₁', y₂') ∈ replies ∧
    v1.digest y₂ = v1.digest y₂'

/-- Logged true replies with a permutation collision raise the `leafHazard` flag. -/
theorem perm_collision_flag (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β)
    (r : β × State) (hr : r ∈ support (run leafHazard C σ comp ([], false)))
    (replies : List (Word × Word))
    (logged : ∀ p ∈ replies, p.1 ∈ r.2.1.inputs ∧ p.2 = σ p.1)
    (collision : PermCollision replies) : r.2.2 = true := by
  apply flag_of_unclean leafHazard C σ comp r hr
  intro clean
  have entry : ∀ p ∈ replies, ∃ e ∈ r.2.1, e.input = p.1 ∧ e.output = p.2 := by
    intro p hp
    obtain ⟨member, value⟩ := logged p hp
    obtain ⟨e, he, hx⟩ := List.mem_map.mp member
    refine ⟨e, he, hx, ?_⟩
    rw [value, ← hx, run_consistent leafHazard C σ comp r hr e he]
  obtain ⟨v, v', different, y₁, y₂, y₁', y₂', p₁, p₂, p₁', p₂', same⟩ := collision
  obtain ⟨e₁, m₁, i₁, o₁⟩ := entry _ p₁
  obtain ⟨e₂, m₂, i₂, o₂⟩ := entry _ p₂
  obtain ⟨e₁', m₁', i₁', o₁'⟩ := entry _ p₁'
  obtain ⟨e₂', m₂', i₂', o₂'⟩ := entry _ p₂'
  exact leaf_hash_unclean (clean_leaf clean) different m₁ m₂ m₁' m₂' i₁ (by rw [i₂, o₁]) i₁'
    (by rw [i₂', o₁']) (by rw [o₂, o₂']; exact same)

/-- **Permutation half of the mixed detector.** For a search that ends by replaying `xs` through
`probePerm` and returns those replies, a permutation collision among them has probability at most
`q / 2^121` over the uniform permutation, for every compression table, when `search` followed by the replay makes at
most `q + extra` public calls (`1 ≤ q ≤ 2^120`, `extra ≤ 2^64`). -/
theorem perm_collision_bound (C : Compression) {β : Type} (search : OracleComp World β)
    (xs : β → List Word) (q extra : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (overhead : extra ≤ 2 ^ 64)
    (bounded : PublicQueryBound (search >>= fun b => probePerm (xs b)) (q + extra)) :
    Pr{let replies ← ($ᵗ Perm >>= fun σ =>
        Prod.fst <$> (⟨C, σ⟩ : Oracle).run (search >>= fun b => probePerm (xs b)))}[
      PermCollision replies] ≤ (q : ℝ≥0∞) / 2 ^ 121 := by
  refine (perm_event_bound leafHazard C _ (q + extra) bounded PermCollision ?_).trans
    (leaf_budget q extra positive small overhead)
  intro σ r hr collision
  rw [run_bind] at hr
  obtain ⟨mid, _, hr'⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨replies, inputs⟩ := probePerm_logged leafHazard C σ (xs mid.1) mid.2 r hr'
  have full : r ∈ support (run leafHazard C σ (search >>= fun b => probePerm (xs b)) ([], false)) := by
    rw [run_bind]
    exact (mem_support_bind_iff _ _ _).mpr ⟨mid, by assumption, hr'⟩
  refine perm_collision_flag C σ _ r full r.1 ?_ collision
  intro p hp
  rw [replies] at hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact ⟨inputs x hx, rfl⟩

/-- **Permutation half of the mixed detector, general form.** Any search whose returned replies
are, on every reachable hazard run, logged true evaluations: a permutation collision among them
has probability at most `q / 2^121` over the uniform permutation, for every compression table. -/
theorem perm_collision_bound_of_logged (C : Compression) {β : Type} (search : OracleComp World β)
    (replies : β → List (Word × Word)) (q extra : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (overhead : extra ≤ 2 ^ 64) (bounded : PublicQueryBound search (q + extra))
    (replied : ∀ (σ : Perm) (r : β × State), r ∈ support (run leafHazard C σ search ([], false)) →
      ∀ p ∈ replies r.1, p.1 ∈ r.2.1.inputs ∧ p.2 = σ p.1) :
    Pr{let x ← ($ᵗ Perm >>= fun σ => Prod.fst <$> (⟨C, σ⟩ : Oracle).run search)}[
      PermCollision (replies x)] ≤ (q : ℝ≥0∞) / 2 ^ 121 :=
  (perm_event_bound leafHazard C search (q + extra) bounded (fun x => PermCollision (replies x))
    fun σ r hr collision => perm_collision_flag C σ search r hr (replies r.1)
      (replied σ r hr) collision).trans (leaf_budget q extra positive small overhead)

/-- The dependent two-call replay of one leaf: `x₁`, then `x₂ = leafX2 v y₁`. -/
def probeLeaf (v : BitVec 2048) : OracleComp World (List (Word × Word)) := do
  let y₁ ← (liftM (World.query (.inr (.inr (.inl (leafX1 v))))) : OracleComp World Word)
  let y₂ ← (liftM (World.query (.inr (.inr (.inl (leafX2 v y₁))))) : OracleComp World Word)
  return [(leafX1 v, y₁), (leafX2 v y₁, y₂)]

theorem forward_logged (H : Hazard) (σ : Perm) (s : State) (x : Word) :
    x ∈ (if x ∈ s.1.inputs then s
      else (s.1 ++ [⟨x, σ x, false⟩], s.2 || hit (H.forward s.1 x) (σ x))).1.inputs := by
  by_cases known : x ∈ s.1.inputs
  · simp only [known, ite_true]
  · simp only [known, ite_false, Log.inputs, List.map_append, List.mem_append]
    simp

/-- One forward step answers `σ x`, logs `x` and only extends the log. -/
theorem forward_step (H : Hazard) (C : Compression) (σ : Perm) (s : State) (x : Word)
    (mid : Word × State) (hmid : mid ∈ support (step H C σ s (.inr (.inr (.inl x))))) :
    mid.1 = σ x ∧ x ∈ mid.2.1.inputs ∧ s.1 <+: mid.2.1 := by
  have grows := (step_spec H C σ s (.inr (.inr (.inl x))) mid hmid).2
  simp only [step, support_pure, Set.mem_singleton_iff] at hmid
  subst hmid
  exact ⟨rfl, forward_logged H σ s x, grows⟩

/-- The leaf replay returns the true evaluations, all logged. -/
theorem probeLeaf_logged (H : Hazard) (C : Compression) (σ : Perm) (v : BitVec 2048)
    (s : State) (r : List (Word × Word) × State) (hr : r ∈ support (run H C σ (probeLeaf v) s)) :
    ∀ p ∈ r.1, p.1 ∈ r.2.1.inputs ∧ p.2 = σ p.1 := by
  simp only [probeLeaf] at hr
  rw [run_query_bind] at hr
  obtain ⟨mid, hmid, hr'⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨answer₁, logged₁, -⟩ := forward_step H C σ s (leafX1 v) mid hmid
  rw [run_query_bind] at hr'
  obtain ⟨mid', hmid', hr''⟩ := (mem_support_bind_iff _ _ _).mp hr'
  obtain ⟨answer₂, logged₂, grows⟩ := forward_step H C σ mid.2 (leafX2 v mid.1) mid' hmid'
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hr''
  subst hr''
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · refine ⟨?_, answer₁⟩
    obtain ⟨e, he, hx⟩ := List.mem_map.mp logged₁
    exact List.mem_map.mpr ⟨e, grows.subset he, hx⟩
  · exact ⟨logged₂, answer₂⟩

end PermLean
