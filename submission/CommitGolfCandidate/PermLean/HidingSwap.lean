import CommitGolf.Statements
import VCVio.EvalDist.MeasureTVDist.Basic
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.ProbabilityNotation
import VCVio.OracleComp.Constructions.SampleableType.Basic
import ToMathlib.Probability.UniformOn

/-! # Swap coupling for permutation-based hiding

A two-stage adversary runs against a uniform `σ : Perm` and a fixed compression table `C`.
Stage one (`A₁`, the choose phase) outputs `c`. A salt `s` is drawn. The honest middle is a
deterministic function `view b c s σ` (root and proof of message `b`). Stage two (`A₂`) sees it.

If a permutation `τ c s σ` supported on a set `S c s σ` turns the world-1 view under
`σ * τ` into the world-0 view under `σ`, and `S`, `τ` do not move when `σ` is replaced by
`σ * τ` (they depend on `σ` only off `S`), then the two output distributions are within the
probability that some adversary query (either stage) touches `S`: a forward query at a point of
`S`, or an inverse query whose answer lies in `S`.

No lazy sampling: the proof partitions the sum over `σ` by stage-one answers and reindexes
each fibre by the involution `σ ↦ σ * τ`. Nothing unfolds `2 ^ 1600` or decides over `BitVec`.

Main results.
* Step 1: `swap_coupling` (generic), `leaf_swap_coupling`, `simulateQ_world_eq`, `hiding_le_bad`,
  `leaf_hiding_le_bad`: the contract's `runHiding` distance is at most the touch probability.
* Step 2: `bad_le`: touch probability `≤ 4 t / |U| + Pr[RH]`, by cutting stage two at the first
  touch of `S(s) ∪ S(s*)` for an independent reference salt `s*` and coupling
  `(s, s*, σ) ↦ (exchange, σ * τ*)` (`runCut_swap`).
* R3c, the range hit: `hazard_cut` (cut runs inside a permutation class), `fibre_hazard` (swap
  closure under equal-prefix transpositions), `stage_one_bound` (QueryBound budget through stage
  one), `SaltLayout.rh_class_bound`, `rh_whole_bound`, and `rh_le` (`Pr[RH] ≤ t / |U|` for
  128-bit salts, at most `2^24` positions, prefix classes of at least `2^1344` words).
* R4: `leaf_hiding_error` (the `min 1` split) and the contract-level `scheme_hiding_R2`:
  `scheme.Hiding HIDING_ERROR` with only the R2 hypotheses (layouts `SL`, uniform salts, the view
  `F` with `hF` and `hFpre`, and the machine refinement `hhonest`). `scheme_hiding` is the same
  with the range hit `hRH` as a hypothesis. `scheme_hiding_digest` fixes the prefix map to the
  32-byte digest `digestOf` (bits `[0, 256)`), whose classes have `2^1344` words (`digest_fiber`).
-/

namespace HSwap
open CommitGolf OracleComp OracleSpec
open scoped ENNReal

abbrev PWord := BitVec PERMUTATION_WIDTH

/-! ## Running an adversary against a fixed permutation, logging touched points -/

/-- One query: coins are forwarded, compression uses `C`, a forward query at `x` logs `x`,
an inverse query at `y` logs its answer `σ⁻¹ y`. -/
def stepLog (C : Compression) (σ : Perm) {γ : Type} :
    (t : World.Domain) → (World.Range t → ProbComp (γ × List PWord)) → ProbComp (γ × List PWord)
  | .inl coins, k => (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>= k
  | .inr (.inl x), k => k (C x)
  | .inr (.inr (.inl x)), k => (fun z => (z.1, x :: z.2)) <$> k (σ x)
  | .inr (.inr (.inr y)), k => (fun z => (z.1, σ.symm y :: z.2)) <$> k (σ.symm y)

/-- Run against fixed `C, σ`; the list holds every touched permutation input, in query order. -/
def runLog (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    ProbComp (β × List PWord) :=
  OracleComp.recOn comp (fun value => pure (value, []))
    (fun t _ next => stepLog C σ t next)

theorem runLog_pure (C : Compression) (σ : Perm) {β : Type} (value : β) :
    runLog C σ (pure value : OracleComp World β) = pure (value, []) := rfl

theorem runLog_query_bind (C : Compression) (σ : Perm) {β : Type} (t : World.Domain)
    (next : World.Range t → OracleComp World β) :
    runLog C σ ((liftM (World.query t) : OracleComp World _) >>= next) =
      stepLog C σ t (fun a => runLog C σ (next a)) := rfl

/-- No touched point lies in `S`. -/
def Clean (S : Finset PWord) (l : List PWord) : Prop := ∀ x ∈ l, x ∉ S

theorem clean_cons {S : Finset PWord} {x : PWord} {l : List PWord} :
    Clean S (x :: l) ↔ x ∉ S ∧ Clean S l := List.forall_mem_cons

theorem clean_append {S : Finset PWord} {l l' : List PWord} :
    Clean S (l ++ l') ↔ Clean S l ∧ Clean S l' := List.forall_mem_append

/-! ## Identical until touch -/

theorem symm_fix {τ : Perm} {S : Finset PWord} (hfix : ∀ x, x ∉ S → τ x = x) {x : PWord}
    (hx : x ∉ S) : τ.symm x = x := by
  rw [Equiv.symm_apply_eq]
  exact (hfix x hx).symm

theorem symm_mem {τ : Perm} {S : Finset PWord} (hfix : ∀ x, x ∉ S → τ x = x) {x : PWord}
    (hx : x ∈ S) : τ.symm x ∈ S := by
  by_contra h
  have back := hfix _ h
  rw [Equiv.apply_symm_apply] at back
  rw [← back] at h
  exact h hx

theorem mul_symm_apply (σ τ : Perm) (y : PWord) : (σ * τ).symm y = τ.symm (σ.symm y) := by
  rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Identical until touch.** If `τ` fixes every point outside `S`, then running against
`σ * τ` or against `σ` gives the same mass to every event of a run that never touches `S`. -/
theorem runLog_swap (C : Compression) (S : Finset PWord) (τ : Perm)
    (hfix : ∀ x, x ∉ S → τ x = x) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    ∀ p : β × List PWord → Prop,
      Pr{let z ← runLog C (σ * τ) comp}[p z ∧ Clean S z.2] =
        Pr{let z ← runLog C σ comp}[p z ∧ Clean S z.2] := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro p; rfl
  | query_bind t next ih =>
    intro p
    rw [runLog_query_bind, runLog_query_bind]
    rcases t with coins | publicQuery
    · exact prEvent_bind_congr _ _ _ _ _ fun a => ih a p
    · rcases publicQuery with x | permQuery
      · exact ih (C x) p
      · rcases permQuery with x | y
        · simp only [stepLog]
          rw [prEvent_map, prEvent_map]
          by_cases hx : x ∈ S
          · rw [prEvent_eq_zero_of_forall_not _ _ fun z hz => (clean_cons.mp hz.2).1 hx,
              prEvent_eq_zero_of_forall_not _ _ fun z hz => (clean_cons.mp hz.2).1 hx]
          · have same : (σ * τ) x = σ x := by rw [Equiv.Perm.mul_apply, hfix x hx]
            rw [same]
            have shape : ∀ z : β × List PWord,
                (p (z.1, x :: z.2) ∧ Clean S (x :: z.2)) ↔ (p (z.1, x :: z.2) ∧ Clean S z.2) := by
              intro z
              rw [clean_cons]
              exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hx, h.2⟩⟩
            rw [prEvent_congr _ _ _ shape, prEvent_congr _ _ _ shape]
            exact ih (σ x) (fun z => p (z.1, x :: z.2))
        · simp only [stepLog]
          rw [prEvent_map, prEvent_map]
          by_cases hy : σ.symm y ∈ S
          · have moved : (σ * τ).symm y ∈ S := by
              rw [mul_symm_apply]; exact symm_mem hfix hy
            rw [prEvent_eq_zero_of_forall_not _ _ fun z hz => (clean_cons.mp hz.2).1 moved,
              prEvent_eq_zero_of_forall_not _ _ fun z hz => (clean_cons.mp hz.2).1 hy]
          · have same : (σ * τ).symm y = σ.symm y := by
              rw [mul_symm_apply]; exact symm_fix hfix hy
            rw [same]
            have shape : ∀ z : β × List PWord,
                (p (z.1, σ.symm y :: z.2) ∧ Clean S (σ.symm y :: z.2)) ↔
                  (p (z.1, σ.symm y :: z.2) ∧ Clean S z.2) := by
              intro z
              rw [clean_cons]
              exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hy, h.2⟩⟩
            rw [prEvent_congr _ _ _ shape, prEvent_congr _ _ _ shape]
            exact ih (σ.symm y) (fun z => p (z.1, σ.symm y :: z.2))

/-! ## Permutations consistent with a log of pairs -/

abbrev PLog := List (PWord × PWord)

/-- Permutations consistent with every logged pair `σ x = y`. -/
@[irreducible] noncomputable def ext (L : PLog) : Finset Perm := by
  classical
  exact Finset.univ.filter fun σ => ∀ e ∈ L, σ e.1 = e.2

theorem mem_ext {L : PLog} {σ : Perm} : σ ∈ ext L ↔ ∀ e ∈ L, σ e.1 = e.2 := by
  classical
  unfold ext
  simp

theorem ext_nil : ext ([] : PLog) = Finset.univ := by
  ext σ
  simp [mem_ext]

theorem mem_ext_append {L : PLog} {e : PWord × PWord} {σ : Perm} :
    σ ∈ ext (L ++ [e]) ↔ σ ∈ ext L ∧ σ e.1 = e.2 := by
  simp only [mem_ext, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]

/-- Partition by a forward answer. -/
theorem sum_ext_forward (L : PLog) (x : PWord) (G : Perm → PWord → ℝ≥0∞) :
    ∑ σ ∈ ext L, G σ (σ x) = ∑ y, ∑ σ ∈ ext (L ++ [(x, y)]), G σ y := by
  classical
  rw [← Finset.sum_fiberwise (ext L) (fun σ => σ x) (fun σ => G σ (σ x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have fibre : (ext L).filter (fun σ => σ x = y) = ext (L ++ [(x, y)]) := by
    ext σ
    rw [Finset.mem_filter, mem_ext_append]
  rw [fibre]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [(mem_ext_append.mp hσ).2]

/-- Partition by an inverse answer. -/
theorem sum_ext_inverse (L : PLog) (y : PWord) (G : Perm → PWord → ℝ≥0∞) :
    ∑ σ ∈ ext L, G σ (σ.symm y) = ∑ x, ∑ σ ∈ ext (L ++ [(x, y)]), G σ x := by
  classical
  rw [← Finset.sum_fiberwise (ext L) (fun σ => σ.symm y) (fun σ => G σ (σ.symm y))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have fibre : (ext L).filter (fun σ => σ.symm y = x) = ext (L ++ [(x, y)]) := by
    ext σ
    rw [Finset.mem_filter, mem_ext_append, Equiv.symm_apply_eq]
    exact and_congr Iff.rfl eq_comm
  rw [fibre]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h : σ x = y := (mem_ext_append.mp hσ).2
  rw [show σ.symm y = x by rw [Equiv.symm_apply_eq, h]]

/-! ## Fibrewise steps -/

/-- A draw from a finite type that ignores `σ` passes a fibrewise equality through. -/
theorem coin_step {ι α : Type} [Fintype ι] (mx : ProbComp ι) (f g : ι → Perm → ProbComp α)
    (s : Finset Perm) (q : α → Prop)
    (h : ∀ a, ∑ σ ∈ s, Pr{let z ← f a σ}[q z] = ∑ σ ∈ s, Pr{let z ← g a σ}[q z]) :
    ∑ σ ∈ s, Pr{let z ← (mx >>= fun a => f a σ)}[q z] =
      ∑ σ ∈ s, Pr{let z ← (mx >>= fun a => g a σ)}[q z] := by
  simp only [prEvent_bind_eq_sum_fintype]
  rw [Finset.sum_comm, Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h a]

theorem forward_step (L : PLog) (x : PWord) (F : Bool → Perm → PWord → ℝ≥0∞)
    (h : ∀ a, ∑ σ ∈ ext (L ++ [(x, a)]), F false σ a = ∑ σ ∈ ext (L ++ [(x, a)]), F true σ a) :
    ∑ σ ∈ ext L, F false σ (σ x) = ∑ σ ∈ ext L, F true σ (σ x) := by
  rw [sum_ext_forward L x (F false), sum_ext_forward L x (F true)]
  exact Finset.sum_congr rfl fun a _ => h a

theorem inverse_step (L : PLog) (y : PWord) (F : Bool → Perm → PWord → ℝ≥0∞)
    (h : ∀ a, ∑ σ ∈ ext (L ++ [(a, y)]), F false σ a = ∑ σ ∈ ext (L ++ [(a, y)]), F true σ a) :
    ∑ σ ∈ ext L, F false σ (σ.symm y) = ∑ σ ∈ ext L, F true σ (σ.symm y) := by
  rw [sum_ext_inverse L y (F false), sum_ext_inverse L y (F true)]
  exact Finset.sum_congr rfl fun a _ => h a

/-! ## Stage one: from a fibrewise equality to the whole sum -/

/-- If two continuations give equal summed event masses over every log-consistent set of
permutations, then so do the stage-one run followed by either continuation. The continuation
receives stage one's output and every point stage one touched. -/
theorem stage_one_sum (C : Compression) {γ α : Type} (comp : OracleComp World γ)
    (K : Bool → γ → List PWord → Perm → ProbComp α) (q : α → Prop)
    (hK : ∀ (L : PLog) (c : γ),
      ∑ σ ∈ ext L, Pr{let z ← K false c (L.map Prod.fst) σ}[q z] =
        ∑ σ ∈ ext L, Pr{let z ← K true c (L.map Prod.fst) σ}[q z]) :
    ∀ L : PLog,
      ∑ σ ∈ ext L, Pr{let z ← (runLog C σ comp >>= fun r =>
          K false r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
        ∑ σ ∈ ext L, Pr{let z ← (runLog C σ comp >>= fun r =>
          K true r.1 (L.map Prod.fst ++ r.2) σ)}[q z] := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro L
    simp only [runLog_pure, pure_bind, List.append_nil]
    exact hK L value
  | query_bind t next ih =>
    intro L
    rcases t with coins | publicQuery
    · have unfold : ∀ (b : Bool) (σ : Perm),
          Pr{let z ← (stepLog C σ (.inl coins) (fun a => runLog C σ (next a)) >>= fun r =>
            K b r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
          Pr{let z ← ((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>= fun a =>
            (runLog C σ (next a) >>= fun r => K b r.1 (L.map Prod.fst ++ r.2) σ))}[q z] :=
        fun b σ => by
          show Pr{let z ← (((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
            fun a => runLog C σ (next a)) >>= fun r => K b r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
          rw [bind_assoc]
      refine (Finset.sum_congr rfl fun σ _ => unfold false σ).trans ?_
      refine Eq.trans ?_ (Finset.sum_congr rfl fun σ _ => unfold true σ).symm
      exact coin_step _ _ _ _ q fun a => ih a L
    · rcases publicQuery with x | permQuery
      · exact ih (C x) L
      · rcases permQuery with x | y
        · have unfold : ∀ (b : Bool) (σ : Perm),
              Pr{let z ← (stepLog C σ (.inr (.inr (.inl x))) (fun a => runLog C σ (next a)) >>=
                fun r => K b r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
              Pr{let z ← (runLog C σ (next (σ x)) >>= fun r =>
                K b r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q z] :=
            fun b σ => by
              show Pr{let z ← (((fun z => (z.1, x :: z.2)) <$> runLog C σ (next (σ x))) >>=
                fun r => K b r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
              rw [bind_map_left]
          refine (Finset.sum_congr rfl fun σ _ => unfold false σ).trans ?_
          refine Eq.trans ?_ (Finset.sum_congr rfl fun σ _ => unfold true σ).symm
          refine forward_step L x (fun b σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
            K b r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q z]) fun a => ?_
          have h := ih a (L ++ [(x, a)])
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] at h
          exact h
        · have unfold : ∀ (b : Bool) (σ : Perm),
              Pr{let z ← (stepLog C σ (.inr (.inr (.inr y))) (fun a => runLog C σ (next a)) >>=
                fun r => K b r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
              Pr{let z ← (runLog C σ (next (σ.symm y)) >>= fun r =>
                K b r.1 (L.map Prod.fst ++ σ.symm y :: r.2) σ)}[q z] :=
            fun b σ => by
              show Pr{let z ← (((fun z => (z.1, σ.symm y :: z.2)) <$>
                runLog C σ (next (σ.symm y))) >>=
                fun r => K b r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
              rw [bind_map_left]
          refine (Finset.sum_congr rfl fun σ _ => unfold false σ).trans ?_
          refine Eq.trans ?_ (Finset.sum_congr rfl fun σ _ => unfold true σ).symm
          refine inverse_step L y (fun b σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
            K b r.1 (L.map Prod.fst ++ a :: r.2) σ)}[q z]) fun a => ?_
          have h := ih a (L ++ [(a, y)])
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] at h
          exact h

/-! ## The honest middle and stage two: reindexing by the swap involution -/

/-- An experiment's output: the adversary's output, every touched point, and the swap set. -/
abbrev Out (β : Type) := β × List PWord × Finset PWord

/-- Some adversary query, in either stage, touched the swap set. -/
def Bad {β : Type} (z : Out β) : Prop := ¬ Clean z.2.2 z.2.1

/-- Everything after stage one in world `b`: draw the salt, hand the honest view to stage two. -/
def tail (C : Compression) {γ β V Salt : Type} (salt : ProbComp Salt)
    (A₂ : γ → V → OracleComp World β) (view : Bool → γ → Salt → Perm → V)
    (S : γ → Salt → Perm → Finset PWord) (b : Bool) (c : γ) (l : List PWord) (σ : Perm) :
    ProbComp (Out β) :=
  salt >>= fun s => runLog C σ (A₂ c (view b c s σ)) >>= fun r => pure (r.1, l ++ r.2, S c s σ)

/-- **Base case.** For a fixed stage-one output `c` and log `L`, the swap `σ ↦ σ * τ c s σ` is an
involution of the log-consistent permutations whose log avoids `S`, maps world 1 to world 0,
and keeps every event away from `Bad`. -/
theorem base_swap (C : Compression) {γ β V Salt : Type} [Fintype Salt] (salt : ProbComp Salt)
    (A₂ : γ → V → OracleComp World β) (view : Bool → γ → Salt → Perm → V)
    (S : γ → Salt → Perm → Finset PWord) (τ : γ → Salt → Perm → Perm)
    (hfix : ∀ c s σ x, x ∉ S c s σ → τ c s σ x = x)
    (hS : ∀ c s σ, S c s (σ * τ c s σ) = S c s σ)
    (hinv : ∀ c s σ, σ * τ c s σ * τ c s (σ * τ c s σ) = σ)
    (hview : ∀ c s σ, view true c s (σ * τ c s σ) = view false c s σ)
    (p : Out β → Prop) (L : PLog) (c : γ) :
    ∑ σ ∈ ext L, Pr{let z ← tail C salt A₂ view S false c (L.map Prod.fst) σ}[p z ∧ ¬Bad z] =
      ∑ σ ∈ ext L, Pr{let z ← tail C salt A₂ view S true c (L.map Prod.fst) σ}[p z ∧ ¬Bad z] := by
  classical
  unfold tail
  refine coin_step salt
    (fun s σ => runLog C σ (A₂ c (view false c s σ)) >>= fun r =>
      pure (r.1, L.map Prod.fst ++ r.2, S c s σ))
    (fun s σ => runLog C σ (A₂ c (view true c s σ)) >>= fun r =>
      pure (r.1, L.map Prod.fst ++ r.2, S c s σ)) (ext L) _ fun s => ?_
  set l := L.map Prod.fst with hl
  let G : Bool → Perm → ℝ≥0∞ := fun b σ =>
    Pr{let z ← runLog C σ (A₂ c (view b c s σ))}[
      (p (z.1, l ++ z.2, S c s σ) ∧ Clean (S c s σ) l) ∧ Clean (S c s σ) z.2]
  have eval : ∀ b σ, Pr{let z ← (runLog C σ (A₂ c (view b c s σ)) >>= fun r =>
      pure (r.1, l ++ r.2, S c s σ))}[p z ∧ ¬Bad z] = G b σ := by
    intro b σ
    rw [bind_pure_comp, prEvent_map]
    apply prEvent_congr
    intro z
    simp only [Bad, not_not, clean_append]
    exact and_assoc.symm
  simp only [eval]
  have zero : ∀ b, ∀ σ ∈ ext L, G b σ ≠ 0 → Clean (S c s σ) l := by
    intro b σ _ nonzero
    by_contra dirty
    exact nonzero (prEvent_eq_zero_of_forall_not _ _ fun z hz => dirty hz.1.2)
  rw [← Finset.sum_filter_of_ne (zero false), ← Finset.sum_filter_of_ne (zero true)]
  have stays : ∀ σ ∈ (ext L).filter (fun σ => Clean (S c s σ) l),
      σ * τ c s σ ∈ (ext L).filter (fun σ => Clean (S c s σ) l) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨mem_ext.mpr fun e he => ?_, by rw [hS]; exact hσ.2⟩
    have input : e.1 ∈ l := by rw [hl]; exact List.mem_map_of_mem he
    rw [Equiv.Perm.mul_apply, hfix c s σ e.1 (hσ.2 e.1 input)]
    exact mem_ext.mp hσ.1 e he
  refine Finset.sum_nbij' (fun σ => σ * τ c s σ) (fun σ => σ * τ c s σ) stays stays
    (fun σ _ => hinv c s σ) (fun σ _ => hinv c s σ) fun σ hσ => ?_
  have clean := (Finset.mem_filter.mp hσ).2
  show G false σ = G true (σ * τ c s σ)
  simp only [G, hview, hS]
  exact (runLog_swap C (S c s σ) (τ c s σ) (hfix c s σ) σ (A₂ c (view false c s σ))
    fun z => p (z.1, l ++ z.2, S c s σ) ∧ Clean (S c s σ) l).symm

/-! ## The whole experiment -/

/-- A uniform sample puts the same mass on every point. -/
theorem uniform_point_eq {γ : Type} [SampleableType γ] (a b : γ) :
    Pr{let t ← ($ᵗ γ : ProbComp γ)}[t = a] = Pr{let t ← ($ᵗ γ : ProbComp γ)}[t = b] := by
  let : MeasurableSpace γ := ⊤
  let : Fintype γ := Fintype.ofFinite γ
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton,
    SampleableType.evalDist_uniformSample, ProbabilityTheory.uniformOn_univ_apply_singleton,
    ProbabilityTheory.uniformOn_univ_apply_singleton]

/-- World `b`: uniform `σ`, stage one, salt, honest view, stage two. -/
def experiment (C : Compression) {γ β V Salt : Type} (A₁ : OracleComp World γ)
    (salt : ProbComp Salt) (A₂ : γ → V → OracleComp World β)
    (view : Bool → γ → Salt → Perm → V) (S : γ → Salt → Perm → Finset PWord) (b : Bool) :
    ProbComp (Out β) :=
  ($ᵗ Perm : ProbComp Perm) >>= fun σ =>
    runLog C σ A₁ >>= fun r => tail C salt A₂ view S b r.1 r.2 σ

/-- Away from `Bad`, both worlds give every event the same mass. -/
theorem experiment_agree (C : Compression) {γ β V Salt : Type} [Fintype Salt]
    (A₁ : OracleComp World γ) (salt : ProbComp Salt)
    (A₂ : γ → V → OracleComp World β) (view : Bool → γ → Salt → Perm → V)
    (S : γ → Salt → Perm → Finset PWord) (τ : γ → Salt → Perm → Perm)
    (hfix : ∀ c s σ x, x ∉ S c s σ → τ c s σ x = x)
    (hS : ∀ c s σ, S c s (σ * τ c s σ) = S c s σ)
    (hinv : ∀ c s σ, σ * τ c s σ * τ c s (σ * τ c s σ) = σ)
    (hview : ∀ c s σ, view true c s (σ * τ c s σ) = view false c s σ)
    (p : Out β → Prop) :
    Pr{let z ← experiment C A₁ salt A₂ view S false}[p z ∧ ¬Bad z] =
      Pr{let z ← experiment C A₁ salt A₂ view S true}[p z ∧ ¬Bad z] := by
  unfold experiment
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype]
  have point : ∀ σ : Perm, Pr{let t ← ($ᵗ Perm : ProbComp Perm)}[t = σ] =
      Pr{let t ← ($ᵗ Perm : ProbComp Perm)}[t = 1] := fun σ => uniform_point_eq σ 1
  simp only [point]
  have h := stage_one_sum C A₁ (fun b c l σ => tail C salt A₂ view S b c l σ)
    (fun z => p z ∧ ¬Bad z)
    (fun L c => base_swap C salt A₂ view S τ hfix hS hinv hview p L c) []
  rw [ext_nil] at h
  simp only [List.map_nil, List.nil_append] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum, h]

/-- Total variation from agreement off a bad event (VCVio's `Event.lean`, not built here). -/
theorem etv_le_of_agree {α β : Type} [MeasurableSpace β] (mx my : ProbComp α) (f : α → β)
    (bad : α → Prop)
    (hagree : ∀ p : α → Prop,
      Pr{let x ← mx}[p x ∧ ¬bad x] = Pr{let y ← my}[p y ∧ ¬bad y])
    (hbad : Pr{let y ← my}[bad y] ≤ Pr{let x ← mx}[bad x]) :
    measureETVDist (f <$> mx) (f <$> my) ≤ Pr{let x ← mx}[bad x] := by
  refine iSup_le fun A => ?_
  have hsplit (mz : ProbComp α) : 𝒟[f <$> mz] A.1 =
      Pr{let x ← mz}[f x ∈ A.1 ∧ bad x] + Pr{let x ← mz}[f x ∈ A.1 ∧ ¬bad x] := by
    have h := prEvent_eq_evalDist (f <$> mz) (· ∈ A.1) A.2.mem
    rw [Set.ofPred_mem_eq] at h
    rw [← h, prEvent_map, prEvent_eq_prEvent_and_add_prEvent_and_not _ _ bad]
  rw [hsplit mx, hsplit my, hagree fun x => f x ∈ A.1]
  have h₁ : Pr{let x ← mx}[f x ∈ A.1 ∧ bad x] ≤ Pr{let x ← mx}[bad x] :=
    prEvent_mono mx _ _ fun _ hx => hx.2
  have h₂ : Pr{let y ← my}[f y ∈ A.1 ∧ bad y] ≤ Pr{let x ← mx}[bad x] :=
    (prEvent_mono my _ _ fun _ hy => hy.2).trans hbad
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · calc _ ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[f y ∈ A.1 ∧ ¬bad y] := add_le_add h₁ le_rfl
      _ ≤ _ := by rw [add_comm]; exact add_le_add le_add_self le_rfl
  · calc _ ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[f y ∈ A.1 ∧ ¬bad y] := add_le_add h₂ le_rfl
      _ ≤ _ := by rw [add_comm]; exact add_le_add le_add_self le_rfl

/-- **Swap coupling.** The adversary's output distributions in the two worlds are within the
probability, in world 0, that some adversary query in either stage touches the swap set. -/
theorem swap_coupling (C : Compression) {γ β V Salt : Type} [Fintype Salt]
    [MeasurableSpace β] (A₁ : OracleComp World γ) (salt : ProbComp Salt)
    (A₂ : γ → V → OracleComp World β) (view : Bool → γ → Salt → Perm → V)
    (S : γ → Salt → Perm → Finset PWord) (τ : γ → Salt → Perm → Perm)
    (hfix : ∀ c s σ x, x ∉ S c s σ → τ c s σ x = x)
    (hS : ∀ c s σ, S c s (σ * τ c s σ) = S c s σ)
    (hinv : ∀ c s σ, σ * τ c s σ * τ c s (σ * τ c s σ) = σ)
    (hview : ∀ c s σ, view true c s (σ * τ c s σ) = view false c s σ) :
    measureETVDist (Prod.fst <$> experiment C A₁ salt A₂ view S false)
        (Prod.fst <$> experiment C A₁ salt A₂ view S true) ≤
      Pr{let z ← experiment C A₁ salt A₂ view S false}[Bad z] := by
  have agree := experiment_agree C A₁ salt A₂ view S τ hfix hS hinv hview
  refine etv_le_of_agree _ _ Prod.fst Bad agree ?_
  have total : ∀ b, Pr{let z ← experiment C A₁ salt A₂ view S b}[Bad z] +
      Pr{let z ← experiment C A₁ salt A₂ view S b}[¬Bad z] = 1 := by
    intro b
    rw [prEvent_add_prEvent_not_eq_prEvent_true]
    exact (prFail_eq_zero_iff _).mp (OracleComp.prFail_eq_zero _)
  have same : Pr{let z ← experiment C A₁ salt A₂ view S false}[¬Bad z] =
      Pr{let z ← experiment C A₁ salt A₂ view S true}[¬Bad z] := by
    simpa only [true_and] using agree fun _ => True
  have h0 := total false
  have h1 := total true
  rw [same] at h0
  exact ENNReal.le_of_add_le_add_right (prEvent_ne_top _) (h1.trans h0.symm).le

/-! ## The salted two-call leaf: the swap and its four properties

A leaf layout abstracts the PL-B leaf. A tag function marks the second-call inputs `W` with their
position and the first-call inputs `X` with nothing, so the two families are disjoint and `W`
inputs at different positions differ. `swapSet c` holds the positions whose leaf inputs may differ
between the two messages (hidden, unequal); elsewhere both worlds use the same inputs. The honest
view (root and proof) is any function of the full leaf outputs `σ (W (σ X))`. -/

structure LeafLayout (Ch Salt Pos : Type) where
  tag : PWord → Option Pos
  X : Ch → Bool → Pos → PWord
  W : Ch → Salt → Bool → Pos → PWord → PWord
  swapSet : Ch → Finset Pos
  tag_X : ∀ c b j, tag (X c b j) = none
  tag_W : ∀ c s b j y, tag (W c s b j y) = some j
  agree : ∀ c s j, j ∉ swapSet c →
    X c false j = X c true j ∧ ∀ y, W c s false j y = W c s true j y

section Leaf
variable {Ch Salt Pos : Type} [DecidableEq Pos] (L : LeafLayout Ch Salt Pos)

/-- The second-call input of world `b` at position `j`. -/
def wpt (c : Ch) (s : Salt) (σ : Perm) (b : Bool) (j : Pos) : PWord :=
  L.W c s b j (σ (L.X c b j))

theorem tag_wpt (c : Ch) (s : Salt) (σ : Perm) (b : Bool) (j : Pos) :
    L.tag (wpt L c s σ b j) = some j := L.tag_W c s b j _

/-- Swap the two worlds' second-call inputs at every position of `swapSet c`. -/
def swapFun (c : Ch) (s : Salt) (σ : Perm) (x : PWord) : PWord :=
  match L.tag x with
  | some j =>
    if j ∈ L.swapSet c then
      (if x = wpt L c s σ false j then wpt L c s σ true j
       else if x = wpt L c s σ true j then wpt L c s σ false j else x)
    else x
  | none => x

theorem swapFun_of_tag {c : Ch} {s : Salt} {σ : Perm} {x : PWord} {j : Pos}
    (h : L.tag x = some j) : swapFun L c s σ x =
      if j ∈ L.swapSet c then
        (if x = wpt L c s σ false j then wpt L c s σ true j
         else if x = wpt L c s σ true j then wpt L c s σ false j else x)
      else x := by
  unfold swapFun
  rw [h]

theorem swapFun_of_none {c : Ch} {s : Salt} {σ : Perm} {x : PWord} (h : L.tag x = none) :
    swapFun L c s σ x = x := by
  unfold swapFun
  rw [h]

theorem swapFun_involutive (c : Ch) (s : Salt) (σ : Perm) :
    Function.Involutive (swapFun L c s σ) := by
  intro x
  cases hx : L.tag x with
  | none => rw [swapFun_of_none L hx, swapFun_of_none L hx]
  | some j =>
    rw [swapFun_of_tag L hx]
    by_cases hj : j ∈ L.swapSet c
    · rw [if_pos hj]
      by_cases ha : x = wpt L c s σ false j
      · rw [if_pos ha, swapFun_of_tag L (tag_wpt L c s σ true j), if_pos hj]
        by_cases hba : wpt L c s σ true j = wpt L c s σ false j
        · rw [if_pos hba, hba]; exact ha.symm
        · rw [if_neg hba, if_pos rfl]; exact ha.symm
      · rw [if_neg ha]
        by_cases hb : x = wpt L c s σ true j
        · rw [if_pos hb, swapFun_of_tag L (tag_wpt L c s σ false j), if_pos hj, if_pos rfl]
          exact hb.symm
        · rw [if_neg hb, swapFun_of_tag L hx, if_pos hj, if_neg ha, if_neg hb]
    · rw [if_neg hj, swapFun_of_tag L hx, if_neg hj]

/-- The swap as a permutation (an involution). -/
noncomputable def swapPerm (c : Ch) (s : Salt) (σ : Perm) : Perm :=
  (swapFun_involutive L c s σ).toPerm _

theorem swapPerm_apply (c : Ch) (s : Salt) (σ : Perm) (x : PWord) :
    swapPerm L c s σ x = swapFun L c s σ x := rfl

/-- The swap points: both worlds' second-call inputs at the swapped positions. -/
noncomputable def swapPts (c : Ch) (s : Salt) (σ : Perm) : Finset PWord :=
  (L.swapSet c).image (wpt L c s σ false) ∪ (L.swapSet c).image (wpt L c s σ true)

theorem swapPerm_fix (c : Ch) (s : Salt) (σ : Perm) (x : PWord) (hx : x ∉ swapPts L c s σ) :
    swapPerm L c s σ x = x := by
  rw [swapPerm_apply]
  cases ht : L.tag x with
  | none => exact swapFun_of_none L ht
  | some j =>
    rw [swapFun_of_tag L ht]
    by_cases hj : j ∈ L.swapSet c
    · rw [if_pos hj]
      have ha : x ≠ wpt L c s σ false j := fun h =>
        hx (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, h.symm⟩))
      have hb : x ≠ wpt L c s σ true j := fun h =>
        hx (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, h.symm⟩))
      rw [if_neg ha, if_neg hb]
    · rw [if_neg hj]

theorem swapPerm_X (c : Ch) (s : Salt) (σ : Perm) (b : Bool) (j : Pos) :
    swapPerm L c s σ (L.X c b j) = L.X c b j := by
  rw [swapPerm_apply]
  exact swapFun_of_none L (L.tag_X c b j)

/-- Precomposing with anything that fixes the first-call inputs keeps every `W`. -/
theorem wpt_mul (ρ : Perm) (hρ : ∀ c b j, ρ (L.X c b j) = L.X c b j)
    (c : Ch) (s : Salt) (σ : Perm) (b : Bool) (j : Pos) :
    wpt L c s (σ * ρ) b j = wpt L c s σ b j := by
  unfold wpt
  rw [Equiv.Perm.mul_apply, hρ]

theorem wpt_swap (c : Ch) (s : Salt) (σ : Perm) (b : Bool) (j : Pos) :
    wpt L c s (σ * swapPerm L c s σ) b j = wpt L c s σ b j := by
  unfold wpt
  rw [Equiv.Perm.mul_apply, swapPerm_X]

theorem wpt_swap_fun (c : Ch) (s : Salt) (σ : Perm) :
    wpt L c s (σ * swapPerm L c s σ) = wpt L c s σ :=
  funext fun b => funext fun j => wpt_swap L c s σ b j

theorem swapPts_swap (c : Ch) (s : Salt) (σ : Perm) :
    swapPts L c s (σ * swapPerm L c s σ) = swapPts L c s σ := by
  unfold swapPts
  rw [wpt_swap_fun]

theorem swapPerm_swap (c : Ch) (s : Salt) (σ : Perm) :
    swapPerm L c s (σ * swapPerm L c s σ) = swapPerm L c s σ := by
  ext x
  rw [swapPerm_apply, swapPerm_apply]
  unfold swapFun
  simp only [wpt_swap]

theorem swapPerm_inv (c : Ch) (s : Salt) (σ : Perm) :
    σ * swapPerm L c s σ * swapPerm L c s (σ * swapPerm L c s σ) = σ := by
  rw [swapPerm_swap, mul_assoc]
  have square : swapPerm L c s σ * swapPerm L c s σ = 1 := by
    refine Equiv.ext fun x => ?_
    rw [Equiv.Perm.mul_apply, swapPerm_apply, swapPerm_apply, Equiv.Perm.one_apply]
    exact swapFun_involutive L c s σ x
  rw [square, mul_one]

/-- The swap sends world 1's second-call input to world 0's, at every position. -/
theorem swapPerm_true (c : Ch) (s : Salt) (σ : Perm) (j : Pos) :
    swapPerm L c s σ (wpt L c s σ true j) = wpt L c s σ false j := by
  rw [swapPerm_apply, swapFun_of_tag L (tag_wpt L c s σ true j)]
  by_cases hj : j ∈ L.swapSet c
  · rw [if_pos hj]
    by_cases hba : wpt L c s σ true j = wpt L c s σ false j
    · rw [if_pos hba]; exact hba
    · rw [if_neg hba, if_pos rfl]
  · rw [if_neg hj]
    obtain ⟨sameX, sameW⟩ := L.agree c s j hj
    unfold wpt
    rw [sameX, sameW]

/-- Under the swap, world 1's leaf outputs are world 0's. -/
theorem leaf_outputs_swap (c : Ch) (s : Salt) (σ : Perm) (j : Pos) :
    (σ * swapPerm L c s σ) (wpt L c s (σ * swapPerm L c s σ) true j) =
      σ (wpt L c s σ false j) := by
  rw [wpt_swap, Equiv.Perm.mul_apply, swapPerm_true]

/-- **Swap coupling for the salted two-call leaf.** For every honest view that is a function of
the full leaf outputs (tree, root and proof), the adversary's output distributions for the two
messages are within the probability that some adversary query touches a swap point. -/
theorem leaf_swap_coupling (C : Compression) {β V : Type} [Fintype Salt] [MeasurableSpace β]
    (A₁ : OracleComp World Ch) (salt : ProbComp Salt) (A₂ : Ch → V → OracleComp World β)
    (F : Ch → Salt → (Pos → PWord) → V) :
    measureETVDist
        (Prod.fst <$> experiment C A₁ salt A₂
          (fun b c s σ => F c s fun j => σ (wpt L c s σ b j)) (swapPts L) false)
        (Prod.fst <$> experiment C A₁ salt A₂
          (fun b c s σ => F c s fun j => σ (wpt L c s σ b j)) (swapPts L) true) ≤
      Pr{let z ← experiment C A₁ salt A₂
          (fun b c s σ => F c s fun j => σ (wpt L c s σ b j)) (swapPts L) false}[Bad z] :=
  swap_coupling C A₁ salt A₂ _ (swapPts L) (swapPerm L) (swapPerm_fix L) (swapPts_swap L)
    (swapPerm_inv L) fun c s σ => by
      show F c s (fun j => (σ * swapPerm L c s σ) (wpt L c s (σ * swapPerm L c s σ) true j)) =
        F c s (fun j => σ (wpt L c s σ false j))
      simp only [leaf_outputs_swap]

end Leaf


/-! ## Uniform compression and the contract's execution -/

/-- Agreement off `bad` for two lossless computations forces equal `bad` mass. -/
theorem bad_le_of_agree {α : Type} (mx my : ProbComp α) (bad : α → Prop)
    (hagree : ∀ p : α → Prop,
      Pr{let x ← mx}[p x ∧ ¬bad x] = Pr{let y ← my}[p y ∧ ¬bad y]) :
    Pr{let y ← my}[bad y] ≤ Pr{let x ← mx}[bad x] := by
  have total : ∀ m : ProbComp α, Pr{let z ← m}[bad z] + Pr{let z ← m}[¬bad z] = 1 := by
    intro m
    rw [prEvent_add_prEvent_not_eq_prEvent_true]
    exact (prFail_eq_zero_iff _).mp (OracleComp.prFail_eq_zero _)
  have same : Pr{let z ← mx}[¬bad z] = Pr{let z ← my}[¬bad z] := by
    simpa only [true_and] using hagree fun _ => True
  have h0 := total mx
  have h1 := total my
  rw [same] at h0
  exact ENNReal.le_of_add_le_add_right (prEvent_ne_top _) (h1.trans h0.symm).le

/-- **Swap coupling with the compression table sampled**, as in `Oracle.sample`. -/
theorem swap_coupling_sampled {γ β V Salt : Type} [Fintype Salt] [MeasurableSpace β]
    (A₁ : OracleComp World γ) (salt : ProbComp Salt) (A₂ : γ → V → OracleComp World β)
    (view : Compression → Bool → γ → Salt → Perm → V) (S : γ → Salt → Perm → Finset PWord)
    (τ : γ → Salt → Perm → Perm)
    (hfix : ∀ c s σ x, x ∉ S c s σ → τ c s σ x = x)
    (hS : ∀ c s σ, S c s (σ * τ c s σ) = S c s σ)
    (hinv : ∀ c s σ, σ * τ c s σ * τ c s (σ * τ c s σ) = σ)
    (hview : ∀ C c s σ, view C true c s (σ * τ c s σ) = view C false c s σ) :
    measureETVDist
        (Prod.fst <$> (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C A₁ salt A₂ (view C) S false))
        (Prod.fst <$> (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C A₁ salt A₂ (view C) S true)) ≤
      Pr{let z ← (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C A₁ salt A₂ (view C) S false)}[Bad z] := by
  have agree : ∀ p : Out β → Prop,
      Pr{let z ← (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C A₁ salt A₂ (view C) S false)}[p z ∧ ¬Bad z] =
        Pr{let z ← (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C A₁ salt A₂ (view C) S true)}[p z ∧ ¬Bad z] := fun p =>
    prEvent_bind_congr _ _ _ _ _ fun C =>
      experiment_agree C A₁ salt A₂ (view C) S τ hfix hS hinv (hview C) p
  exact etv_le_of_agree _ _ Prod.fst Bad agree (bad_le_of_agree _ _ Bad agree)

/-- The contract's execution `Oracle.run` against `⟨C, σ⟩` has the outputs of `runLog`. -/
theorem simulateQ_world_eq (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    simulateQ (Oracle.world ⟨C, σ⟩) comp = Prod.fst <$> runLog C σ comp := by
  induction comp using OracleComp.inductionOn with
  | pure value => rw [runLog_pure, simulateQ_pure, map_pure]
  | query_bind t next ih =>
    rw [runLog_query_bind, simulateQ_query_bind]
    rcases t with coins | publicQuery
    · simp only [stepLog, map_bind, ← ih]
      rfl
    · rcases publicQuery with x | permQuery
      · simp only [stepLog, ← ih]
        rfl
      · rcases permQuery with x | y
        · simp only [stepLog, Functor.map_map, ← ih]
          rfl
        · simp only [stepLog, Functor.map_map, ← ih]
          rfl

theorem run_fst_eq (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    Prod.fst <$> (⟨C, σ⟩ : Oracle).run comp = Prod.fst <$> runLog C σ comp := by
  rw [← simulateQ_world_eq]
  unfold Oracle.run QueryImpl.withAddCost
  exact QueryImpl.fst_map_run_withCost (ω := Multiplicative ℕ) _ _ comp


/-! ## The contract's hiding experiment -/

theorem run_fst_eq_simulateQ (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    Prod.fst <$> (⟨C, σ⟩ : Oracle).run comp = simulateQ (Oracle.world ⟨C, σ⟩) comp := by
  unfold Oracle.run QueryImpl.withAddCost
  exact QueryImpl.fst_map_run_withCost (ω := Multiplicative ℕ) _ _ comp

/-- Equal event masses give equal output measures. -/
theorem evalDist_eq_of_events {α : Type} [MeasurableSpace α] (mx my : ProbComp α)
    (h : ∀ p : α → Prop, Pr{let x ← mx}[p x] = Pr{let y ← my}[p y]) : 𝒟[mx] = 𝒟[my] := by
  ext A hA
  have hx := prEvent_eq_evalDist mx (· ∈ A) hA.mem
  have hy := prEvent_eq_evalDist my (· ∈ A) hA.mem
  rw [Set.ofPred_mem_eq] at hx hy
  rw [← hx, ← hy, h]

/-- Equal-distribution first draws followed by a common continuation. -/
theorem prEvent_bind_congr_left {α β : Type} (mx my : ProbComp α) (f : α → ProbComp β)
    (q : β → Prop) (h : ∀ p : α → Prop, Pr{let x ← mx}[p x] = Pr{let y ← my}[p y]) :
    Pr{let z ← (mx >>= f)}[q z] = Pr{let z ← (my >>= f)}[q z] := by
  letI : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    evalDist_eq_of_events mx my h]

theorem etv_congr {α : Type} [MeasurableSpace α] (mx my mx' my' : ProbComp α)
    (hx : ∀ p : α → Prop, Pr{let x ← mx}[p x] = Pr{let x ← mx'}[p x])
    (hy : ∀ p : α → Prop, Pr{let y ← my}[p y] = Pr{let y ← my'}[p y]) :
    measureETVDist mx my = measureETVDist mx' my' := by
  unfold measureETVDist
  rw [evalDist_eq_of_events mx mx' hx, evalDist_eq_of_events my my' hy]

/-- The honest middle of the contract's experiment: commit to the selected message, open. -/
def honest (scheme : Scheme) {St : Type} {k : Nat} (b : Bool)
    (c : Hiding.HidingChallenge St k) : OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← scheme.commit (if b then c.message₁ else c.message₀)
  let proof ← scheme.opening trapdoor c.positions
  return (root, proof)

theorem hidingExperiment_eq (scheme : Scheme) {St Out : Type} {k : Nat}
    (adversary : Hiding.HidingAdversary St Out k) (b : Bool) :
    Hiding.hidingExperiment scheme adversary b =
      adversary.choose >>= fun c => honest scheme b c >>= fun v =>
        adversary.observe c.aux v.1 v.2 := by
  unfold Hiding.hidingExperiment honest
  refine bind_congr fun c => ?_
  simp only [bind_assoc]
  refine bind_congr fun x => ?_
  rcases x with ⟨root, trapdoor⟩
  simp only [bind_assoc, pure_bind]

theorem runHiding_eq {Out : Type} (exp : OracleComp World Out) :
    Hiding.runHiding exp = ($ᵗ Compression : ProbComp Compression) >>= fun C =>
      ($ᵗ Perm : ProbComp Perm) >>= fun σ => simulateQ (Oracle.world ⟨C, σ⟩) exp := by
  unfold Hiding.runHiding Oracle.sample
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun C => bind_congr fun σ => ?_
  rw [← run_fst_eq_simulateQ, map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  rcases x with ⟨o, n⟩
  rfl

/-- **Contract form of step 1.** If the honest commitment and opening of the selected message
have the distribution of `salt >>= view` against every fixed oracle pair (the refinement
obligation), then the contract's hiding distance is at most the touch probability of world 0. -/
theorem hiding_le_bad (scheme : Scheme) {St Out Salt : Type} {k : Nat} [Fintype Salt]
    (adversary : Hiding.HidingAdversary St Out k) (salt : ProbComp Salt)
    (view : Compression → Bool → Hiding.HidingChallenge St k → Salt → Perm → Commitment × Proof)
    (S : Hiding.HidingChallenge St k → Salt → Perm → Finset PWord)
    (τ : Hiding.HidingChallenge St k → Salt → Perm → Perm)
    (hfix : ∀ c s σ x, x ∉ S c s σ → τ c s σ x = x)
    (hS : ∀ c s σ, S c s (σ * τ c s σ) = S c s σ)
    (hinv : ∀ c s σ, σ * τ c s σ * τ c s (σ * τ c s σ) = σ)
    (hview : ∀ C c s σ, view C true c s (σ * τ c s σ) = view C false c s σ)
    (hhonest : ∀ (C : Compression) (σ : Perm) (b : Bool) (c : Hiding.HidingChallenge St k)
      (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s => pure (view C b c s σ))}[q v]) :
    letI : MeasurableSpace Out := ⊤
    measureETVDist (Hiding.runHiding (Hiding.hidingExperiment scheme adversary false))
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary true)) ≤
      Pr{let z ← (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C adversary.choose salt (fun c v => adversary.observe c.aux v.1 v.2)
            (view C) S false)}[Bad z] := by
  letI : MeasurableSpace Out := ⊤
  have reduce : ∀ (b : Bool) (p : Out → Prop),
      Pr{let o ← Hiding.runHiding (Hiding.hidingExperiment scheme adversary b)}[p o] =
        Pr{let o ← (Prod.fst <$> (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C adversary.choose salt (fun c v => adversary.observe c.aux v.1 v.2)
            (view C) S b))}[p o] := by
    intro b p
    rw [runHiding_eq, prEvent_map]
    unfold experiment
    refine prEvent_bind_congr _ _ _ _ _ fun C => ?_
    refine prEvent_bind_congr _ _ _ _ _ fun σ => ?_
    rw [hidingExperiment_eq, simulateQ_bind, simulateQ_world_eq, bind_map_left]
    refine prEvent_bind_congr _ _ _ _ _ fun r => ?_
    rw [simulateQ_bind]
    simp only [simulateQ_world_eq]
    have hh : ∀ q : Commitment × Proof → Prop,
        Pr{let v ← (Prod.fst <$> runLog C σ (honest scheme b r.1))}[q v] =
          Pr{let v ← (salt >>= fun s => pure (view C b r.1 s σ))}[q v] := by
      intro q
      rw [← simulateQ_world_eq]
      exact hhonest C σ b r.1 q
    rw [prEvent_bind_congr_left _ _ _ _ hh]
    unfold tail
    rw [bind_assoc]
    refine prEvent_bind_congr _ _ _ _ _ fun s => ?_
    rw [pure_bind, prEvent_map, bind_pure_comp, prEvent_map]
  rw [etv_congr _ _ _ _ (reduce false) (reduce true)]
  exact swap_coupling_sampled adversary.choose salt _ view S τ hfix hS hinv hview

/-- **Contract form for the salted two-call leaf.** Remaining obligations: the refinement
`hhonest` (the machine's commit and opening produce `F` of the leaf outputs) and a bound on the
touch probability (step 2 of the swap argument). -/
theorem leaf_hiding_le_bad (scheme : Scheme) {St Out Salt Pos : Type} {k : Nat} [Fintype Salt]
    [DecidableEq Pos] (L : LeafLayout (Hiding.HidingChallenge St k) Salt Pos)
    (adversary : Hiding.HidingAdversary St Out k) (salt : ProbComp Salt)
    (F : Compression → Hiding.HidingChallenge St k → Salt → (Pos → PWord) → Commitment × Proof)
    (hhonest : ∀ (C : Compression) (σ : Perm) (b : Bool) (c : Hiding.HidingChallenge St k)
      (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s => pure (F C c s fun j => σ (wpt L c s σ b j)))}[q v]) :
    letI : MeasurableSpace Out := ⊤
    measureETVDist (Hiding.runHiding (Hiding.hidingExperiment scheme adversary false))
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary true)) ≤
      Pr{let z ← (($ᵗ Compression : ProbComp Compression) >>= fun C =>
          experiment C adversary.choose salt (fun c v => adversary.observe c.aux v.1 v.2)
            (fun b c s σ => F C c s fun j => σ (wpt L c s σ b j)) (swapPts L) false)}[Bad z] :=
  hiding_le_bad scheme adversary salt (fun C b c s σ => F C c s fun j => σ (wpt L c s σ b j))
    (swapPts L) (swapPerm L) (swapPerm_fix L) (swapPts_swap L) (swapPerm_inv L)
    (fun C c s σ => by
      show F C c s (fun j => (σ * swapPerm L c s σ) (wpt L c s (σ * swapPerm L c s σ) true j)) =
        F C c s (fun j => σ (wpt L c s σ false j))
      simp only [leaf_outputs_swap])
    hhonest


/-! ## Engine for step 2: runs cut at the first touch

`runCut` stops at the first query that touches `S` and reports the touched point and whether the
query was an inverse one. Under `σ ↦ σ * τ` with `τ` fixing everything outside `S`, the cut run
changes only in the point reported by an inverse first touch, which moves by `τ⁻¹`: forward
touches and touch-free runs are unchanged. This is the identical-until-first-touch property used
by the reference-salt coupling `Φ*` (step 2(b) of the swap argument). -/

/-- One query of a run cut at the first touch of `S`. -/
def stepCut (C : Compression) (S : Finset PWord) (σ : Perm) {γ : Type} :
    (t : World.Domain) → (World.Range t → ProbComp (γ ⊕ (PWord × Bool))) →
      ProbComp (γ ⊕ (PWord × Bool))
  | .inl coins, k => (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>= k
  | .inr (.inl x), k => k (C x)
  | .inr (.inr (.inl x)), k => if x ∈ S then pure (.inr (x, false)) else k (σ x)
  | .inr (.inr (.inr y)), k =>
      if σ.symm y ∈ S then pure (.inr (σ.symm y, true)) else k (σ.symm y)

/-- The adversary's output if it never touches `S`, else its first touch. -/
def runCut (C : Compression) (S : Finset PWord) (σ : Perm) {β : Type}
    (comp : OracleComp World β) : ProbComp (β ⊕ (PWord × Bool)) :=
  OracleComp.recOn comp (fun value => pure (.inl value))
    (fun t _ next => stepCut C S σ t next)

/-- Move an inverse first touch by `τ⁻¹`; leave everything else. -/
def adjust (τ : Perm) {β : Type} : β ⊕ (PWord × Bool) → β ⊕ (PWord × Bool)
  | .inl v => .inl v
  | .inr (x, false) => .inr (x, false)
  | .inr (x, true) => .inr (τ.symm x, true)

/-- **Identical until the first touch.** -/
theorem runCut_swap (C : Compression) (S : Finset PWord) (τ : Perm)
    (hfix : ∀ x, x ∉ S → τ x = x) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    runCut C S (σ * τ) comp = adjust τ <$> runCut C S σ comp := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    show (pure (.inl value) : ProbComp (β ⊕ (PWord × Bool))) =
      adjust τ <$> (pure (.inl value) : ProbComp (β ⊕ (PWord × Bool)))
    rw [map_pure]
    rfl
  | query_bind t next ih =>
    show stepCut C S (σ * τ) t (fun a => runCut C S (σ * τ) (next a)) =
      adjust τ <$> stepCut C S σ t (fun a => runCut C S σ (next a))
    rcases t with coins | publicQuery
    · show (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
          (fun a => runCut C S (σ * τ) (next a)) =
        adjust τ <$> ((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
          fun a => runCut C S σ (next a))
      rw [map_bind]
      exact bind_congr fun a => ih a
    · rcases publicQuery with x | permQuery
      · exact ih (C x)
      · rcases permQuery with x | y
        · simp only [stepCut]
          by_cases hx : x ∈ S
          · rw [if_pos hx, if_pos hx, map_pure]
            rfl
          · have same : (σ * τ) x = σ x := by rw [Equiv.Perm.mul_apply, hfix x hx]
            rw [if_neg hx, if_neg hx, same]
            exact ih (σ x)
        · simp only [stepCut]
          by_cases hy : σ.symm y ∈ S
          · have moved : (σ * τ).symm y ∈ S := by
              rw [mul_symm_apply]; exact symm_mem hfix hy
            rw [if_pos moved, if_pos hy, map_pure, mul_symm_apply]
            rfl
          · have same : (σ * τ).symm y = σ.symm y := by
              rw [mul_symm_apply]; exact symm_fix hfix hy
            have notMoved : (σ * τ).symm y ∉ S := by rw [same]; exact hy
            rw [if_neg notMoved, if_neg hy, same]
            exact ih (σ.symm y)



/-! # Step 2: the touch probability

the swap argument, step 2. Reference salts `s*` are drawn next to the real salts `s`. The run of stage
two is cut at its first touch of `U = S(s) ∪ S(s*)`. A first touch in `S(s)` that is not an inverse
query answered by a real world-0 second-call input (`RH`, the range hit) is carried to a first
touch in `S(s*)` by exchanging `s` and `s*` on the swapped positions and precomposing `σ` with the
swaps `W⁰_j(s_j) ↔ W⁰_j(s*_j)` (`ref_swap_le`). -/

/-! ## Stage one with an inequality -/

theorem coin_step_le {ι α₁ α₂ : Type} [Fintype ι] (mx : ProbComp ι)
    (f : ι → Perm → ProbComp α₁) (g : ι → Perm → ProbComp α₂) (s : Finset Perm)
    (q₁ : α₁ → Prop) (q₂ : α₂ → Prop)
    (h : ∀ a, ∑ σ ∈ s, Pr{let z ← f a σ}[q₁ z] ≤ ∑ σ ∈ s, Pr{let z ← g a σ}[q₂ z]) :
    ∑ σ ∈ s, Pr{let z ← (mx >>= fun a => f a σ)}[q₁ z] ≤
      ∑ σ ∈ s, Pr{let z ← (mx >>= fun a => g a σ)}[q₂ z] := by
  simp only [prEvent_bind_eq_sum_fintype]
  rw [Finset.sum_comm, Finset.sum_comm (s := s)]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_le_mul_right (h a) _

theorem forward_step_le (L : PLog) (x : PWord) (F G : Perm → PWord → ℝ≥0∞)
    (h : ∀ a, ∑ σ ∈ ext (L ++ [(x, a)]), F σ a ≤ ∑ σ ∈ ext (L ++ [(x, a)]), G σ a) :
    ∑ σ ∈ ext L, F σ (σ x) ≤ ∑ σ ∈ ext L, G σ (σ x) := by
  rw [sum_ext_forward L x F, sum_ext_forward L x G]
  exact Finset.sum_le_sum fun a _ => h a

theorem inverse_step_le (L : PLog) (y : PWord) (F G : Perm → PWord → ℝ≥0∞)
    (h : ∀ a, ∑ σ ∈ ext (L ++ [(a, y)]), F σ a ≤ ∑ σ ∈ ext (L ++ [(a, y)]), G σ a) :
    ∑ σ ∈ ext L, F σ (σ.symm y) ≤ ∑ σ ∈ ext L, G σ (σ.symm y) := by
  rw [sum_ext_inverse L y F, sum_ext_inverse L y G]
  exact Finset.sum_le_sum fun a _ => h a

/-- `stage_one_sum` with an inequality and two different continuations and events. -/
theorem stage_one_le (C : Compression) {γ α₁ α₂ : Type} (comp : OracleComp World γ)
    (K₁ : γ → List PWord → Perm → ProbComp α₁) (K₂ : γ → List PWord → Perm → ProbComp α₂)
    (q₁ : α₁ → Prop) (q₂ : α₂ → Prop)
    (hK : ∀ (L : PLog) (c : γ),
      ∑ σ ∈ ext L, Pr{let z ← K₁ c (L.map Prod.fst) σ}[q₁ z] ≤
        ∑ σ ∈ ext L, Pr{let z ← K₂ c (L.map Prod.fst) σ}[q₂ z]) :
    ∀ L : PLog,
      ∑ σ ∈ ext L, Pr{let z ← (runLog C σ comp >>= fun r =>
          K₁ r.1 (L.map Prod.fst ++ r.2) σ)}[q₁ z] ≤
        ∑ σ ∈ ext L, Pr{let z ← (runLog C σ comp >>= fun r =>
          K₂ r.1 (L.map Prod.fst ++ r.2) σ)}[q₂ z] := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro L
    simp only [runLog_pure, pure_bind, List.append_nil]
    exact hK L value
  | query_bind t next ih =>
    intro L
    rcases t with coins | publicQuery
    · have unfold : ∀ {α : Type} (K : γ → List PWord → Perm → ProbComp α) (q : α → Prop)
          (σ : Perm),
          Pr{let z ← (stepLog C σ (.inl coins) (fun a => runLog C σ (next a)) >>= fun r =>
            K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
          Pr{let z ← ((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
            fun a => (runLog C σ (next a) >>= fun r => K r.1 (L.map Prod.fst ++ r.2) σ))}[q z] :=
        fun K q σ => by
          show Pr{let z ← (((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
            fun a => runLog C σ (next a)) >>= fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
          rw [bind_assoc]
      refine (Finset.sum_congr rfl fun σ _ => unfold K₁ q₁ σ).trans_le ?_
      refine le_of_le_of_eq ?_ (Finset.sum_congr rfl fun σ _ => unfold K₂ q₂ σ).symm
      exact coin_step_le _ _ _ _ q₁ q₂ fun a => ih a L
    · rcases publicQuery with x | permQuery
      · exact ih (C x) L
      · rcases permQuery with x | y
        · have unfold : ∀ {α : Type} (K : γ → List PWord → Perm → ProbComp α) (q : α → Prop)
              (σ : Perm),
              Pr{let z ← (stepLog C σ (.inr (.inr (.inl x))) (fun a => runLog C σ (next a)) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
              Pr{let z ← (runLog C σ (next (σ x)) >>= fun r =>
                K r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q z] :=
            fun K q σ => by
              show Pr{let z ← (((fun z => (z.1, x :: z.2)) <$> runLog C σ (next (σ x))) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
              rw [bind_map_left]
          refine (Finset.sum_congr rfl fun σ _ => unfold K₁ q₁ σ).trans_le ?_
          refine le_of_le_of_eq ?_ (Finset.sum_congr rfl fun σ _ => unfold K₂ q₂ σ).symm
          refine forward_step_le L x
            (fun σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
              K₁ r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q₁ z])
            (fun σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
              K₂ r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q₂ z]) fun a => ?_
          have h := ih a (L ++ [(x, a)])
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] at h
          exact h
        · have unfold : ∀ {α : Type} (K : γ → List PWord → Perm → ProbComp α) (q : α → Prop)
              (σ : Perm),
              Pr{let z ← (stepLog C σ (.inr (.inr (.inr y))) (fun a => runLog C σ (next a)) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
              Pr{let z ← (runLog C σ (next (σ.symm y)) >>= fun r =>
                K r.1 (L.map Prod.fst ++ σ.symm y :: r.2) σ)}[q z] :=
            fun K q σ => by
              show Pr{let z ← (((fun z => (z.1, σ.symm y :: z.2)) <$>
                runLog C σ (next (σ.symm y))) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
              rw [bind_map_left]
          refine (Finset.sum_congr rfl fun σ _ => unfold K₁ q₁ σ).trans_le ?_
          refine le_of_le_of_eq ?_ (Finset.sum_congr rfl fun σ _ => unfold K₂ q₂ σ).symm
          refine inverse_step_le L y
            (fun σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
              K₁ r.1 (L.map Prod.fst ++ a :: r.2) σ)}[q₁ z])
            (fun σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
              K₂ r.1 (L.map Prod.fst ++ a :: r.2) σ)}[q₂ z]) fun a => ?_
          have h := ih a (L ++ [(a, y)])
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append] at h
          exact h

/-! ## Per-position salts

A salt layout is a leaf layout whose salt is a function from positions to salt values `U`, the
second-call input at position `j` carrying the salt value `u` readably (`saltOf`). -/

structure SaltLayout (Ch Pos U : Type) where
  tag : PWord → Option Pos
  X : Ch → Bool → Pos → PWord
  W : Ch → Bool → Pos → U → PWord → PWord
  saltOf : PWord → U
  swapSet : Ch → Finset Pos
  tag_X : ∀ c b j, tag (X c b j) = none
  tag_W : ∀ c b j u y, tag (W c b j u y) = some j
  saltOf_W : ∀ c b j u y, saltOf (W c b j u y) = u
  agree : ∀ c j, j ∉ swapSet c →
    X c false j = X c true j ∧ ∀ u y, W c false j u y = W c true j u y

namespace SaltLayout
variable {Ch Pos U : Type} [DecidableEq Pos] (SL : SaltLayout Ch Pos U)

/-- The leaf layout with salts `s : Pos → U`. -/
def toLeaf : LeafLayout Ch (Pos → U) Pos where
  tag := SL.tag
  X := SL.X
  W c s b j y := SL.W c b j (s j) y
  swapSet := SL.swapSet
  tag_X := SL.tag_X
  tag_W c s b j y := SL.tag_W c b j (s j) y
  agree c s j hj := ⟨(SL.agree c j hj).1, fun y => (SL.agree c j hj).2 (s j) y⟩

/-- Salt of the pair layout: `false` reads the real salts, `true` the reference salts on the
swapped positions (and the real ones elsewhere). -/
def pick (c : Ch) (p : (Pos → U) × (Pos → U)) (b : Bool) (j : Pos) : U :=
  if b = true ∧ j ∈ SL.swapSet c then p.2 j else p.1 j

/-- World 0's second-call inputs under real (`false`) and reference (`true`) salts. Its swap is
the coupling `τ*` (step 2(b) of the swap argument). -/
def pairLeaf : LeafLayout Ch ((Pos → U) × (Pos → U)) Pos where
  tag := SL.tag
  X c _ j := SL.X c false j
  W c p b j y := SL.W c false j (SL.pick c p b j) y
  swapSet := SL.swapSet
  tag_X c _ j := SL.tag_X c false j
  tag_W c p b j y := SL.tag_W c false j _ y
  agree c p j hj := ⟨rfl, fun y => by simp [pick, hj]⟩

theorem toLeaf_swapSet : SL.toLeaf.swapSet = SL.swapSet := rfl
theorem pairLeaf_swapSet : SL.pairLeaf.swapSet = SL.swapSet := rfl

/-- Take `a` on the swapped positions, `b` elsewhere. -/
def mix (c : Ch) (a b : Pos → U) : Pos → U := fun j => if j ∈ SL.swapSet c then a j else b j

/-- Exchange real and reference salts on the swapped positions. -/
def exch (c : Ch) (p : (Pos → U) × (Pos → U)) : (Pos → U) × (Pos → U) :=
  (SL.mix c p.2 p.1, SL.mix c p.1 p.2)

theorem mix_in (c : Ch) (a b : Pos → U) (j : Pos) (hj : j ∈ SL.swapSet c) :
    SL.mix c a b j = a j := if_pos hj

theorem mix_out (c : Ch) (a b : Pos → U) (j : Pos) (hj : j ∉ SL.swapSet c) :
    SL.mix c a b j = b j := if_neg hj

theorem exch_exch (c : Ch) (p : (Pos → U) × (Pos → U)) : SL.exch c (SL.exch c p) = p := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
  · by_cases hj : j ∈ SL.swapSet c <;> simp [exch, mix, hj]

theorem exch_fst (c : Ch) (p : (Pos → U) × (Pos → U)) (j : Pos) :
    (SL.exch c p).1 j = SL.pick c p true j := by
  by_cases hj : j ∈ SL.swapSet c <;> simp [exch, mix, pick, hj]

/-- The swap set of the real salts `s`. -/
noncomputable def sset (c : Ch) (s : Pos → U) (σ : Perm) : Finset PWord := swapPts SL.toLeaf c s σ

/-- Real and reference swap sets together. -/
noncomputable def uset (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) : Finset PWord :=
  SL.sset c p.1 σ ∪ SL.sset c p.2 σ

/-- World 0's second-call inputs on the swapped positions. -/
noncomputable def w0set (c : Ch) (s : Pos → U) (σ : Perm) : Finset PWord :=
  (SL.swapSet c).image (wpt SL.toLeaf c s σ false)

/-- The reference coupling `τ*`: swap `W⁰_j(s_j) ↔ W⁰_j(s*_j)` on the swapped positions. -/
noncomputable def refSwap (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) : Perm :=
  swapPerm SL.pairLeaf c p σ

theorem wpt_toLeaf (c : Ch) (s : Pos → U) (σ : Perm) (b : Bool) (j : Pos) :
    wpt SL.toLeaf c s σ b j = SL.W c b j (s j) (σ (SL.X c b j)) := rfl

theorem wpt_pairLeaf (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (b : Bool) (j : Pos) :
    wpt SL.pairLeaf c p σ b j = SL.W c false j (SL.pick c p b j) (σ (SL.X c false j)) := rfl

theorem wpt_pair_false (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (j : Pos) :
    wpt SL.pairLeaf c p σ false j = wpt SL.toLeaf c p.1 σ false j := by
  rw [wpt_pairLeaf, wpt_toLeaf]
  simp [pick]

theorem wpt_pair_true (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (j : Pos)
    (hj : j ∈ SL.swapSet c) :
    wpt SL.pairLeaf c p σ true j = wpt SL.toLeaf c p.2 σ false j := by
  rw [wpt_pairLeaf, wpt_toLeaf]
  simp [pick, hj]

theorem refSwap_X (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (c' : Ch) (b : Bool)
    (j : Pos) : SL.refSwap c p σ (SL.X c' b j) = SL.X c' b j := by
  unfold refSwap
  rw [swapPerm_apply]
  exact swapFun_of_none SL.pairLeaf (x := SL.X c' b j) (SL.tag_X c' b j)

theorem pts_sub (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    swapPts SL.pairLeaf c p σ ⊆ SL.uset c p σ := by
  intro x hx
  unfold swapPts at hx
  unfold uset sset swapPts
  rw [pairLeaf_swapSet] at hx
  rw [toLeaf_swapSet]
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    rw [wpt_pair_false]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    rw [wpt_pair_true SL c p σ j hj]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))

theorem refSwap_fix (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (x : PWord)
    (hx : x ∉ SL.uset c p σ) : SL.refSwap c p σ x = x :=
  swapPerm_fix SL.pairLeaf c p σ x fun h => hx (SL.pts_sub c p σ h)

theorem sset_congr (c : Ch) (σ : Perm) {s s' : Pos → U} (h : ∀ j ∈ SL.swapSet c, s j = s' j) :
    SL.sset c s σ = SL.sset c s' σ := by
  unfold sset swapPts
  have e : ∀ b, Set.EqOn (wpt SL.toLeaf c s σ b) (wpt SL.toLeaf c s' σ b)
      (SL.toLeaf.swapSet c : Set Pos) := by
    intro b j hj
    rw [wpt_toLeaf, wpt_toLeaf, h j hj]
  rw [Finset.image_congr (e false), Finset.image_congr (e true)]

theorem sset_mul (c : Ch) (s : Pos → U) (σ ρ : Perm)
    (hρ : ∀ c' b j, ρ (SL.X c' b j) = SL.X c' b j) : SL.sset c s (σ * ρ) = SL.sset c s σ := by
  unfold sset swapPts
  have e : ∀ b, wpt SL.toLeaf c s (σ * ρ) b = wpt SL.toLeaf c s σ b :=
    fun b => funext fun j => wpt_mul SL.toLeaf ρ hρ c s σ b j
  rw [e false, e true]

theorem uset_exch (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    SL.uset c (SL.exch c p) (σ * SL.refSwap c p σ) = SL.uset c p σ := by
  unfold uset
  rw [SL.sset_mul c _ σ _ (SL.refSwap_X c p σ), SL.sset_mul c _ σ _ (SL.refSwap_X c p σ),
    SL.sset_congr c σ (s := (SL.exch c p).1) (s' := p.2) fun j hj => SL.mix_in c p.2 p.1 j hj,
    SL.sset_congr c σ (s := (SL.exch c p).2) (s' := p.1) fun j hj => SL.mix_in c p.1 p.2 j hj]
  exact Finset.union_comm _ _

theorem swap_ite_comm (x a b : PWord) :
    (if x = a then b else if x = b then a else x) =
      (if x = b then a else if x = a then b else x) := by
  by_cases ha : x = a
  · by_cases hb : x = b
    · rw [if_pos ha, if_pos hb]; exact hb.symm.trans ha
    · rw [if_pos ha, if_neg hb, if_pos ha]
  · rw [if_neg ha]
    by_cases hb : x = b
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, if_neg ha]

theorem refSwap_exch (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    SL.refSwap c (SL.exch c p) (σ * SL.refSwap c p σ) = SL.refSwap c p σ := by
  refine Equiv.ext fun x => ?_
  unfold refSwap
  rw [swapPerm_apply, swapPerm_apply]
  cases ht : SL.tag x with
  | none =>
    rw [swapFun_of_none SL.pairLeaf (x := x) ht, swapFun_of_none SL.pairLeaf (x := x) ht]
  | some j =>
    rw [swapFun_of_tag SL.pairLeaf (x := x) ht, swapFun_of_tag SL.pairLeaf (x := x) ht,
      pairLeaf_swapSet]
    by_cases hj : j ∈ SL.swapSet c
    · rw [if_pos hj, if_pos hj]
      have hmul : ∀ b, wpt SL.pairLeaf c (SL.exch c p) (σ * swapPerm SL.pairLeaf c p σ) b j =
          wpt SL.pairLeaf c (SL.exch c p) σ b j :=
        fun b => wpt_mul SL.pairLeaf _ (fun c' _ j' => SL.refSwap_X c p σ c' false j') c _ σ b j
      have h1 : wpt SL.toLeaf c (SL.exch c p).1 σ false j = wpt SL.toLeaf c p.2 σ false j := by
        rw [wpt_toLeaf, wpt_toLeaf, show (SL.exch c p).1 j = p.2 j from SL.mix_in c _ _ j hj]
      have h2 : wpt SL.toLeaf c (SL.exch c p).2 σ false j = wpt SL.toLeaf c p.1 σ false j := by
        rw [wpt_toLeaf, wpt_toLeaf, show (SL.exch c p).2 j = p.1 j from SL.mix_in c _ _ j hj]
      rw [hmul false, hmul true, wpt_pair_false, wpt_pair_true SL c _ σ j hj, wpt_pair_false,
        wpt_pair_true SL c _ σ j hj, h1, h2]
      exact swap_ite_comm x _ _
    · rw [if_neg hj, if_neg hj]

theorem refSwap_sq (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    SL.refSwap c p σ * SL.refSwap c p σ = 1 := by
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  unfold refSwap
  rw [swapPerm_apply, swapPerm_apply]
  exact swapFun_involutive SL.pairLeaf c p σ x

theorem refSwap_inv (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    σ * SL.refSwap c p σ * SL.refSwap c (SL.exch c p) (σ * SL.refSwap c p σ) = σ := by
  rw [refSwap_exch, mul_assoc, refSwap_sq, mul_one]

theorem refSwap_symm (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    (SL.refSwap c p σ).symm = SL.refSwap c p σ :=
  Function.Involutive.toPerm_symm (swapFun_involutive SL.pairLeaf c p σ)

/-- World 0's honest view with real salts `s`. -/
def viewF {V : Type} (F : Ch → (Pos → U) → (Pos → PWord) → V) (c : Ch) (s : Pos → U)
    (σ : Perm) : V :=
  F c s fun j => σ (wpt SL.toLeaf c s σ false j)

theorem viewF_exch {V : Type} (F : Ch → (Pos → U) → (Pos → PWord) → V)
    (hF : ∀ c s s' o, (∀ j, j ∉ SL.swapSet c → s j = s' j) → F c s o = F c s' o)
    (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    SL.viewF F c (SL.exch c p).1 (σ * SL.refSwap c p σ) = SL.viewF F c p.1 σ := by
  unfold viewF
  have outputs : ∀ j, (σ * SL.refSwap c p σ)
      (wpt SL.toLeaf c (SL.exch c p).1 (σ * SL.refSwap c p σ) false j) =
        σ (wpt SL.toLeaf c p.1 σ false j) := by
    intro j
    rw [wpt_mul SL.toLeaf _ (SL.refSwap_X c p σ), Equiv.Perm.mul_apply]
    have e : wpt SL.toLeaf c (SL.exch c p).1 σ false j = wpt SL.pairLeaf c p σ true j := by
      rw [wpt_toLeaf, wpt_pairLeaf, exch_fst]
    rw [e]
    show σ (swapPerm SL.pairLeaf c p σ (wpt SL.pairLeaf c p σ true j)) = _
    rw [swapPerm_true, wpt_pair_false]
  simp only [outputs]
  exact hF c _ _ _ fun j hj => SL.mix_out c _ _ j hj

theorem refSwap_back (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (x : PWord)
    (hx : x ∈ SL.sset c p.1 σ) (hnot : x ∉ SL.w0set c p.1 σ) :
    (SL.refSwap c p σ).symm x ∈ SL.sset c p.1 σ := by
  rw [refSwap_symm]
  have hx1 : x ∈ (SL.swapSet c).image (wpt SL.toLeaf c p.1 σ true) := by
    unfold sset swapPts at hx
    rcases Finset.mem_union.mp hx with h | h
    · exact absurd h hnot
    · exact h
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx1
  have hne : wpt SL.toLeaf c p.1 σ true j ≠ wpt SL.toLeaf c p.1 σ false j := fun h => hnot (by
    unfold w0set
    rw [h]
    exact Finset.mem_image_of_mem _ hj)
  unfold refSwap sset swapPts
  rw [swapPerm_apply, swapFun_of_tag SL.pairLeaf (tag_wpt SL.toLeaf c p.1 σ true j),
    pairLeaf_swapSet, if_pos hj, wpt_pair_false, wpt_pair_true SL c p σ j hj, if_neg hne,
    toLeaf_swapSet]
  split_ifs
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)

theorem mem_ext_refSwap (L : PLog) (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm)
    (hσ : σ ∈ ext L) (clean : Clean (SL.uset c p σ) (L.map Prod.fst)) :
    σ * SL.refSwap c p σ ∈ ext L := by
  refine mem_ext.mpr fun e he => ?_
  rw [Equiv.Perm.mul_apply, SL.refSwap_fix c p σ e.1 (clean e.1 (List.mem_map_of_mem he))]
  exact mem_ext.mp hσ e he

/-- First touch of `U` in the real swap set, other than the range hit. -/
def E0 {β : Type} (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (l : List PWord)
    (r : β ⊕ (PWord × Bool)) : Prop :=
  Clean (SL.uset c p σ) l ∧ ∃ x b, r = .inr (x, b) ∧ x ∈ SL.sset c p.1 σ ∧
    ¬ (b = true ∧ x ∈ SL.w0set c p.1 σ)

/-- First touch of `U` in the reference swap set. -/
def Estar {β : Type} (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (l : List PWord)
    (r : β ⊕ (PWord × Bool)) : Prop :=
  Clean (SL.uset c p σ) l ∧ ∃ x b, r = .inr (x, b) ∧ x ∈ SL.sset c p.2 σ

/-- The range hit: the first touch of `U` is an inverse query answered by a real world-0
second-call input. -/
def RH {β : Type} (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (l : List PWord)
    (r : β ⊕ (PWord × Bool)) : Prop :=
  Clean (SL.uset c p σ) l ∧ ∃ x, r = .inr (x, true) ∧ x ∈ SL.w0set c p.1 σ

theorem E0_imp {β : Type} (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) (l : List PWord)
    (r : β ⊕ (PWord × Bool)) (h : SL.E0 c p σ l r) :
    SL.Estar c (SL.exch c p) (σ * SL.refSwap c p σ) l (adjust (SL.refSwap c p σ) r) := by
  obtain ⟨clean, x, b, rfl, hx, hnot⟩ := h
  refine ⟨by rw [uset_exch]; exact clean, ?_⟩
  have same : SL.sset c (SL.exch c p).2 (σ * SL.refSwap c p σ) = SL.sset c p.1 σ := by
    rw [SL.sset_mul c _ σ _ (SL.refSwap_X c p σ)]
    exact SL.sset_congr c σ (s := (SL.exch c p).2) (s' := p.1) fun j hj => SL.mix_in c p.1 p.2 j hj
  cases b with
  | false => exact ⟨x, false, rfl, by rw [same]; exact hx⟩
  | true =>
    have hw : x ∉ SL.w0set c p.1 σ := fun hw => hnot ⟨rfl, hw⟩
    exact ⟨(SL.refSwap c p σ).symm x, true, rfl, by
      rw [same]; exact SL.refSwap_back c p σ x hx hw⟩

/-- **Reference-salt coupling** (step 2(b)). Over the permutations consistent with a stage-one
log and all salt pairs, first touches in the real swap set (other than range hits) have at most
the mass of first touches in the reference swap set. -/
theorem ref_swap_le (C : Compression) [Fintype Pos] [Fintype U] {β V : Type}
    (A₂ : Ch → V → OracleComp World β) (F : Ch → (Pos → U) → (Pos → PWord) → V)
    (hF : ∀ c s s' o, (∀ j, j ∉ SL.swapSet c → s j = s' j) → F c s o = F c s' o)
    (L : PLog) (c : Ch) :
    ∑ σ ∈ ext L, ∑ p : (Pos → U) × (Pos → U),
        Pr{let r ← runCut C (SL.uset c p σ) σ (A₂ c (SL.viewF F c p.1 σ))}[
          SL.E0 c p σ (L.map Prod.fst) r] ≤
      ∑ σ ∈ ext L, ∑ p : (Pos → U) × (Pos → U),
        Pr{let r ← runCut C (SL.uset c p σ) σ (A₂ c (SL.viewF F c p.1 σ))}[
          SL.Estar c p σ (L.map Prod.fst) r] := by
  classical
  set l := L.map Prod.fst with hl
  let G₀ : Perm × ((Pos → U) × (Pos → U)) → ℝ≥0∞ := fun q =>
    Pr{let r ← runCut C (SL.uset c q.2 q.1) q.1 (A₂ c (SL.viewF F c q.2.1 q.1))}[
      SL.E0 c q.2 q.1 l r]
  let G₁ : Perm × ((Pos → U) × (Pos → U)) → ℝ≥0∞ := fun q =>
    Pr{let r ← runCut C (SL.uset c q.2 q.1) q.1 (A₂ c (SL.viewF F c q.2.1 q.1))}[
      SL.Estar c q.2 q.1 l r]
  let Φ : Perm × ((Pos → U) × (Pos → U)) → Perm × ((Pos → U) × (Pos → U)) := fun q =>
    (q.1 * SL.refSwap c q.2 q.1, SL.exch c q.2)
  have lhs : ∑ q ∈ ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U))), G₀ q =
      ∑ σ ∈ ext L, ∑ p : (Pos → U) × (Pos → U), G₀ (σ, p) := Finset.sum_product _ _ _
  have rhs : ∑ q ∈ ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U))), G₁ q =
      ∑ σ ∈ ext L, ∑ p : (Pos → U) × (Pos → U), G₁ (σ, p) := Finset.sum_product _ _ _
  show ∑ σ ∈ ext L, ∑ p : (Pos → U) × (Pos → U), G₀ (σ, p) ≤
    ∑ σ ∈ ext L, ∑ p : (Pos → U) × (Pos → U), G₁ (σ, p)
  rw [← lhs, ← rhs]
  have zero : ∀ q ∈ ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U))), G₀ q ≠ 0 →
      Clean (SL.uset c q.2 q.1) l := by
    intro q _ nonzero
    by_contra dirty
    exact nonzero (prEvent_eq_zero_of_forall_not _ _ fun r hr => dirty hr.1)
  rw [← Finset.sum_filter_of_ne zero]
  have stays : ∀ q ∈ (ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U)))).filter
      (fun q => Clean (SL.uset c q.2 q.1) l),
      Φ q ∈ (ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U)))).filter
        (fun q => Clean (SL.uset c q.2 q.1) l) := by
    intro q hq
    obtain ⟨σ, p⟩ := q
    rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨SL.mem_ext_refSwap L c p σ hq.1.1 hq.2, Finset.mem_univ _⟩,
      by show Clean (SL.uset c (SL.exch c p) (σ * SL.refSwap c p σ)) l
         rw [uset_exch]; exact hq.2⟩
  have inv : ∀ q, Φ (Φ q) = q := by
    intro q
    obtain ⟨σ, p⟩ := q
    show (σ * SL.refSwap c p σ * SL.refSwap c (SL.exch c p) (σ * SL.refSwap c p σ),
      SL.exch c (SL.exch c p)) = (σ, p)
    rw [refSwap_inv, exch_exch]
  calc ∑ q ∈ (ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U)))).filter
          (fun q => Clean (SL.uset c q.2 q.1) l), G₀ q
      ≤ ∑ q ∈ (ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U)))).filter
          (fun q => Clean (SL.uset c q.2 q.1) l), G₁ (Φ q) := by
        refine Finset.sum_le_sum fun q _ => ?_
        obtain ⟨σ, p⟩ := q
        show Pr{let r ← runCut C (SL.uset c p σ) σ (A₂ c (SL.viewF F c p.1 σ))}[
            SL.E0 c p σ l r] ≤
          Pr{let r ← (runCut C (SL.uset c (SL.exch c p) (σ * SL.refSwap c p σ))
            (σ * SL.refSwap c p σ)
            (A₂ c (SL.viewF F c (SL.exch c p).1 (σ * SL.refSwap c p σ))))}[
            SL.Estar c (SL.exch c p) (σ * SL.refSwap c p σ) l r]
        rw [uset_exch, SL.viewF_exch F hF, runCut_swap C _ _ (SL.refSwap_fix c p σ), prEvent_map]
        exact prEvent_mono _ _ _ fun r hr => SL.E0_imp c p σ l r hr
    _ = ∑ q ∈ (ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U)))).filter
          (fun q => Clean (SL.uset c q.2 q.1) l), G₁ q :=
        Finset.sum_nbij' Φ Φ stays stays (fun q _ => inv q) (fun q _ => inv q) fun _ _ => rfl
    _ ≤ ∑ q ∈ ext L ×ˢ (Finset.univ : Finset ((Pos → U) × (Pos → U))), G₁ q :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end SaltLayout


/-! ## Logged runs against cut runs -/

theorem runCut_pure (C : Compression) (S : Finset PWord) (σ : Perm) {β : Type} (value : β) :
    runCut C S σ (pure value : OracleComp World β) = pure (.inl value) := rfl

theorem runCut_query_bind (C : Compression) (S : Finset PWord) (σ : Perm) {β : Type}
    (t : World.Domain) (next : World.Range t → OracleComp World β) :
    runCut C S σ ((liftM (World.query t) : OracleComp World _) >>= next) =
      stepCut C S σ t (fun a => runCut C S σ (next a)) := rfl

theorem prTrue {α : Type} (mx : ProbComp α) : Pr{let _ ← mx}[True] = 1 :=
  (prFail_eq_zero_iff _).mp (OracleComp.prFail_eq_zero _)

/-- A run touching `T ⊆ U` is cut at a first touch of `U`. -/
theorem log_touch_le_cut (C : Compression) (U T : Finset PWord) (hTU : T ⊆ U) (σ : Perm)
    {β : Type} (comp : OracleComp World β) :
    Pr{let z ← runLog C σ comp}[¬ Clean T z.2] ≤
      Pr{let r ← runCut C U σ comp}[∃ x b, r = .inr (x, b) ∧ x ∈ U] := by
  classical
  induction comp using OracleComp.inductionOn with
  | pure value =>
    rw [runLog_pure, prEvent_pure, if_neg]
    · exact zero_le
    · exact fun h => h fun x hx => absurd hx List.not_mem_nil
  | query_bind t next ih =>
    rw [runLog_query_bind, runCut_query_bind]
    rcases t with coins | publicQuery
    · exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun a => ih a
    · rcases publicQuery with x | permQuery
      · exact ih (C x)
      · rcases permQuery with x | y
        · simp only [stepLog, stepCut]
          rw [prEvent_map]
          by_cases hx : x ∈ U
          · rw [if_pos hx, prEvent_pure, if_pos ⟨x, false, rfl, hx⟩]
            exact prEvent_le_one _
          · rw [if_neg hx]
            have hxT : x ∉ T := fun h => hx (hTU h)
            refine le_trans (le_of_eq (prEvent_congr _ _ _ fun z => ?_)) (ih (σ x))
            simp only [clean_cons, hxT, not_false_eq_true, true_and]
        · simp only [stepLog, stepCut]
          rw [prEvent_map]
          by_cases hy : σ.symm y ∈ U
          · rw [if_pos hy, prEvent_pure, if_pos ⟨σ.symm y, true, rfl, hy⟩]
            exact prEvent_le_one _
          · rw [if_neg hy]
            have hyT : σ.symm y ∉ T := fun h => hy (hTU h)
            refine le_trans (le_of_eq (prEvent_congr _ _ _ fun z => ?_)) (ih (σ.symm y))
            simp only [clean_cons, hyT, not_false_eq_true, true_and]

/-- A first touch of `U` inside `T` is a touch of `T`. -/
theorem cut_in_le_log (C : Compression) (U T : Finset PWord) (σ : Perm) {β : Type}
    (comp : OracleComp World β) :
    Pr{let r ← runCut C U σ comp}[∃ x b, r = .inr (x, b) ∧ x ∈ T] ≤
      Pr{let z ← runLog C σ comp}[¬ Clean T z.2] := by
  classical
  induction comp using OracleComp.inductionOn with
  | pure value =>
    rw [runCut_pure, prEvent_pure, if_neg]
    · exact zero_le
    · rintro ⟨x, b, h, -⟩
      cases h
  | query_bind t next ih =>
    rw [runLog_query_bind, runCut_query_bind]
    rcases t with coins | publicQuery
    · exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun a => ih a
    · rcases publicQuery with x | permQuery
      · exact ih (C x)
      · rcases permQuery with x | y
        · simp only [stepLog, stepCut]
          rw [prEvent_map]
          by_cases hx : x ∈ U
          · rw [if_pos hx, prEvent_pure]
            split_ifs with hT
            · obtain ⟨x', b, h, hx'⟩ := hT
              simp only [Sum.inr.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              refine le_trans (le_of_eq (prTrue (runLog C σ (next (σ x)))).symm)
                (prEvent_mono _ _ _ fun z _ hc => ?_)
              exact (clean_cons.mp hc).1 hx'
            · exact zero_le
          · rw [if_neg hx]
            exact (ih (σ x)).trans (prEvent_mono _ _ _ fun z hz hc => hz (clean_cons.mp hc).2)
        · simp only [stepLog, stepCut]
          rw [prEvent_map]
          by_cases hy : σ.symm y ∈ U
          · rw [if_pos hy, prEvent_pure]
            split_ifs with hT
            · obtain ⟨x', b, h, hx'⟩ := hT
              simp only [Sum.inr.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              refine le_trans (le_of_eq (prTrue (runLog C σ (next (σ.symm y)))).symm)
                (prEvent_mono _ _ _ fun z _ hc => ?_)
              exact (clean_cons.mp hc).1 hx'
            · exact zero_le
          · rw [if_neg hy]
            exact (ih (σ.symm y)).trans
              (prEvent_mono _ _ _ fun z hz hc => hz (clean_cons.mp hc).2)

/-! ## Uniform salts: marginals and union bounds -/

theorem sum_point_eq_one {S : Type} [Fintype S] (mx : ProbComp S) :
    ∑ a, Pr{let x ← mx}[x = a] = 1 := by
  classical
  have h := prEvent_bind_eq_sum_fintype mx pure fun _ => True
  rw [bind_pure, prTrue] at h
  rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [prEvent_pure, if_pos trivial, mul_one]

/-- Two independent draws of a uniform salt. -/
theorem pair_sum {S α : Type} [Fintype S] (salt : ProbComp S) (P₀ : ℝ≥0∞)
    (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀) (K : S → S → ProbComp α) (q : α → Prop) :
    Pr{let z ← (salt >>= fun s => salt >>= fun s' => K s s')}[q z] =
      P₀ * P₀ * ∑ p : S × S, Pr{let z ← K p.1 p.2}[q z] := by
  rw [prEvent_bind_eq_sum_fintype]
  simp only [prEvent_bind_eq_sum_fintype, hunif]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [mul_assoc]

/-- A uniform salt function hits a given value at a given position with probability at most
`1 / |U|`. -/
theorem marginal_le {Pos U : Type} [Fintype Pos] [DecidableEq Pos] [Fintype U]
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (j : Pos) (u : U) : Pr{let s ← salt}[s j = u] ≤ (Fintype.card U : ℝ≥0∞)⁻¹ := by
  classical
  have expand : ∀ q : (Pos → U) → Prop,
      Pr{let s ← salt}[q s] = ∑ a, P₀ * Pr{let x ← (pure a : ProbComp (Pos → U))}[q x] := by
    intro q
    have h := prEvent_bind_eq_sum_fintype salt pure q
    rw [bind_pure] at h
    rw [h]
    simp only [hunif]
  have same : ∀ u', Pr{let s ← salt}[s j = u'] = Pr{let s ← salt}[s j = u] := by
    intro u'
    rw [expand, expand]
    let e : (Pos → U) ≃ (Pos → U) :=
      Equiv.piCongrRight fun k => if k = j then Equiv.swap u u' else Equiv.refl U
    refine Fintype.sum_equiv e _ _ fun a => ?_
    rw [prEvent_pure, prEvent_pure]
    have he : e a j = Equiv.swap u u' (a j) := by simp [e]
    rw [he]
    by_cases h : a j = u'
    · rw [if_pos h, if_pos (by rw [h]; exact Equiv.swap_apply_right u u')]
    · have h' : Equiv.swap u u' (a j) ≠ u := by
        intro h'
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h'
        exact h h'
      rw [if_neg h, if_neg h']
  have total : ∑ u', Pr{let s ← salt}[s j = u'] ≤ 1 := by
    have h := sum_prEvent_eq_some_le_one salt fun s => some (s j)
    simpa only [Option.some.injEq] using h
  simp only [same, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
  rw [ENNReal.le_inv_iff_mul_le, mul_comm]
  exact total

/-- Union bound over a list for a salt-dependent set. -/
theorem list_hit_le {S : Type} (salt : ProbComp S) (T : S → Finset PWord) (l : List PWord)
    (ε : ℝ≥0∞) (hpt : ∀ x, Pr{let s ← salt}[x ∈ T s] ≤ ε) :
    Pr{let s ← salt}[¬ Clean (T s) l] ≤ l.length * ε := by
  classical
  calc Pr{let s ← salt}[¬ Clean (T s) l] ≤ Pr{let s ← salt}[∃ x ∈ l.toFinset, x ∈ T s] :=
        prEvent_mono _ _ _ fun s hs => by
          unfold Clean at hs
          push Not at hs
          obtain ⟨x, hx, hT⟩ := hs
          exact ⟨x, List.mem_toFinset.mpr hx, hT⟩
    _ ≤ l.toFinset.card * ε := prEvent_exists_finset_le_card_mul _ _ _ fun x _ => hpt x
    _ ≤ l.length * ε := by
        refine mul_le_mul_left ?_ _
        exact_mod_cast List.toFinset_card_le l

/-- **Union bound for an independent salt.** A salt drawn before a computation that ignores it
hits one of at most `t` touched points with probability at most `t * ε`. -/
theorem fresh_salt_le {S γ δ : Type} [Fintype S] (salt : ProbComp S) (m : ProbComp γ)
    (rec : S → γ → δ) (q : δ → Prop) (T : S → Finset PWord) (list : γ → List PWord) (t : ℕ)
    (ε : ℝ≥0∞) (hq : ∀ s z, q (rec s z) → ¬ Clean (T s) (list z))
    (hlen : ∀ z ∈ support m, (list z).length ≤ t)
    (hpt : ∀ x, Pr{let s ← salt}[x ∈ T s] ≤ ε) :
    Pr{let y ← (salt >>= fun s => rec s <$> m)}[q y] ≤ t * ε := by
  calc Pr{let y ← (salt >>= fun s => rec s <$> m)}[q y]
      ≤ Pr{let y ← (salt >>= fun s => (fun z => (s, z)) <$> m)}[¬ Clean (T y.1) (list y.2)] := by
        refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun s => ?_
        rw [prEvent_map, prEvent_map]
        exact prEvent_mono _ _ _ fun z hz => hq s z hz
    _ = Pr{let y ← (m >>= fun z => (fun s => (s, z)) <$> salt)}[¬ Clean (T y.1) (list y.2)] := by
        have h := prEvent_bind_bind_swap_of_countable_left salt m
          (fun s z => ¬ Clean (T s) (list z))
        simpa only [map_bind, Functor.map_map, Function.comp_def] using h
    _ ≤ t * ε := by
        refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
        rw [prEvent_map]
        refine (list_hit_le salt T (list z) ε hpt).trans ?_
        refine mul_le_mul_left ?_ _
        exact_mod_cast hlen z hz

namespace SaltLayout
variable {Ch Pos U : Type} [DecidableEq Pos] (SL : SaltLayout Ch Pos U)

theorem mem_sset (c : Ch) (s : Pos → U) (σ : Perm) (x : PWord) (hx : x ∈ SL.sset c s σ) :
    ∃ j, SL.tag x = some j ∧ SL.saltOf x = s j := by
  unfold sset swapPts at hx
  rcases Finset.mem_union.mp hx with h | h <;>
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    rw [wpt_toLeaf]
    exact ⟨j, SL.tag_W _ _ _ _ _, SL.saltOf_W _ _ _ _ _⟩

theorem sset_point_le [Fintype Pos] [Fintype U] (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞)
    (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀) (c : Ch) (σ : Perm) (x : PWord) :
    Pr{let s ← salt}[x ∈ SL.sset c s σ] ≤ (Fintype.card U : ℝ≥0∞)⁻¹ := by
  cases ht : SL.tag x with
  | none =>
    rw [prEvent_eq_zero_of_forall_not _ _ fun s hs => by
      obtain ⟨j, hj, -⟩ := SL.mem_sset c s σ x hs
      rw [ht] at hj
      cases hj]
    exact zero_le
  | some j =>
    refine (prEvent_mono _ _ _ fun s hs => ?_).trans (marginal_le salt P₀ hunif j (SL.saltOf x))
    obtain ⟨j', hj', hu⟩ := SL.mem_sset c s σ x hs
    rw [ht] at hj'
    cases hj'
    exact hu.symm

/-! ## The step-two experiment -/

section Bound
variable [Fintype Pos] [Fintype U] (C : Compression) {β V : Type} (A₁ : OracleComp World Ch)
  (salt : ProbComp (Pos → U)) (A₂ : Ch → V → OracleComp World β)
  (F : Ch → (Pos → U) → (Pos → PWord) → V)

/-- A step-two record: challenge, stage-one log, permutation, real and reference salts, and
stage two's result. -/
abbrev Rec (Ch Pos U ρ : Type) := Ch × List PWord × Perm × ((Pos → U) × (Pos → U)) × ρ

/-- Stage two of world 0 after stage one, with a reference salt drawn too, logging touches. -/
noncomputable def tlog (c : Ch) (l : List PWord) (σ : Perm) : ProbComp (Rec Ch Pos U (List PWord)) :=
  salt >>= fun s => salt >>= fun s' =>
    (fun r => (c, l, σ, (s, s'), r.2)) <$> runLog C σ (A₂ c (SL.viewF F c s σ))

/-- Stage two of world 0, cut at its first touch of `U = S(s) ∪ S(s*)`. -/
noncomputable def tcut (c : Ch) (l : List PWord) (σ : Perm) : ProbComp (Rec Ch Pos U (β ⊕ (PWord × Bool))) :=
  salt >>= fun s => salt >>= fun s' =>
    (fun r => (c, l, σ, (s, s'), r)) <$>
      runCut C (SL.uset c (s, s') σ) σ (A₂ c (SL.viewF F c s σ))

/-- The whole world-0 experiment with continuation `T` after stage one. -/
noncomputable def whole {α : Type} (T : Ch → List PWord → Perm → ProbComp α) : ProbComp α :=
  ($ᵗ Perm : ProbComp Perm) >>= fun σ => runLog C σ A₁ >>= fun r => T r.1 r.2 σ

def badR (z : Rec Ch Pos U (List PWord)) : Prop :=
  ¬ Clean (SL.sset z.1 z.2.2.2.1.1 z.2.2.1) (z.2.1 ++ z.2.2.2.2)
def hitReal {ρ : Type} (z : Rec Ch Pos U ρ) : Prop :=
  ¬ Clean (SL.sset z.1 z.2.2.2.1.1 z.2.2.1) z.2.1
def hitRef1 {ρ : Type} (z : Rec Ch Pos U ρ) : Prop :=
  ¬ Clean (SL.sset z.1 z.2.2.2.1.2 z.2.2.1) z.2.1
def hitRef (z : Rec Ch Pos U (List PWord)) : Prop :=
  ¬ Clean (SL.sset z.1 z.2.2.2.1.2 z.2.2.1) (z.2.1 ++ z.2.2.2.2)
def e0 (z : Rec Ch Pos U (β ⊕ (PWord × Bool))) : Prop :=
  SL.E0 z.1 z.2.2.2.1 z.2.2.1 z.2.1 z.2.2.2.2
def estar (z : Rec Ch Pos U (β ⊕ (PWord × Bool))) : Prop :=
  SL.Estar z.1 z.2.2.2.1 z.2.2.1 z.2.1 z.2.2.2.2
/-- The range-hit event of the whole experiment (remaining lemma R3c bounds it). -/
def rh (z : Rec Ch Pos U (β ⊕ (PWord × Bool))) : Prop :=
  SL.RH z.1 z.2.2.2.1 z.2.2.1 z.2.1 z.2.2.2.2

theorem split_point (c : Ch) (l : List PWord) (σ : Perm) (s s' : Pos → U) :
    Pr{let z ← ((fun r => (c, l, σ, (s, s'), r.2)) <$>
        runLog C σ (A₂ c (SL.viewF F c s σ)))}[SL.badR z] ≤
      Pr{let z ← ((fun r => (c, l, σ, (s, s'), r.2)) <$>
        runLog C σ (A₂ c (SL.viewF F c s σ)))}[SL.hitReal z ∨ SL.hitRef1 z] +
      Pr{let z ← ((fun r => (c, l, σ, (s, s'), r)) <$>
        runCut C (SL.uset c (s, s') σ) σ (A₂ c (SL.viewF F c s σ)))}[
          SL.e0 z ∨ SL.rh z ∨ SL.estar z] := by
  rw [prEvent_map, prEvent_map, prEvent_map]
  by_cases clean : Clean (SL.uset c (s, s') σ) l
  · refine le_add_left ?_
    have cleanS : Clean (SL.sset c s σ) l := fun x hx hS =>
      clean x hx (Finset.mem_union_left _ hS)
    have sub : SL.sset c s σ ⊆ SL.uset c (s, s') σ := fun x hx => Finset.mem_union_left _ hx
    calc _ = Pr{let z ← runLog C σ (A₂ c (SL.viewF F c s σ))}[¬ Clean (SL.sset c s σ) z.2] :=
          prEvent_congr _ _ _ fun z => by
            show ¬ Clean (SL.sset c s σ) (l ++ z.2) ↔ ¬ Clean (SL.sset c s σ) z.2
            rw [clean_append]
            exact ⟨fun h hc => h ⟨cleanS, hc⟩, fun h hc => h hc.2⟩
      _ ≤ _ := log_touch_le_cut C _ _ sub σ _
      _ ≤ _ := prEvent_mono _ _ _ fun r hr => by
          obtain ⟨x, b, rfl, hxU⟩ := hr
          show SL.E0 c (s, s') σ l (Sum.inr (x, b)) ∨ SL.RH c (s, s') σ l (Sum.inr (x, b)) ∨
            SL.Estar c (s, s') σ l (Sum.inr (x, b))
          rcases Finset.mem_union.mp hxU with hs | hs'
          · by_cases hrh : b = true ∧ x ∈ SL.w0set c s σ
            · exact Or.inr (Or.inl ⟨clean, x, by rw [hrh.1], hrh.2⟩)
            · exact Or.inl ⟨clean, x, b, rfl, hs, hrh⟩
          · exact Or.inr (Or.inr ⟨clean, x, b, rfl, hs'⟩)
  · refine le_add_right ?_
    have hc : ¬ Clean (SL.sset c s σ) l ∨ ¬ Clean (SL.sset c s' σ) l := by
      unfold Clean at clean
      push Not at clean
      obtain ⟨x, hx, hU⟩ := clean
      rcases Finset.mem_union.mp hU with h | h
      · exact Or.inl fun hc => hc x hx h
      · exact Or.inr fun hc => hc x hx h
    calc _ ≤ (1 : ℝ≥0∞) := prEvent_le_one _
      _ = Pr{let z ← runLog C σ (A₂ c (SL.viewF F c s σ))}[True] := (prTrue _).symm
      _ ≤ _ := prEvent_mono _ _ _ fun z _ => hc

theorem estar_point (c : Ch) (l : List PWord) (σ : Perm) (s s' : Pos → U) :
    Pr{let z ← ((fun r => (c, l, σ, (s, s'), r)) <$>
        runCut C (SL.uset c (s, s') σ) σ (A₂ c (SL.viewF F c s σ)))}[SL.estar z] ≤
      Pr{let z ← ((fun r => (c, l, σ, (s, s'), r.2)) <$>
        runLog C σ (A₂ c (SL.viewF F c s σ)))}[SL.hitRef z] := by
  rw [prEvent_map, prEvent_map]
  refine (prEvent_mono _ _ _ fun r hr => ?_).trans
    ((cut_in_le_log C (SL.uset c (s, s') σ) (SL.sset c s' σ) σ _).trans
      (prEvent_mono _ _ _ fun z hz => ?_))
  · obtain ⟨_, x, b, rfl, hx⟩ := hr
    exact ⟨x, b, rfl, hx⟩
  · show ¬ Clean (SL.sset c s' σ) (l ++ z.2)
    rw [clean_append]
    exact fun h => hz h.2

theorem bad_le_badR :
    Pr{let z ← experiment C A₁ salt A₂
        (fun b c s σ => F c s fun j => σ (wpt SL.toLeaf c s σ b j)) (swapPts SL.toLeaf)
        false}[Bad z] ≤
      Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.badR z] := by
  unfold experiment whole tail tlog
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun σ => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun s => ?_
  rw [bind_pure_comp, prEvent_map, prEvent_bind_eq_sum_fintype]
  simp only [prEvent_map]
  have hX : ∀ s' : Pos → U,
      Pr{let z ← runLog C σ (A₂ r.1 (SL.viewF F r.1 s σ))}[
        SL.badR (r.1, r.2, σ, (s, s'), z.2)] =
      Pr{let z ← runLog C σ (A₂ r.1 (SL.viewF F r.1 s σ))}[
        ¬ Clean (SL.sset r.1 s σ) (r.2 ++ z.2)] := fun _ => rfl
  simp only [hX]
  rw [← Finset.sum_mul, sum_point_eq_one, one_mul]
  exact le_of_eq rfl

theorem whole_split :
    Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.badR z] ≤
      Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitReal z ∨ SL.hitRef1 z] +
      Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[
        SL.e0 z ∨ SL.rh z ∨ SL.estar z] := by
  unfold whole tlog tcut
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun σ => ?_
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun r => ?_
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun s => ?_
  refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun s' => ?_
  exact SL.split_point C A₂ F r.1 r.2 σ s s'

theorem whole_estar :
    Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.estar z] ≤
      Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitRef z] := by
  unfold whole tlog tcut
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun σ => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun s => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun s' => ?_
  exact SL.estar_point C A₂ F r.1 r.2 σ s s'

theorem whole_e0 (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (hF : ∀ c s s' o, (∀ j, j ∉ SL.swapSet c → s j = s' j) → F c s o = F c s' o) :
    Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.e0 z] ≤
      Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.estar z] := by
  unfold whole
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype]
  have point : ∀ σ : Perm, Pr{let t ← ($ᵗ Perm : ProbComp Perm)}[t = σ] =
      Pr{let t ← ($ᵗ Perm : ProbComp Perm)}[t = 1] := fun σ => uniform_point_eq σ 1
  simp only [point]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  have h := stage_one_le C A₁ (SL.tcut C salt A₂ F) (SL.tcut C salt A₂ F) SL.e0 SL.estar
    (fun L c => ?_) []
  · rw [ext_nil] at h
    simp only [List.map_nil, List.nil_append] at h
    exact h
  · unfold tcut
    simp only [pair_sum salt P₀ hunif]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_right ?_ _
    simp only [prEvent_map, e0, estar, Prod.mk.eta]
    exact SL.ref_swap_le C A₂ F hF L c

theorem whole_hitReal (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀) (t : ℕ)
    (hlen1 : ∀ σ, ∀ r ∈ support (runLog C σ A₁), r.2.length ≤ t) :
    Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitReal z] ≤
      t * (Fintype.card U : ℝ≥0∞)⁻¹ := by
  unfold whole tlog
  refine prEvent_bind_le_of_forall_le _ _ _ fun σ => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun r hr => ?_
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero salt _
    (fun s => ¬ Clean (SL.sset r.1 s σ) r.2) _ fun s hs => ?_).trans ?_
  · refine le_antisymm ((prEvent_bind_le_prEvent_of_forall_eq_zero salt _ (fun _ => False) _
      fun s' _ => ?_).trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun _ h => h)))
      (zero_le)
    rw [prEvent_map]
    exact prEvent_eq_zero_of_forall_not _ _ fun z hz => hs hz
  · refine (list_hit_le salt _ r.2 _ fun x => SL.sset_point_le salt P₀ hunif r.1 σ x).trans ?_
    refine mul_le_mul_left ?_ _
    exact_mod_cast hlen1 σ r hr

theorem whole_hitRef1 (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀) (t : ℕ)
    (hlen1 : ∀ σ, ∀ r ∈ support (runLog C σ A₁), r.2.length ≤ t) :
    Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitRef1 z] ≤
      t * (Fintype.card U : ℝ≥0∞)⁻¹ := by
  unfold whole tlog
  refine prEvent_bind_le_of_forall_le _ _ _ fun σ => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun r hr => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun s => ?_
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero salt _
    (fun s' => ¬ Clean (SL.sset r.1 s' σ) r.2) _ fun s' hs' => ?_).trans ?_
  · rw [prEvent_map]
    exact prEvent_eq_zero_of_forall_not _ _ fun z hz => hs' hz
  · refine (list_hit_le salt _ r.2 _ fun x => SL.sset_point_le salt P₀ hunif r.1 σ x).trans ?_
    refine mul_le_mul_left ?_ _
    exact_mod_cast hlen1 σ r hr

theorem whole_hitRef (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀) (t : ℕ)
    (hlen2 : ∀ σ, ∀ r ∈ support (runLog C σ A₁), ∀ v, ∀ r₂ ∈ support (runLog C σ (A₂ r.1 v)),
      r.2.length + r₂.2.length ≤ t) :
    Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitRef z] ≤
      t * (Fintype.card U : ℝ≥0∞)⁻¹ := by
  unfold whole tlog
  refine prEvent_bind_le_of_forall_le _ _ _ fun σ => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun r hr => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun s => ?_
  exact fresh_salt_le salt (runLog C σ (A₂ r.1 (SL.viewF F r.1 s σ)))
    (fun s' r₂ => (r.1, r.2, σ, (s, s'), r₂.2)) SL.hitRef (fun s' => SL.sset r.1 s' σ)
    (fun r₂ => r.2 ++ r₂.2) t _ (fun _ _ h => h)
    (fun z hz => by rw [List.length_append]; exact hlen2 σ r hr _ z hz)
    (fun x => SL.sset_point_le salt P₀ hunif r.1 σ x)

/-- **Step 2 for a fixed compression table.** The touch probability of world 0 is at most
`4t/|U|` plus the range-hit mass. -/
theorem bad_le (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (hF : ∀ c s s' o, (∀ j, j ∉ SL.swapSet c → s j = s' j) → F c s o = F c s' o) (t : ℕ)
    (hlen1 : ∀ σ, ∀ r ∈ support (runLog C σ A₁), r.2.length ≤ t)
    (hlen2 : ∀ σ, ∀ r ∈ support (runLog C σ A₁), ∀ v, ∀ r₂ ∈ support (runLog C σ (A₂ r.1 v)),
      r.2.length + r₂.2.length ≤ t) :
    Pr{let z ← experiment C A₁ salt A₂
        (fun b c s σ => F c s fun j => σ (wpt SL.toLeaf c s σ b j)) (swapPts SL.toLeaf)
        false}[Bad z] ≤
      4 * (t * (Fintype.card U : ℝ≥0∞)⁻¹) +
        Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.rh z] := by
  set ε := (t : ℝ≥0∞) * (Fintype.card U : ℝ≥0∞)⁻¹
  have hR := SL.whole_hitReal C A₁ salt A₂ F P₀ hunif t hlen1
  have hR1 := SL.whole_hitRef1 C A₁ salt A₂ F P₀ hunif t hlen1
  have hRef := SL.whole_hitRef C A₁ salt A₂ F P₀ hunif t hlen2
  have hE := SL.whole_estar C A₁ salt A₂ F
  have h0 := SL.whole_e0 C A₁ salt A₂ F P₀ hunif hF
  calc _ ≤ _ := SL.bad_le_badR C A₁ salt A₂ F
    _ ≤ _ := SL.whole_split C A₁ salt A₂ F
    _ ≤ (Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitReal z] +
          Pr{let z ← SaltLayout.whole C A₁ (SL.tlog C salt A₂ F)}[SL.hitRef1 z]) +
        (Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.e0 z] +
          (Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.rh z] +
            Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.estar z])) :=
        add_le_add (prEvent_or_le _ _ _)
          ((prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_or_le _ _ _)))
    _ ≤ (ε + ε) + (ε + (Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.rh z] + ε)) :=
        add_le_add (add_le_add hR hR1)
          (add_le_add ((h0.trans hE).trans hRef) (add_le_add le_rfl (hE.trans hRef)))
    _ = 4 * ε + Pr{let z ← SaltLayout.whole C A₁ (SL.tcut C salt A₂ F)}[SL.rh z] := by ring

end Bound
end SaltLayout


/-! ## Query budget: touched points from the contract's `QueryBound`

`some_supported_result` and `counted_query_support` follow the public accepted submission's
`HidingQueries.lean`. -/

theorem some_supported_result {α : Type} (computation : OracleComp World α) :
    ∃ result, result ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact ⟨value, by simp⟩
  | query_bind query next ih =>
    obtain ⟨result, reached⟩ := ih default
    exact ⟨result, (mem_support_bind_iff _ _ _).mpr
      ⟨default, mem_support_query query default, reached⟩⟩

theorem counted_query_support {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (answer : World.Range query)
    (result : α × Nat) (reached : result ∈ support (Hiding.counted (next answer))) :
    (result.1, Oracle.callCost query + result.2) ∈ support
      (Hiding.counted ((liftM (World.query query) : OracleComp World _) >>= next)) := by
  rw [Hiding.counted, costDist, instrumentedRun, simulateQ_bind, simulateQ_query, WriterT.run_bind]
  refine (mem_support_bind_iff _ _ _).mpr
    ⟨(answer, (Multiplicative.ofAdd (Oracle.callCost query) : Multiplicative Nat)), ?_, ?_⟩
  · simp [QueryImpl.withAddCost, QueryImpl.withCost]
  · change (result.1, Oracle.callCost query + result.2) ∈ support
      ((fun value : α × Nat => (value.1, Oracle.callCost query + value.2)) <$>
        Hiding.counted (next answer))
    rw [support_map]
    exact ⟨result, reached, by simp [Nat.add_comm]⟩

/-- Every logged run is an instrumented execution whose public-call count covers the touched
points. -/
theorem runLog_counted (C : Compression) (σ : Perm) {β : Type} (comp : OracleComp World β) :
    ∀ z ∈ support (runLog C σ comp),
      ∃ n, (z.1, n) ∈ support (Hiding.counted comp) ∧ z.2.length ≤ n := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro z hz
    rw [runLog_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨⟨a, n⟩, reached⟩ :=
      some_supported_result (Hiding.counted (pure value : OracleComp World β))
    have h1 : a = value := by
      have fst : Prod.fst <$> Hiding.counted (pure value : OracleComp World β) = pure value :=
        fst_map_run_simulateQ_addCostOracle Oracle.callCost (pure value)
      have ha : a ∈ support (Prod.fst <$> Hiding.counted (pure value : OracleComp World β)) := by
        rw [support_map]
        exact ⟨(a, n), reached, rfl⟩
      rw [fst, support_pure, Set.mem_singleton_iff] at ha
      exact ha
    subst h1
    exact ⟨n, reached, Nat.zero_le _⟩
  | query_bind t next ih =>
    intro z hz
    rw [runLog_query_bind] at hz
    rcases t with coins | publicQuery
    · simp only [stepLog] at hz
      obtain ⟨a, -, ha⟩ := (mem_support_bind_iff _ _ _).mp hz
      obtain ⟨n, hn, len⟩ := ih a z ha
      exact ⟨_, counted_query_support (.inl coins) next a (z.1, n) hn, by
        show z.2.length ≤ Oracle.callCost (.inl coins) + n
        omega⟩
    · rcases publicQuery with x | permQuery
      · simp only [stepLog] at hz
        obtain ⟨n, hn, len⟩ := ih (C x) z hz
        exact ⟨_, counted_query_support (.inr (.inl x)) next (C x) (z.1, n) hn, by
          show z.2.length ≤ Oracle.callCost (.inr (.inl x)) + n
          omega⟩
      · rcases permQuery with x | y
        · simp only [stepLog] at hz
          rw [support_map] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          obtain ⟨n, hn, len⟩ := ih (σ x) w hw
          refine ⟨_, counted_query_support (.inr (.inr (.inl x))) next (σ x) (w.1, n) hn, ?_⟩
          show (x :: w.2).length ≤ Oracle.callCost (.inr (.inr (.inl x))) + n
          have one : Oracle.callCost (.inr (.inr (.inl x))) = 1 := rfl
          rw [List.length_cons, one]
          omega
        · simp only [stepLog] at hz
          rw [support_map] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          obtain ⟨n, hn, len⟩ := ih (σ.symm y) w hw
          refine ⟨_, counted_query_support (.inr (.inr (.inr y))) next (σ.symm y) (w.1, n) hn,
            ?_⟩
          show (σ.symm y :: w.2).length ≤ Oracle.callCost (.inr (.inr (.inr y))) + n
          have one : Oracle.callCost (.inr (.inr (.inr y))) = 1 := rfl
          rw [List.length_cons, one]
          omega

/-- The contract's two-stage budget bounds the touched points of both stages. -/
theorem touched_length {St Out : Type} {k : Nat} (adversary : Hiding.HidingAdversary St Out k)
    (t : ℕ) (bounded : Hiding.QueryBound adversary t) (C : Compression) (σ : Perm) :
    (∀ r ∈ support (runLog C σ adversary.choose), r.2.length ≤ t) ∧
    (∀ r ∈ support (runLog C σ adversary.choose), ∀ v : Commitment × Proof,
      ∀ r₂ ∈ support (runLog C σ (adversary.observe r.1.aux v.1 v.2)),
        r.2.length + r₂.2.length ≤ t) := by
  constructor
  · intro r hr
    obtain ⟨n, hn, len⟩ := runLog_counted C σ adversary.choose r hr
    exact len.trans (bounded (r.1, n) hn).1
  · intro r hr v r₂ hr₂
    obtain ⟨n, hn, len⟩ := runLog_counted C σ adversary.choose r hr
    obtain ⟨m, hm, len2⟩ := runLog_counted C σ _ r₂ hr₂
    have total : n + m ≤ t := (bounded (r.1, n) hn).2 v.1 v.2 (r₂.1, m) hm
    omega

/-! ## The contract statement -/

/-- **Hiding of the salted two-call leaf, up to the range hit.** Remaining hypotheses: the
refinement `hhonest` with a uniform salt (R2) and the range-hit bound `hRH` (R3c). -/
theorem leaf_hiding_bound (scheme : Scheme) {St Out Pos U : Type} {k : Nat} [Fintype Pos]
    [DecidableEq Pos] [Fintype U] (SL : SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (adversary : Hiding.HidingAdversary St Out k) (t : ℕ)
    (bounded : Hiding.QueryBound adversary t)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (F : Compression → Hiding.HidingChallenge St k → (Pos → U) → (Pos → PWord) →
      Commitment × Proof)
    (hF : ∀ C c s s' o, (∀ j, j ∉ SL.swapSet c → s j = s' j) → F C c s o = F C c s' o)
    (hhonest : ∀ (C : Compression) (σ : Perm) (b : Bool) (c : Hiding.HidingChallenge St k)
      (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s => pure (F C c s fun j => σ (wpt SL.toLeaf c s σ b j)))}[q v])
    (εRH : ℝ≥0∞)
    (hRH : ∀ C : Compression, Pr{let z ← (SaltLayout.whole C adversary.choose
        (SL.tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) (F C)))}[SL.rh z] ≤ εRH) :
    letI : MeasurableSpace Out := ⊤
    measureETVDist (Hiding.runHiding (Hiding.hidingExperiment scheme adversary false))
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary true)) ≤
      4 * (t * (Fintype.card U : ℝ≥0∞)⁻¹) + εRH := by
  letI : MeasurableSpace Out := ⊤
  refine (leaf_hiding_le_bad scheme SL.toLeaf adversary salt F hhonest).trans ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun C => ?_
  have h1 : ∀ σ, ∀ r ∈ support (runLog C σ adversary.choose), r.2.length ≤ t :=
    fun σ => (touched_length adversary t bounded C σ).1
  have h2 : ∀ σ, ∀ r ∈ support (runLog C σ adversary.choose), ∀ v : Commitment × Proof,
      ∀ r₂ ∈ support (runLog C σ ((fun c v => adversary.observe c.aux v.1 v.2) r.1 v)),
        r.2.length + r₂.2.length ≤ t :=
    fun σ => (touched_length adversary t bounded C σ).2
  have hb := SL.bad_le C adversary.choose salt (fun c v => adversary.observe c.aux v.1 v.2)
    (F C) P₀ hunif (hF C) t h1 h2
  have hr := hRH C
  exact hb.trans (add_le_add le_rfl hr)

/-- **R4: the contract's error.** With 128-bit salts and the range hit at most `t / 2^128`, the
hiding distance is at most `HIDING_ERROR k t = min 1 ((t + 1) / 2^120)`, for every opening size. -/
theorem leaf_hiding_error (scheme : Scheme) {St Out Pos U : Type} {k : Nat} [Fintype Pos]
    [DecidableEq Pos] [Fintype U] (SL : SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (adversary : Hiding.HidingAdversary St Out k) (t : ℕ)
    (bounded : Hiding.QueryBound adversary t)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (F : Compression → Hiding.HidingChallenge St k → (Pos → U) → (Pos → PWord) →
      Commitment × Proof)
    (hF : ∀ C c s s' o, (∀ j, j ∉ SL.swapSet c → s j = s' j) → F C c s o = F C c s' o)
    (hhonest : ∀ (C : Compression) (σ : Perm) (b : Bool) (c : Hiding.HidingChallenge St k)
      (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s => pure (F C c s fun j => σ (wpt SL.toLeaf c s σ b j)))}[q v])
    (hU : Fintype.card U = 2 ^ 128)
    (hRH : ∀ C : Compression, Pr{let z ← (SaltLayout.whole C adversary.choose
        (SL.tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) (F C)))}[SL.rh z] ≤
          t * (Fintype.card U : ℝ≥0∞)⁻¹) :
    letI : MeasurableSpace Out := ⊤
    measureTVDist (Hiding.runHiding (Hiding.hidingExperiment scheme adversary false))
        (Hiding.runHiding (Hiding.hidingExperiment scheme adversary true)) ≤ HIDING_ERROR k t := by
  let : MeasurableSpace Out := ⊤
  have hE := leaf_hiding_bound scheme SL adversary t bounded salt P₀ hunif F hF hhonest _ hRH
  set x : ℝ≥0∞ := (t : ℝ≥0∞) * (Fintype.card U : ℝ≥0∞)⁻¹ with hx
  have h5 : 4 * x + x = 5 * x := by ring
  have hx' : x = ENNReal.ofReal ((t : ℝ) / 2 ^ 128) := by
    rw [hx, hU, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]
    norm_cast
  have real : 5 * ((t : ℝ) / 2 ^ 128) ≤ ((t : ℝ) + 1) / 2 ^ 120 := by
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    calc 5 * ((t : ℝ) / 2 ^ 128) = (t : ℝ) * (5 / 2 ^ 128) := by ring
      _ ≤ (t : ℝ) * (1 / 2 ^ 120) := mul_le_mul_of_nonneg_left (by norm_num) ht
      _ = (t : ℝ) / 2 ^ 120 := by ring
      _ ≤ ((t : ℝ) + 1) / 2 ^ 120 := by gcongr; linarith
  have bound : 4 * x + x ≤ ENNReal.ofReal (((t : ℝ) + 1) / 2 ^ 120) := by
    rw [h5, hx', ← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal real
  unfold HIDING_ERROR HIDING_SECURITY_BITS
  refine le_min (measureTVDist_le_one _ _) ?_
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hE.trans bound)

/-- **The contract's hiding property for a salted two-call leaf scheme.** The remaining
hypotheses are R2 (the leaf layouts `SL`, uniform salts, the view `F` reading salts only off the
swap set, and the refinement `hhonest`) and R3c (the range-hit bound `hRH`). -/
theorem scheme_hiding (scheme : Scheme) {Pos U : Type} [Fintype Pos] [DecidableEq Pos]
    [Fintype U] (hU : Fintype.card U = 2 ^ 128)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (SL : ∀ (St : Type) (k : Nat), SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (F : ∀ (St : Type) (k : Nat), Compression → Hiding.HidingChallenge St k → (Pos → U) →
      (Pos → PWord) → Commitment × Proof)
    (hF : ∀ St k C c s s' o, (∀ j, j ∉ (SL St k).swapSet c → s j = s' j) →
      F St k C c s o = F St k C c s' o)
    (hhonest : ∀ (St : Type) (k : Nat) (C : Compression) (σ : Perm) (b : Bool)
      (c : Hiding.HidingChallenge St k) (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s =>
          pure (F St k C c s fun j => σ (wpt (SL St k).toLeaf c s σ b j)))}[q v])
    (hRH : ∀ (St Out : Type) (k : Nat) (adversary : Hiding.HidingAdversary St Out k) (t : Nat),
      Hiding.QueryBound adversary t → ∀ C : Compression,
        Pr{let z ← (SaltLayout.whole C adversary.choose
          ((SL St k).tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) (F St k C)))}[
            (SL St k).rh z] ≤ t * (Fintype.card U : ℝ≥0∞)⁻¹) :
    scheme.Hiding HIDING_ERROR := by
  refine ⟨fun _ _ => by unfold HIDING_ERROR; exact le_min zero_le_one (by positivity), ?_⟩
  intro k t _ St Out adversary bounded
  exact leaf_hiding_error scheme (SL St k) adversary t bounded salt P₀ hunif (F St k) (hF St k)
    (hhonest St k) hU (hRH St Out k adversary t bounded)


/-! ## The range hit: a hazard bound for cut runs (R3c, core)

Inside a set `K` of permutations, a run cut at its first touch of `U` ends with an inverse query
answered inside `H ⊆ U` with summed mass at most `|K| · q · ε`, if every fresh inverse answer
lands in `H` for at most an `ε` fraction of the log-consistent permutations of `K`. -/

/-- The contract's public-query budget (compression and both permutation directions cost one). -/
def PublicQueryBound {β : Type} (comp : OracleComp World β) (budget : ℕ) : Prop :=
  IsQueryBound comp budget (fun t left => Oracle.callCost t ≤ left)
    (fun t left => left - Oracle.callCost t)

/-- Permutations of `K` consistent with a log. -/
@[irreducible] noncomputable def extK (K : Finset Perm) (L : PLog) : Finset Perm := by
  classical
  exact K.filter fun σ => σ ∈ ext L

theorem mem_extK {K : Finset Perm} {L : PLog} {σ : Perm} : σ ∈ extK K L ↔ σ ∈ K ∧ σ ∈ ext L := by
  classical
  unfold extK
  simp

theorem sum_extK_forward (K : Finset Perm) (L : PLog) (x : PWord) (G : Perm → PWord → ℝ≥0∞) :
    ∑ σ ∈ extK K L, G σ (σ x) = ∑ y, ∑ σ ∈ extK K (L ++ [(x, y)]), G σ y := by
  classical
  rw [← Finset.sum_fiberwise (extK K L) (fun σ => σ x) (fun σ => G σ (σ x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have fibre : (extK K L).filter (fun σ => σ x = y) = extK K (L ++ [(x, y)]) := by
    ext σ
    rw [Finset.mem_filter, mem_extK, mem_extK, mem_ext_append, and_assoc]
  rw [fibre]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [(mem_ext_append.mp (mem_extK.mp hσ).2).2]

theorem sum_extK_inverse (K : Finset Perm) (L : PLog) (y : PWord) (G : Perm → PWord → ℝ≥0∞) :
    ∑ σ ∈ extK K L, G σ (σ.symm y) = ∑ x, ∑ σ ∈ extK K (L ++ [(x, y)]), G σ x := by
  classical
  rw [← Finset.sum_fiberwise (extK K L) (fun σ => σ.symm y) (fun σ => G σ (σ.symm y))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have fibre : (extK K L).filter (fun σ => σ.symm y = x) = extK K (L ++ [(x, y)]) := by
    ext σ
    rw [Finset.mem_filter, mem_extK, mem_extK, mem_ext_append, Equiv.symm_apply_eq, and_assoc]
    exact and_congr Iff.rfl (and_congr Iff.rfl eq_comm)
  rw [fibre]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h : σ x = y := (mem_ext_append.mp (mem_extK.mp hσ).2).2
  rw [show σ.symm y = x by rw [Equiv.symm_apply_eq, h]]

theorem card_extK_forward (K : Finset Perm) (L : PLog) (x : PWord) :
    ((extK K L).card : ℝ≥0∞) = ∑ y, ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) := by
  have h := sum_extK_forward K L x fun _ _ => 1
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem card_extK_inverse (K : Finset Perm) (L : PLog) (y : PWord) :
    ((extK K L).card : ℝ≥0∞) = ∑ x, ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) := by
  have h := sum_extK_inverse K L y fun _ _ => 1
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem sum_point_le_one {S : Type} [Fintype S] (mx : ProbComp S) :
    ∑ a, Pr{let x ← mx}[x = a] ≤ 1 := le_of_eq (sum_point_eq_one mx)

/-- **Hazard bound for cut runs.** -/
theorem hazard_cut (C : Compression) (U H : Finset PWord) (hHU : H ⊆ U) (K : Finset Perm)
    (T : ℕ) (ε : ℝ≥0∞)
    (hfib : ∀ L : PLog, Clean U (L.map Prod.fst) → L.length < T → ∀ y, (∀ e ∈ L, e.2 ≠ y) →
      (((extK K L).filter fun σ => σ.symm y ∈ H).card : ℝ≥0∞) ≤ ε * (extK K L).card)
    {β : Type} (comp : OracleComp World β) :
    ∀ q, PublicQueryBound comp q → ∀ L : PLog, Clean U (L.map Prod.fst) → L.length + q ≤ T →
      ∑ σ ∈ extK K L, Pr{let r ← runCut C U σ comp}[∃ x, r = .inr (x, true) ∧ x ∈ H] ≤
        (extK K L).card * (q * ε) := by
  classical
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro q _ L _ _
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun σ _ => ?_)) zero_le
    rw [runCut_pure, prEvent_pure, if_neg]
    rintro ⟨x, h, -⟩
    cases h
  | query_bind t next ih =>
    intro q bounded L clean len
    change Oracle.callCost t ≤ q ∧
      (∀ a, PublicQueryBound (next a) (q - Oracle.callCost t)) at bounded
    simp only [runCut_query_bind]
    rcases t with coins | publicQuery
    · simp only [stepCut]
      simp only [prEvent_bind_eq_sum_fintype]
      rw [Finset.sum_comm]
      calc ∑ a, ∑ σ ∈ extK K L, Pr{let x ← (liftM (unifSpec.query coins) :
              ProbComp (unifSpec.Range coins))}[x = a] *
            Pr{let r ← runCut C U σ (next a)}[∃ x, r = .inr (x, true) ∧ x ∈ H]
          = ∑ a, Pr{let x ← (liftM (unifSpec.query coins) :
              ProbComp (unifSpec.Range coins))}[x = a] *
            ∑ σ ∈ extK K L, Pr{let r ← runCut C U σ (next a)}[
              ∃ x, r = .inr (x, true) ∧ x ∈ H] := by
            simp only [Finset.mul_sum]
        _ ≤ ∑ a, Pr{let x ← (liftM (unifSpec.query coins) :
              ProbComp (unifSpec.Range coins))}[x = a] * ((extK K L).card * (q * ε)) :=
            Finset.sum_le_sum fun a _ => mul_le_mul_right (ih a q (bounded.2 a) L clean len) _
        _ = (∑ a, Pr{let x ← (liftM (unifSpec.query coins) :
              ProbComp (unifSpec.Range coins))}[x = a]) * ((extK K L).card * (q * ε)) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * ((extK K L).card * (q * ε)) := mul_le_mul_left (sum_point_le_one _) _
        _ = _ := one_mul _
    · have one : 1 ≤ q := bounded.1
      have shrink : ((extK K L).card : ℝ≥0∞) * (((q - 1 : ℕ) : ℝ≥0∞) * ε) ≤
          (extK K L).card * (q * ε) := by
        refine mul_le_mul_right (mul_le_mul_left ?_ _) _
        exact_mod_cast Nat.sub_le q 1
      rcases publicQuery with x | permQuery
      · simp only [stepCut]
        exact (ih (C x) (q - 1) (bounded.2 (C x)) L clean (by omega)).trans shrink
      · rcases permQuery with x | y
        · simp only [stepCut]
          by_cases hx : x ∈ U
          · simp only [if_pos hx]
            refine le_trans (le_of_eq (Finset.sum_eq_zero fun σ _ => ?_)) zero_le
            rw [prEvent_pure, if_neg]
            rintro ⟨x', h, -⟩
            simp only [Sum.inr.injEq, Prod.mk.injEq] at h
            exact Bool.false_ne_true h.2
          · simp only [if_neg hx]
            refine (sum_extK_forward K L x
              (fun σ y => Pr{let r ← runCut C U σ (next y)}[∃ x, r = .inr (x, true) ∧ x ∈ H])).trans_le
              ?_
            calc ∑ y : PWord, ∑ σ ∈ extK K (L ++ [(x, y)]),
                  Pr{let r ← runCut C U σ (next y)}[∃ x, r = .inr (x, true) ∧ x ∈ H]
                ≤ ∑ y : PWord, ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) *
                    (((q - 1 : ℕ) : ℝ≥0∞) * ε) :=
                  Finset.sum_le_sum fun y _ => ih y (q - 1) (bounded.2 y) (L ++ [(x, y)])
                    (by
                      rw [List.map_append, clean_append]
                      exact ⟨clean, fun z hz => by
                        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hz
                        rw [hz]; exact hx⟩)
                    (by rw [List.length_append, List.length_singleton]; omega)
              _ = ((extK K L).card : ℝ≥0∞) * (((q - 1 : ℕ) : ℝ≥0∞) * ε) := by
                  rw [← Finset.sum_mul, ← card_extK_forward]
              _ ≤ _ := shrink
        · simp only [stepCut]
          let G : Perm → PWord → ℝ≥0∞ := fun σ x =>
            Pr{let r ← (if x ∈ U then (pure (.inr (x, true)) : ProbComp (β ⊕ (PWord × Bool)))
              else runCut C U σ (next x))}[∃ x, r = .inr (x, true) ∧ x ∈ H]
          refine (sum_extK_inverse K L y G).trans_le ?_
          have each : ∀ x, ∑ σ ∈ extK K (L ++ [(x, y)]), G σ x ≤
              ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) * (if x ∈ H then 1 else 0) +
                ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) * (((q - 1 : ℕ) : ℝ≥0∞) * ε) := by
            intro x
            by_cases hx : x ∈ U
            · refine le_trans (le_of_eq ?_) le_self_add
              have hG : ∀ σ, G σ x = if x ∈ H then 1 else 0 := by
                intro σ
                show Pr{let r ← (if x ∈ U then (pure (.inr (x, true)) :
                  ProbComp (β ⊕ (PWord × Bool))) else runCut C U σ (next x))}[
                    ∃ x, r = .inr (x, true) ∧ x ∈ H] = _
                rw [if_pos hx, prEvent_pure]
                by_cases hH : x ∈ H
                · rw [if_pos ⟨x, rfl, hH⟩, if_pos hH]
                · rw [if_neg, if_neg hH]
                  rintro ⟨x', h, hx'⟩
                  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
                  rw [h.1] at hH
                  exact hH hx'
              rw [Finset.sum_congr rfl fun σ _ => hG σ, Finset.sum_const, nsmul_eq_mul]
            · refine le_trans ?_ le_add_self
              have hG : ∀ σ, G σ x = Pr{let r ← runCut C U σ (next x)}[
                  ∃ x, r = .inr (x, true) ∧ x ∈ H] := by
                intro σ
                show Pr{let r ← (if x ∈ U then (pure (.inr (x, true)) :
                  ProbComp (β ⊕ (PWord × Bool))) else runCut C U σ (next x))}[
                    ∃ x, r = .inr (x, true) ∧ x ∈ H] = _
                rw [if_neg hx]
              rw [Finset.sum_congr rfl fun σ _ => hG σ]
              exact ih x (q - 1) (bounded.2 x) (L ++ [(x, y)])
                (by
                  rw [List.map_append, clean_append]
                  exact ⟨clean, fun z hz => by
                    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hz
                    rw [hz]; exact hx⟩)
                (by rw [List.length_append, List.length_singleton]; omega)
          have hits : ∑ x, ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) * (if x ∈ H then 1 else 0) =
              (((extK K L).filter fun σ => σ.symm y ∈ H).card : ℝ≥0∞) := by
            have h := sum_extK_inverse K L y fun _ x => if x ∈ H then 1 else 0
            simp only [Finset.sum_const, nsmul_eq_mul] at h
            rw [← h, Finset.sum_boole]
          have hazard : (((extK K L).filter fun σ => σ.symm y ∈ H).card : ℝ≥0∞) ≤
              ε * (extK K L).card := by
            by_cases logged : ∃ e ∈ L, e.2 = y
            · obtain ⟨e, he, hy⟩ := logged
              have empty : (extK K L).filter (fun σ => σ.symm y ∈ H) = ∅ := by
                refine Finset.filter_eq_empty_iff.mpr fun σ hσ hH => ?_
                have he' : σ e.1 = e.2 := mem_ext.mp (mem_extK.mp hσ).2 e he
                have hsymm : σ.symm y = e.1 := by rw [Equiv.symm_apply_eq, he', hy]
                rw [hsymm] at hH
                exact clean e.1 (List.mem_map_of_mem he) (hHU hH)
              rw [empty, Finset.card_empty, Nat.cast_zero]
              exact zero_le
            · exact hfib L clean (by omega) y fun e he h => logged ⟨e, he, h⟩
          calc ∑ x, ∑ σ ∈ extK K (L ++ [(x, y)]), G σ x
              ≤ ∑ x, (((extK K (L ++ [(x, y)])).card : ℝ≥0∞) * (if x ∈ H then 1 else 0) +
                  ((extK K (L ++ [(x, y)])).card : ℝ≥0∞) * (((q - 1 : ℕ) : ℝ≥0∞) * ε)) :=
                Finset.sum_le_sum fun x _ => each x
            _ = (((extK K L).filter fun σ => σ.symm y ∈ H).card : ℝ≥0∞) +
                  ((extK K L).card : ℝ≥0∞) * (((q - 1 : ℕ) : ℝ≥0∞) * ε) := by
                rw [Finset.sum_add_distrib, hits, ← Finset.sum_mul, ← card_extK_inverse]
            _ ≤ ε * (extK K L).card + ((extK K L).card : ℝ≥0∞) * (((q - 1 : ℕ) : ℝ≥0∞) * ε) :=
                add_le_add hazard le_rfl
            _ = ((extK K L).card : ℝ≥0∞) * ((((q - 1 : ℕ) : ℝ≥0∞) + 1) * ε) := by ring
            _ = (extK K L).card * (q * ε) := by
                rw [show ((q - 1 : ℕ) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) by
                  exact_mod_cast Nat.sub_add_cancel one]


/-- **Fresh inverse answers inside a swap-closed class.** If `K` is closed under post-composition
with transpositions of words of equal prefix outside a protected set `A`, and the hazard targets
`H` never map into `A`, then a fresh inverse answer lands in `H` for at most a
`|H| / (N - |A| - |L|)` fraction of the log-consistent permutations of `K`, where every prefix
class has at least `N` words. -/
theorem fibre_hazard {D : Type} [DecidableEq D] (pre : PWord → D) (N : ℕ)
    (hN : ∀ d, N ≤ (Finset.univ.filter fun y => pre y = d).card)
    (K : Finset Perm) (A H : Finset PWord)
    (hclosed : ∀ σ ∈ K, ∀ y y', pre y = pre y' → y ∉ A → y' ∉ A → Equiv.swap y y' * σ ∈ K)
    (hA : ∀ σ ∈ K, ∀ h ∈ H, σ h ∉ A)
    (L : PLog) (y : PWord) (fresh : ∀ e ∈ L, e.2 ≠ y) :
    ((extK K L).filter fun σ => σ.symm y ∈ H).card * (N - A.card - L.length) ≤
      H.card * (extK K L).card := by
  classical
  by_cases hyA : y ∈ A
  · have empty : (extK K L).filter (fun σ => σ.symm y ∈ H) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun σ hσ hH =>
        hA σ (mem_extK.mp hσ).1 _ hH (by rw [Equiv.apply_symm_apply]; exact hyA)
    rw [empty, Finset.card_empty, zero_mul]
    exact Nat.zero_le _
  · set S := extK K L
    set Y := ((Finset.univ.filter fun y' => pre y' = pre y) \ A) \ (L.map Prod.snd).toFinset
      with hYdef
    have hY : N - A.card - L.length ≤ Y.card := by
      rw [hYdef]
      have h1 := Finset.le_card_sdiff (L.map Prod.snd).toFinset
        ((Finset.univ.filter fun y' => pre y' = pre y) \ A)
      have h2 := Finset.le_card_sdiff A (Finset.univ.filter fun y' => pre y' = pre y)
      have h3 : (L.map Prod.snd).toFinset.card ≤ L.length := by
        have := List.toFinset_card_le (L.map Prod.snd)
        rwa [List.length_map] at this
      have h4 := hN (pre y)
      omega
    have same : ∀ h, ∀ y' ∈ Y, (S.filter fun σ => σ h = y).card =
        (S.filter fun σ => σ h = y').card := by
      intro h y' hy'
      have hy'Y := hy'
      simp only [Y, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset, List.mem_map] at hy'Y
      obtain ⟨⟨hpre, hy'A⟩, hy'L⟩ := hy'Y
      have keep : ∀ σ ∈ S, Equiv.swap y y' * σ ∈ S := by
        intro σ hσ
        obtain ⟨hK, hL⟩ := mem_extK.mp hσ
        refine mem_extK.mpr ⟨hclosed σ hK y y' hpre.symm hyA hy'A, mem_ext.mpr fun e he => ?_⟩
        rw [Equiv.Perm.mul_apply, mem_ext.mp hL e he]
        exact Equiv.swap_apply_of_ne_of_ne (fresh e he) fun h' => hy'L ⟨e, he, h'⟩
      refine Finset.card_nbij' (fun σ => Equiv.swap y y' * σ) (fun σ => Equiv.swap y y' * σ)
        ?_ ?_ ?_ ?_
      · intro σ hσ
        rw [Finset.mem_coe, Finset.mem_filter] at hσ ⊢
        refine ⟨keep σ hσ.1, ?_⟩
        rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_left]
      · intro σ hσ
        rw [Finset.mem_coe, Finset.mem_filter] at hσ ⊢
        refine ⟨keep σ hσ.1, ?_⟩
        rw [Equiv.Perm.mul_apply, hσ.2, Equiv.swap_apply_right]
      · intro σ _
        exact Equiv.swap_mul_self_mul y y' σ
      · intro σ _
        exact Equiv.swap_mul_self_mul y y' σ
    have each : ∀ h, (S.filter fun σ => σ h = y).card * Y.card ≤ S.card := by
      intro h
      calc (S.filter fun σ => σ h = y).card * Y.card
          = ∑ y' ∈ Y, (S.filter fun σ => σ h = y').card := by
            rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
            exact Finset.sum_congr rfl fun y' hy' => same h y' hy'
        _ = (S.filter fun σ => σ h ∈ Y).card :=
            Finset.sum_card_fiberwise_eq_card_filter ..
        _ ≤ S.card := Finset.card_filter_le _ _
    have split : (S.filter fun σ => σ.symm y ∈ H).card =
        ∑ h ∈ H, (S.filter fun σ => σ h = y).card := by
      rw [← Finset.sum_card_fiberwise_eq_card_filter]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.filter_congr fun σ _ => (Equiv.symm_apply_eq σ).trans eq_comm]
    calc (S.filter fun σ => σ.symm y ∈ H).card * (N - A.card - L.length)
        ≤ (S.filter fun σ => σ.symm y ∈ H).card * Y.card := Nat.mul_le_mul_left _ hY
      _ = ∑ h ∈ H, (S.filter fun σ => σ h = y).card * Y.card := by rw [split, Finset.sum_mul]
      _ ≤ ∑ _h ∈ H, S.card := Finset.sum_le_sum fun h _ => each h
      _ = H.card * S.card := by rw [Finset.sum_const, smul_eq_mul]


/-! ## The range hit in the step-two experiment -/

theorem public_query_bound_of_counted_support {α : Type} (computation : OracleComp World α)
    (budget : Nat) (bounded : ∀ result ∈ support (Hiding.counted computation), result.2 ≤ budget) :
    PublicQueryBound computation budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query))
    constructor
    · obtain ⟨result, reached⟩ := some_supported_result (Hiding.counted (next default))
      have bound := bounded _ (counted_query_support query next default result reached)
      change Oracle.callCost query + result.2 ≤ budget at bound
      omega
    · intro answer
      apply ih answer
      intro result reached
      have bound := bounded _ (counted_query_support query next answer result reached)
      change Oracle.callCost query + result.2 ≤ budget at bound
      omega

theorem counted_pure {β : Type} (value : β) :
    ∃ n, (value, n) ∈ support (Hiding.counted (pure value : OracleComp World β)) := by
  obtain ⟨⟨a, n⟩, reached⟩ :=
    some_supported_result (Hiding.counted (pure value : OracleComp World β))
  have h1 : a = value := by
    have fst : Prod.fst <$> Hiding.counted (pure value : OracleComp World β) = pure value :=
      fst_map_run_simulateQ_addCostOracle Oracle.callCost (pure value)
    have ha : a ∈ support (Prod.fst <$> Hiding.counted (pure value : OracleComp World β)) := by
      rw [support_map]
      exact ⟨(a, n), reached, rfl⟩
    rw [fst, support_pure, Set.mem_singleton_iff] at ha
    exact ha
  subst h1
  exact ⟨n, reached⟩

theorem card_ext_forward (L : PLog) (x : PWord) :
    ((ext L).card : ℝ≥0∞) = ∑ y, ((ext (L ++ [(x, y)])).card : ℝ≥0∞) := by
  have h := sum_ext_forward L x fun _ _ => 1
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem card_ext_inverse (L : PLog) (y : PWord) :
    ((ext L).card : ℝ≥0∞) = ∑ x, ((ext (L ++ [(x, y)])).card : ℝ≥0∞) := by
  have h := sum_ext_inverse L y fun _ _ => 1
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem coin_bound {ι α : Type} [Fintype ι] (mx : ProbComp ι) (f : ι → Perm → ProbComp α)
    (s : Finset Perm) (q : α → Prop) (B : ℝ≥0∞)
    (h : ∀ a, ∑ σ ∈ s, Pr{let z ← f a σ}[q z] ≤ B) :
    ∑ σ ∈ s, Pr{let z ← (mx >>= fun a => f a σ)}[q z] ≤ B := by
  simp only [prEvent_bind_eq_sum_fintype]
  rw [Finset.sum_comm]
  calc ∑ a, ∑ σ ∈ s, Pr{let x ← mx}[x = a] * Pr{let z ← f a σ}[q z]
      = ∑ a, Pr{let x ← mx}[x = a] * ∑ σ ∈ s, Pr{let z ← f a σ}[q z] := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ a, Pr{let x ← mx}[x = a] * B := Finset.sum_le_sum fun a _ => mul_le_mul_right (h a) _
    _ = (∑ a, Pr{let x ← mx}[x = a]) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * B := mul_le_mul_left (sum_point_le_one mx) _
    _ = B := one_mul B

/-- Stage one with a per-permutation budget: if every reachable continuation has summed mass at
most `|ext L'| · B` over the consistent permutations of a log no longer than the stage-one cost,
so has the whole run. -/
theorem stage_one_bound (C : Compression) {γ α : Type} (comp : OracleComp World γ)
    (K : γ → List PWord → Perm → ProbComp α) (q : α → Prop) (B : ℝ≥0∞) :
    ∀ L : PLog, (∀ (L' : PLog) (c : γ) (n : ℕ), (c, n) ∈ support (Hiding.counted comp) →
        L'.length ≤ L.length + n →
        ∑ σ ∈ ext L', Pr{let z ← K c (L'.map Prod.fst) σ}[q z] ≤ (ext L').card * B) →
      ∑ σ ∈ ext L, Pr{let z ← (runLog C σ comp >>= fun r =>
          K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] ≤ (ext L).card * B := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
    intro L hK
    simp only [runLog_pure, pure_bind, List.append_nil]
    obtain ⟨n, hn⟩ := counted_pure value
    exact hK L value n hn (Nat.le_add_right _ _)
  | query_bind t next ih =>
    intro L hK
    rcases t with coins | publicQuery
    · have unfold : ∀ σ : Perm,
          Pr{let z ← (stepLog C σ (.inl coins) (fun a => runLog C σ (next a)) >>= fun r =>
            K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
          Pr{let z ← ((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
            fun a => (runLog C σ (next a) >>= fun r => K r.1 (L.map Prod.fst ++ r.2) σ))}[q z] :=
        fun σ => by
          show Pr{let z ← (((liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins)) >>=
            fun a => runLog C σ (next a)) >>= fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
          rw [bind_assoc]
      refine (Finset.sum_congr rfl fun σ _ => unfold σ).trans_le ?_
      exact coin_bound _ _ _ q _ fun a => ih a L fun L' c n hn hlen =>
        hK L' c _ (counted_query_support (.inl coins) next a (c, n) hn) (by
          show L'.length ≤ L.length + (Oracle.callCost (.inl coins) + n)
          have zero : Oracle.callCost (.inl coins : World.Domain) = 0 := rfl
          omega)
    · rcases publicQuery with x | permQuery
      · exact ih (C x) L fun L' c n hn hlen =>
          hK L' c _ (counted_query_support (.inr (.inl x)) next (C x) (c, n) hn) (by
            show L'.length ≤ L.length + (Oracle.callCost (.inr (.inl x)) + n)
            have one : Oracle.callCost (.inr (.inl x) : World.Domain) = 1 := rfl
            omega)
      · rcases permQuery with x | y
        · have unfold : ∀ σ : Perm,
              Pr{let z ← (stepLog C σ (.inr (.inr (.inl x))) (fun a => runLog C σ (next a)) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
              Pr{let z ← (runLog C σ (next (σ x)) >>= fun r =>
                K r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q z] :=
            fun σ => by
              show Pr{let z ← (((fun z => (z.1, x :: z.2)) <$> runLog C σ (next (σ x))) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
              rw [bind_map_left]
          refine (Finset.sum_congr rfl fun σ _ => unfold σ).trans_le ?_
          refine (sum_ext_forward L x (fun σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
            K r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q z])).trans_le ?_
          calc ∑ a : PWord, ∑ σ ∈ ext (L ++ [(x, a)]), Pr{let z ← (runLog C σ (next a) >>=
                fun r => K r.1 (L.map Prod.fst ++ x :: r.2) σ)}[q z]
              ≤ ∑ a : PWord, ((ext (L ++ [(x, a)])).card : ℝ≥0∞) * B :=
                Finset.sum_le_sum fun a _ => by
                  have h := ih a (L ++ [(x, a)]) fun L' c n hn hlen =>
                    hK L' c _ (counted_query_support (.inr (.inr (.inl x))) next a (c, n) hn) (by
                      show L'.length ≤ L.length + (Oracle.callCost (.inr (.inr (.inl x))) + n)
                      have one : Oracle.callCost (.inr (.inr (.inl x)) : World.Domain) = 1 := rfl
                      rw [List.length_append, List.length_singleton] at hlen
                      omega)
                  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
                    List.singleton_append] at h
                  exact h
            _ = ((ext L).card : ℝ≥0∞) * B := by rw [← Finset.sum_mul, ← card_ext_forward]
        · have unfold : ∀ σ : Perm,
              Pr{let z ← (stepLog C σ (.inr (.inr (.inr y))) (fun a => runLog C σ (next a)) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] =
              Pr{let z ← (runLog C σ (next (σ.symm y)) >>= fun r =>
                K r.1 (L.map Prod.fst ++ σ.symm y :: r.2) σ)}[q z] :=
            fun σ => by
              show Pr{let z ← (((fun z => (z.1, σ.symm y :: z.2)) <$>
                runLog C σ (next (σ.symm y))) >>=
                fun r => K r.1 (L.map Prod.fst ++ r.2) σ)}[q z] = _
              rw [bind_map_left]
          refine (Finset.sum_congr rfl fun σ _ => unfold σ).trans_le ?_
          refine (sum_ext_inverse L y (fun σ a => Pr{let z ← (runLog C σ (next a) >>= fun r =>
            K r.1 (L.map Prod.fst ++ a :: r.2) σ)}[q z])).trans_le ?_
          calc ∑ a : PWord, ∑ σ ∈ ext (L ++ [(a, y)]), Pr{let z ← (runLog C σ (next a) >>=
                fun r => K r.1 (L.map Prod.fst ++ a :: r.2) σ)}[q z]
              ≤ ∑ a : PWord, ((ext (L ++ [(a, y)])).card : ℝ≥0∞) * B :=
                Finset.sum_le_sum fun a _ => by
                  have h := ih a (L ++ [(a, y)]) fun L' c n hn hlen =>
                    hK L' c _ (counted_query_support (.inr (.inr (.inr y))) next a (c, n) hn) (by
                      show L'.length ≤ L.length + (Oracle.callCost (.inr (.inr (.inr y))) + n)
                      have one : Oracle.callCost (.inr (.inr (.inr y)) : World.Domain) = 1 := rfl
                      rw [List.length_append, List.length_singleton] at hlen
                      omega)
                  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
                    List.singleton_append] at h
                  exact h
            _ = ((ext L).card : ℝ≥0∞) * B := by rw [← Finset.sum_mul, ← card_ext_inverse]

theorem pre_swap {D : Type} (pre : PWord → D) (y y' z : PWord) (h : pre y = pre y') :
    pre (Equiv.swap y y' z) = pre z := by
  by_cases hz : z = y
  · rw [hz, Equiv.swap_apply_left, h]
  · by_cases hz' : z = y'
    · rw [hz', Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hz hz']

namespace SaltLayout
variable {Ch Pos U : Type} [DecidableEq Pos] (SL : SaltLayout Ch Pos U)

theorem wpt_congr (c : Ch) (s : Pos → U) {σ σ' : Perm}
    (h : ∀ b j, σ (SL.X c b j) = σ' (SL.X c b j)) (b : Bool) :
    wpt SL.toLeaf c s σ b = wpt SL.toLeaf c s σ' b :=
  funext fun j => by rw [wpt_toLeaf, wpt_toLeaf, h b j]

theorem uset_congr (c : Ch) (p : (Pos → U) × (Pos → U)) {σ σ' : Perm}
    (h : ∀ b j, σ (SL.X c b j) = σ' (SL.X c b j)) : SL.uset c p σ = SL.uset c p σ' := by
  unfold uset sset swapPts
  simp only [SL.wpt_congr c _ h]

theorem w0set_congr (c : Ch) (s : Pos → U) {σ σ' : Perm}
    (h : ∀ b j, σ (SL.X c b j) = σ' (SL.X c b j)) : SL.w0set c s σ = SL.w0set c s σ' := by
  unfold w0set
  rw [SL.wpt_congr c s h]

theorem w0set_sub (c : Ch) (p : (Pos → U) × (Pos → U)) (σ : Perm) :
    SL.w0set c p.1 σ ⊆ SL.uset c p σ := fun x hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem tag_w0set (c : Ch) (s : Pos → U) (σ : Perm) (h : PWord) (hh : h ∈ SL.w0set c s σ) :
    SL.tag h ≠ none := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
  rw [wpt_toLeaf, SL.tag_W]
  exact Option.some_ne_none j

theorem viewF_swap {D V : Type} (pre : PWord → D) (F : Ch → (Pos → U) → (Pos → PWord) → V)
    (hFpre : ∀ c s o o', (∀ j, pre (o j) = pre (o' j)) → F c s o = F c s o')
    (c : Ch) (s : Pos → U) (σ : Perm) (y y' : PWord) (hpre : pre y = pre y')
    (hX : ∀ b j, Equiv.swap y y' (σ (SL.X c b j)) = σ (SL.X c b j)) :
    SL.viewF F c s (Equiv.swap y y' * σ) = SL.viewF F c s σ := by
  unfold viewF
  have hw : wpt SL.toLeaf c s (Equiv.swap y y' * σ) false = wpt SL.toLeaf c s σ false :=
    SL.wpt_congr c s (fun b j => by rw [Equiv.Perm.mul_apply, hX b j]) false
  rw [hw]
  refine hFpre c s _ _ fun j => ?_
  rw [Equiv.Perm.mul_apply, pre_swap pre y y' _ hpre]

/-- **Range hit over one stage-one log and salt pair.** -/
theorem rh_class_bound [Fintype Pos] {D V β : Type} [DecidableEq D] (pre : PWord → D) (N : ℕ)
    (hN : ∀ d, N ≤ (Finset.univ.filter fun y => pre y = d).card)
    (F : Ch → (Pos → U) → (Pos → PWord) → V)
    (hFpre : ∀ c s o o', (∀ j, pre (o j) = pre (o' j)) → F c s o = F c s o')
    (C : Compression) (A₂ : Ch → V → OracleComp World β) (c : Ch)
    (p : (Pos → U) × (Pos → U)) (L : PLog) (T q P : ℕ)
    (hq : ∀ v, PublicQueryBound (A₂ c v) q) (hlen : L.length + q ≤ T)
    (hP : Fintype.card Pos ≤ P) (hM : 2 * P + 2 * T < N) :
    ∑ σ ∈ ext L, Pr{let r ← runCut C (SL.uset c p σ) σ (A₂ c (SL.viewF F c p.1 σ))}[
        SL.RH c p σ (L.map Prod.fst) r] ≤
      (ext L).card * (q * ((P : ℝ≥0∞) / ((N - 2 * P - 2 * T : ℕ) : ℝ≥0∞))) := by
  classical
  set l := L.map Prod.fst with hl
  set ε : ℝ≥0∞ := (P : ℝ≥0∞) / ((N - 2 * P - 2 * T : ℕ) : ℝ≥0∞) with hε
  let g : Perm → (Bool → Pos → PWord) × V := fun σ =>
    ((fun b j => σ (SL.X c b j)), SL.viewF F c p.1 σ)
  have maps : ∀ σ ∈ ext L, g σ ∈ (ext L).image g := fun σ hσ => Finset.mem_image_of_mem g hσ
  rw [← Finset.sum_fiberwise_of_maps_to maps,
    Finset.card_eq_sum_card_fiberwise maps, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun g₀ hg₀ => ?_
  obtain ⟨σ₀, hσ₀, rfl⟩ := Finset.mem_image.mp hg₀
  set K := (ext L).filter (fun σ => g σ = g σ₀) with hK
  have hX : ∀ σ ∈ K, ∀ b j, σ (SL.X c b j) = σ₀ (SL.X c b j) := fun σ hσ b j =>
    congrFun (congrFun (Prod.mk.inj (Finset.mem_filter.mp hσ).2).1 b) j
  have hV : ∀ σ ∈ K, SL.viewF F c p.1 σ = SL.viewF F c p.1 σ₀ := fun σ hσ =>
    (Prod.mk.inj (Finset.mem_filter.mp hσ).2).2
  have hKL : ∀ σ ∈ K, σ ∈ ext L := fun σ hσ => (Finset.mem_filter.mp hσ).1
  set U₀ := SL.uset c p σ₀ with hU₀
  set H₀ := SL.w0set c p.1 σ₀ with hH₀
  have same : ∀ σ ∈ K,
      Pr{let r ← runCut C (SL.uset c p σ) σ (A₂ c (SL.viewF F c p.1 σ))}[SL.RH c p σ l r] =
        Pr{let r ← runCut C U₀ σ (A₂ c (SL.viewF F c p.1 σ₀))}[
          Clean U₀ l ∧ ∃ x, r = .inr (x, true) ∧ x ∈ H₀] := by
    intro σ hσ
    unfold RH
    rw [SL.uset_congr c p (hX σ hσ), SL.w0set_congr c p.1 (hX σ hσ), hV σ hσ]
  rw [Finset.sum_congr rfl same]
  by_cases clean : Clean U₀ l
  · have extKK : extK K L = K := by
      ext σ
      rw [mem_extK]
      exact ⟨fun h => h.1, fun h => ⟨h, hKL σ h⟩⟩
    set A : Finset PWord := (Finset.univ.image fun bj : Bool × Pos => σ₀ (SL.X c bj.1 bj.2)) ∪
      (L.map Prod.snd).toFinset with hA
    have hAcard : A.card ≤ 2 * P + T := by
      rw [hA]
      have h1 := Finset.card_union_le (Finset.univ.image fun bj : Bool × Pos =>
        σ₀ (SL.X c bj.1 bj.2)) (L.map Prod.snd).toFinset
      have h2 : (Finset.univ.image fun bj : Bool × Pos => σ₀ (SL.X c bj.1 bj.2)).card ≤
          2 * P := by
        refine (Finset.card_image_le).trans ?_
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
        omega
      have h3 : (L.map Prod.snd).toFinset.card ≤ L.length := by
        have := List.toFinset_card_le (L.map Prod.snd)
        rwa [List.length_map] at this
      omega
    have hHcard : H₀.card ≤ P := by
      rw [hH₀]
      unfold w0set
      refine (Finset.card_image_le).trans ((Finset.card_le_univ _).trans hP)
    have hclosed : ∀ σ ∈ K, ∀ y y', pre y = pre y' → y ∉ A → y' ∉ A →
        Equiv.swap y y' * σ ∈ K := by
      intro σ hσ y y' hpre hy hy'
      have fixA : ∀ z ∈ A, Equiv.swap y y' z = z := fun z hz =>
        Equiv.swap_apply_of_ne_of_ne (fun h => hy (h ▸ hz)) (fun h => hy' (h ▸ hz))
      have fixX : ∀ b j, Equiv.swap y y' (σ (SL.X c b j)) = σ (SL.X c b j) := by
        intro b j
        rw [hX σ hσ b j]
        exact fixA _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(b, j), Finset.mem_univ _, rfl⟩))
      refine Finset.mem_filter.mpr ⟨mem_ext.mpr fun e he => ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, mem_ext.mp (hKL σ hσ) e he]
        exact fixA _ (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem he)))
      · show ((fun b j => (Equiv.swap y y' * σ) (SL.X c b j)),
            SL.viewF F c p.1 (Equiv.swap y y' * σ)) = g σ₀
        rw [SL.viewF_swap pre F hFpre c p.1 σ y y' hpre fixX]
        rw [← (Finset.mem_filter.mp hσ).2]
        refine Prod.ext (funext fun b => funext fun j => ?_) rfl
        show (Equiv.swap y y' * σ) (SL.X c b j) = σ (SL.X c b j)
        rw [Equiv.Perm.mul_apply]
        exact fixX b j
    have hAH : ∀ σ ∈ K, ∀ h ∈ H₀, σ h ∉ A := by
      intro σ hσ h hh hA'
      rcases Finset.mem_union.mp hA' with hx | hx
      · obtain ⟨bj, _, hbj⟩ := Finset.mem_image.mp hx
        rw [← hX σ hσ bj.1 bj.2] at hbj
        have := σ.injective hbj
        have tagX := SL.tag_X c bj.1 bj.2
        rw [this] at tagX
        exact SL.tag_w0set c p.1 σ₀ h hh tagX
      · obtain ⟨e, he, he2⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
        have h1 : σ e.1 = e.2 := mem_ext.mp (hKL σ hσ) e he
        have heq : e.1 = h := σ.injective (h1.trans he2)
        exact clean e.1 (List.mem_map_of_mem he) (SL.w0set_sub c p σ₀ (by rw [heq]; exact hh))
    have hfib : ∀ L' : PLog, Clean U₀ (L'.map Prod.fst) → L'.length < T → ∀ y,
        (∀ e ∈ L', e.2 ≠ y) →
        (((extK K L').filter fun σ => σ.symm y ∈ H₀).card : ℝ≥0∞) ≤ ε * (extK K L').card := by
      intro L' _ hL' y fresh
      have nat := fibre_hazard pre N hN K A H₀ hclosed hAH L' y fresh
      have M0 : 0 < N - 2 * P - 2 * T := by omega
      have hsum : A.card + L'.length ≤ 2 * P + 2 * T := by
        have := Nat.add_le_add hAcard hL'.le
        omega
      have nat2 : ((extK K L').filter fun σ => σ.symm y ∈ H₀).card * (N - 2 * P - 2 * T) ≤
          P * (extK K L').card := by
        calc ((extK K L').filter fun σ => σ.symm y ∈ H₀).card * (N - 2 * P - 2 * T)
            ≤ ((extK K L').filter fun σ => σ.symm y ∈ H₀).card * (N - A.card - L'.length) :=
              Nat.mul_le_mul_left _ (by
                rw [Nat.sub_sub, Nat.sub_sub]
                exact Nat.sub_le_sub_left hsum N)
          _ ≤ H₀.card * (extK K L').card := nat
          _ ≤ P * (extK K L').card := Nat.mul_le_mul_right _ hHcard
      have Mne : ((N - 2 * P - 2 * T : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast M0.ne'
      have Mtop : ((N - 2 * P - 2 * T : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [hε, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
        ENNReal.le_div_iff_mul_le (Or.inl Mne) (Or.inl Mtop)]
      exact_mod_cast nat2
    calc ∑ σ ∈ K, Pr{let r ← runCut C U₀ σ (A₂ c (SL.viewF F c p.1 σ₀))}[
            Clean U₀ l ∧ ∃ x, r = .inr (x, true) ∧ x ∈ H₀]
        ≤ ∑ σ ∈ extK K L, Pr{let r ← runCut C U₀ σ (A₂ c (SL.viewF F c p.1 σ₀))}[
            ∃ x, r = .inr (x, true) ∧ x ∈ H₀] := by
          rw [extKK]
          exact Finset.sum_le_sum fun σ _ => prEvent_mono _ _ _ fun r hr => hr.2
      _ ≤ (extK K L).card * (q * ε) :=
          hazard_cut C U₀ H₀ (SL.w0set_sub c p σ₀) K T ε hfib _ q (hq _) L clean hlen
      _ = (K.card : ℝ≥0∞) * (q * ε) := by rw [extKK]
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun σ _ =>
      prEvent_eq_zero_of_forall_not _ _ fun r hr => clean hr.1)) zero_le

end SaltLayout


theorem salt_mass {S : Type} [Fintype S] (salt : ProbComp S) (P₀ : ℝ≥0∞)
    (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀) : P₀ * (Fintype.card S : ℝ≥0∞) = 1 := by
  have h := sum_point_eq_one salt
  simp only [hunif, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [mul_comm]
  exact h

/-- **R3c: the range hit of the whole experiment**, for a view reading hidden leaf outputs only
through a prefix map `pre` whose classes have at least `N` words. -/
theorem rh_whole_bound {St Out Pos U D : Type} {k : Nat} [Fintype Pos] [DecidableEq Pos]
    [Fintype U] [DecidableEq D] (SL : SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (adversary : Hiding.HidingAdversary St Out k) (t : ℕ)
    (bounded : Hiding.QueryBound adversary t)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (C : Compression)
    (F : Hiding.HidingChallenge St k → (Pos → U) → (Pos → PWord) → Commitment × Proof)
    (pre : PWord → D) (N : ℕ) (hN : ∀ d, N ≤ (Finset.univ.filter fun y => pre y = d).card)
    (hFpre : ∀ c s o o', (∀ j, pre (o j) = pre (o' j)) → F c s o = F c s o')
    (P : ℕ) (hP : Fintype.card Pos ≤ P) (hM : 2 * P + 2 * t < N) :
    Pr{let z ← (SaltLayout.whole C adversary.choose
        (SL.tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) F))}[SL.rh z] ≤
      t * ((P : ℝ≥0∞) / ((N - 2 * P - 2 * t : ℕ) : ℝ≥0∞)) := by
  set ε := (P : ℝ≥0∞) / ((N - 2 * P - 2 * t : ℕ) : ℝ≥0∞) with hε
  unfold SaltLayout.whole
  rw [prEvent_bind_eq_sum_fintype]
  have point : ∀ σ : Perm, Pr{let x ← ($ᵗ Perm : ProbComp Perm)}[x = σ] =
      Pr{let x ← ($ᵗ Perm : ProbComp Perm)}[x = 1] := fun σ => uniform_point_eq σ 1
  simp only [point]
  rw [← Finset.mul_sum]
  have key : ∀ (L' : PLog) (c : Hiding.HidingChallenge St k) (n : ℕ),
      (c, n) ∈ support (Hiding.counted adversary.choose) → L'.length ≤ ([] : PLog).length + n →
      ∑ σ ∈ ext L', Pr{let z ← (SL.tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) F c
        (L'.map Prod.fst) σ)}[SL.rh z] ≤ (ext L').card * (t * ε) := by
    intro L' c n hn hlen
    have first : n ≤ t := (bounded (c, n) hn).1
    simp only [List.length_nil, Nat.zero_add] at hlen
    have hq : ∀ v : Commitment × Proof,
        PublicQueryBound ((fun c v => adversary.observe c.aux v.1 v.2) c v) (t - n) := fun v =>
      public_query_bound_of_counted_support _ _ fun last hl => by
        have := (bounded (c, n) hn).2 v.1 v.2 last hl
        omega
    unfold SaltLayout.tcut
    simp only [pair_sum salt P₀ hunif, prEvent_map]
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine (mul_le_mul_right (Finset.sum_le_sum (g := fun _ => ((ext L').card : ℝ≥0∞) *
      (((t - n : ℕ) : ℝ≥0∞) * ε)) fun p _ => ?_) _).trans ?_
    · simp only [SaltLayout.rh, Prod.mk.eta]
      exact SL.rh_class_bound pre N hN F hFpre C (fun c v => adversary.observe c.aux v.1 v.2) c p
        L' t (t - n) P hq (by omega) hP hM
    · have hmass := salt_mass salt P₀ hunif
      calc P₀ * P₀ * ∑ _p : (Pos → U) × (Pos → U),
            ((ext L').card : ℝ≥0∞) * (((t - n : ℕ) : ℝ≥0∞) * ε)
          = P₀ * P₀ * ((Fintype.card ((Pos → U) × (Pos → U)) : ℝ≥0∞) *
            (((ext L').card : ℝ≥0∞) * (((t - n : ℕ) : ℝ≥0∞) * ε))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = (P₀ * (Fintype.card (Pos → U) : ℝ≥0∞)) * (P₀ * (Fintype.card (Pos → U) : ℝ≥0∞)) *
            (((ext L').card : ℝ≥0∞) * (((t - n : ℕ) : ℝ≥0∞) * ε)) := by
            rw [Fintype.card_prod]
            push_cast
            ring
        _ = ((ext L').card : ℝ≥0∞) * (((t - n : ℕ) : ℝ≥0∞) * ε) := by
            rw [hmass, one_mul, one_mul]
        _ ≤ ((ext L').card : ℝ≥0∞) * (t * ε) :=
            mul_le_mul_right (mul_le_mul_left (by exact_mod_cast Nat.sub_le t n) _) _
  have h := stage_one_bound C adversary.choose
    (SL.tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) F) SL.rh (t * ε) [] key
  rw [ext_nil] at h
  simp only [List.map_nil, List.nil_append] at h
  have mass : Pr{let x ← ($ᵗ Perm : ProbComp Perm)}[x = 1] *
      ((Finset.univ : Finset Perm).card : ℝ≥0∞) = 1 := by
    rw [Finset.card_univ]
    exact salt_mass _ _ point
  calc _ ≤ Pr{let x ← ($ᵗ Perm : ProbComp Perm)}[x = 1] *
        (((Finset.univ : Finset Perm).card : ℝ≥0∞) * (t * ε)) := mul_le_mul_right h _
    _ = (Pr{let x ← ($ᵗ Perm : ProbComp Perm)}[x = 1] *
        ((Finset.univ : Finset Perm).card : ℝ≥0∞)) * (t * ε) := (mul_assoc _ _ _).symm
    _ = t * ε := by rw [mass, one_mul]

/-- **R3c with the contract's numbers**: 128-bit salts, at most `2^24` positions, prefix classes
of at least `2^1344` words. -/
theorem rh_le {St Out Pos U D : Type} {k : Nat} [Fintype Pos] [DecidableEq Pos]
    [Fintype U] [DecidableEq D] (SL : SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (adversary : Hiding.HidingAdversary St Out k) (t : ℕ)
    (bounded : Hiding.QueryBound adversary t)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (C : Compression)
    (F : Hiding.HidingChallenge St k → (Pos → U) → (Pos → PWord) → Commitment × Proof)
    (pre : PWord → D) (hN : ∀ d, 2 ^ 1344 ≤ (Finset.univ.filter fun y => pre y = d).card)
    (hFpre : ∀ c s o o', (∀ j, pre (o j) = pre (o' j)) → F c s o = F c s o')
    (hPos : Fintype.card Pos ≤ 2 ^ 24) (hU : Fintype.card U = 2 ^ 128) :
    Pr{let z ← (SaltLayout.whole C adversary.choose
        (SL.tcut C salt (fun c v => adversary.observe c.aux v.1 v.2) F))}[SL.rh z] ≤
      t * (Fintype.card U : ℝ≥0∞)⁻¹ := by
  rw [hU]
  have two : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  have twoTop : ((2 ^ 128 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  by_cases ht : 2 ^ 128 ≤ t
  · calc _ ≤ (1 : ℝ≥0∞) := prEvent_le_one _
      _ ≤ (t : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl two) (Or.inl twoTop), one_mul]
          exact_mod_cast ht
  · have ht := Nat.lt_of_not_le ht
    have big : 2 ^ 24 * 2 ^ 128 + 2 * 2 ^ 24 + 2 * 2 ^ 128 ≤ 2 ^ 1344 :=
      (show 2 ^ 24 * 2 ^ 128 + 2 * 2 ^ 24 + 2 * 2 ^ 128 ≤ 2 ^ 153 by norm_num).trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    have hM : 2 * 2 ^ 24 + 2 * t < 2 ^ 1344 := by omega
    refine (rh_whole_bound SL adversary t bounded salt P₀ hunif C F pre (2 ^ 1344) hN hFpre
      (2 ^ 24) hPos hM).trans ?_
    refine mul_le_mul_right ?_ _
    have hPM : 2 ^ 24 * 2 ^ 128 ≤ 2 ^ 1344 - 2 * 2 ^ 24 - 2 * t := by omega
    refine ENNReal.div_le_of_le_mul ?_
    calc ((2 ^ 24 : ℕ) : ℝ≥0∞)
        = ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((2 ^ 24 * 2 ^ 128 : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_mul (2 ^ 24) (2 ^ 128), mul_comm (((2 ^ 24 : ℕ)) : ℝ≥0∞), ← mul_assoc,
            ENNReal.inv_mul_cancel two twoTop, one_mul]
      _ ≤ ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ((2 ^ 1344 - 2 * 2 ^ 24 - 2 * t : ℕ) : ℝ≥0∞) :=
          mul_le_mul_right (by exact_mod_cast hPM) _

/-- **The contract's hiding property for a salted two-call leaf scheme, with the range hit
proved.** The only remaining hypotheses are R2: the leaf layouts, uniform 128-bit salts over at
most `2^24` positions, a view `F` that reads salts only off the swap set and hidden leaf outputs
only through a prefix map with classes of at least `2^1344` words, and the refinement `hhonest`. -/
theorem scheme_hiding_R2 (scheme : Scheme) {Pos U D : Type} [Fintype Pos] [DecidableEq Pos]
    [Fintype U] [DecidableEq D] (hU : Fintype.card U = 2 ^ 128) (hPos : Fintype.card Pos ≤ 2 ^ 24)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (SL : ∀ (St : Type) (k : Nat), SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (F : ∀ (St : Type) (k : Nat), Compression → Hiding.HidingChallenge St k → (Pos → U) →
      (Pos → PWord) → Commitment × Proof)
    (hF : ∀ St k C c s s' o, (∀ j, j ∉ (SL St k).swapSet c → s j = s' j) →
      F St k C c s o = F St k C c s' o)
    (pre : PWord → D) (hN : ∀ d, 2 ^ 1344 ≤ (Finset.univ.filter fun y => pre y = d).card)
    (hFpre : ∀ St k C c s o o', (∀ j, pre (o j) = pre (o' j)) → F St k C c s o = F St k C c s o')
    (hhonest : ∀ (St : Type) (k : Nat) (C : Compression) (σ : Perm) (b : Bool)
      (c : Hiding.HidingChallenge St k) (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s =>
          pure (F St k C c s fun j => σ (wpt (SL St k).toLeaf c s σ b j)))}[q v]) :
    scheme.Hiding HIDING_ERROR :=
  scheme_hiding scheme hU salt P₀ hunif SL F hF hhonest
    fun St _ k adversary t bounded C => rh_le (SL St k) adversary t bounded salt P₀ hunif C
      (F St k C) pre hN (hFpre St k C) hPos hU

/-! ## The digest slice: prefix classes of `2^1344` words -/

/-- Exactly `2^(n-w)` words of width `n` have a given `w`-bit slice at offset `off` (the proof is
the one of `PermLean.card_extract_fiber`). -/
theorem slice_fiber_card (n off w : ℕ) (fits : off + w ≤ n) (t : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = t).card = 2 ^ (n - w) := by
  classical
  let mask : BitVec w → BitVec n := fun u => (u.setWidth n) <<< off
  have slice_xor : ∀ (x : BitVec n) (u : BitVec w),
      (x ^^^ mask u).extractLsb' off w = x.extractLsb' off w ^^^ u := by
    intro x u
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h₀ : decide (i < w) = true := decide_eq_true hi
    have a : decide (off + i < n) = true := decide_eq_true (by omega)
    have b : decide (off + i < off) = false := decide_eq_false (by omega)
    have c : decide (i < n) = true := decide_eq_true (by omega)
    simp only [mask, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, Nat.add_sub_cancel_left, h₀, a, b, c, Bool.true_and, Bool.not_false]
  have equal : ∀ t t' : BitVec w,
      (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = t).card =
        (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = t').card := by
    intro t t'
    apply Finset.card_nbij' (fun x => x ^^^ mask (t ^^^ t')) (fun x => x ^^^ mask (t ^^^ t'))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [slice_xor, hx, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [slice_xor, hx, BitVec.xor_comm t t', ← BitVec.xor_assoc, BitVec.xor_self,
        BitVec.zero_xor]
    · intro x _
      show x ^^^ mask (t ^^^ t') ^^^ mask (t ^^^ t') = x
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · intro x _
      show x ^^^ mask (t ^^^ t') ^^^ mask (t ^^^ t') = x
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have total : (Finset.univ : Finset (BitVec n)).card =
      ∑ u ∈ (Finset.univ : Finset (BitVec w)),
        (Finset.univ.filter fun x : BitVec n => x.extractLsb' off w = u).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [Finset.sum_congr rfl (fun u _ => equal u t), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_bitVec, Fintype.card_bitVec, smul_eq_mul] at total
  have split : 2 ^ n = 2 ^ w * 2 ^ (n - w) := by
    rw [← pow_add]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (total.symm.trans split)

/-- The digest of a permutation output: bits `[0, 256)`, i.e. bytes `[0, 32)`. -/
def digestOf (y : PWord) : BitVec 256 := y.extractLsb' 0 256

theorem digest_fiber (d : BitVec 256) :
    2 ^ 1344 ≤ (Finset.univ.filter fun y : PWord => digestOf y = d).card :=
  (slice_fiber_card PERMUTATION_WIDTH 0 256 (by unfold PERMUTATION_WIDTH; omega) d).ge

/-- **The contract's hiding property for a salted two-call leaf scheme whose honest view reads the
hidden second-call outputs through their 32-byte digests only.** Every hypothesis is part of R2:
the leaf layouts `SL` (tags, salts, swap sets), uniform 128-bit salts over at most `2^24`
positions, the view `F` (`hF`: salts of swapped positions unread; `hFdigest`: second-call outputs
read through `digestOf` only), and the machine refinement `hhonest`. -/
theorem scheme_hiding_digest (scheme : Scheme) {Pos U : Type} [Fintype Pos] [DecidableEq Pos]
    [Fintype U] (hU : Fintype.card U = 2 ^ 128) (hPos : Fintype.card Pos ≤ 2 ^ 24)
    (salt : ProbComp (Pos → U)) (P₀ : ℝ≥0∞) (hunif : ∀ s, Pr{let x ← salt}[x = s] = P₀)
    (SL : ∀ (St : Type) (k : Nat), SaltLayout (Hiding.HidingChallenge St k) Pos U)
    (F : ∀ (St : Type) (k : Nat), Compression → Hiding.HidingChallenge St k → (Pos → U) →
      (Pos → PWord) → Commitment × Proof)
    (hF : ∀ St k C c s s' o, (∀ j, j ∉ (SL St k).swapSet c → s j = s' j) →
      F St k C c s o = F St k C c s' o)
    (hFdigest : ∀ St k C c s o o', (∀ j, digestOf (o j) = digestOf (o' j)) →
      F St k C c s o = F St k C c s o')
    (hhonest : ∀ (St : Type) (k : Nat) (C : Compression) (σ : Perm) (b : Bool)
      (c : Hiding.HidingChallenge St k) (q : Commitment × Proof → Prop),
      Pr{let v ← simulateQ (Oracle.world ⟨C, σ⟩) (honest scheme b c)}[q v] =
        Pr{let v ← (salt >>= fun s =>
          pure (F St k C c s fun j => σ (wpt (SL St k).toLeaf c s σ b j)))}[q v]) :
    scheme.Hiding HIDING_ERROR :=
  scheme_hiding_R2 scheme hU hPos salt P₀ hunif SL F hF digestOf digest_fiber hFdigest hhonest

end HSwap
