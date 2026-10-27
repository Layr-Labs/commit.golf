import CommitGolfCandidate.Xof.RandomOracle
import CommitGolfCandidate.Xof.CompressionProof.Binding

namespace CommitGolf.RandomOracleBaseline
open OracleComp OracleSpec
abbrev Table := List (List Bool × CompressionBaseline.Digest)
def Good (T : Table) : Prop := ∀ p ∈ T, ∀ p' ∈ T, p.2 = p'.2 → p.1 = p'.1

def answer : QueryImpl family.spec (StateT Table ProbComp) := fun x T => do
  let y ← match T.find? (fun p => p.1 == x) with
    | some p => pure p.2
    | none => $ᵗ CompressionBaseline.Digest
  return (y, (x, y) :: T)
def impl : QueryImpl family.world (StateT Table ProbComp) :=
  (fun n => (liftM (unifSpec.query n : ProbComp _) : StateT Table ProbComp _)) + answer

def run {α : Type} (c : OracleComp family.world α) (T : Table) : ProbComp (α × Table) :=
  (simulateQ impl c).run T

@[simp] theorem run_pure {α : Type} (a : α) (T : Table) :
    run (pure a) T = pure (a, T) := by simp [run]

theorem run_coin {α : Type} (n : Nat) (k : Fin (n+1) → OracleComp family.world α) (T : Table) :
    run ((family.world.query (.inl n) : OracleComp family.world _) >>= k) T =
      (unifSpec.query n : ProbComp _) >>= fun u => run (k u) T := by
  simp [run, impl]

theorem run_query {α : Type} (x : List Bool) (k : CompressionBaseline.Digest → OracleComp family.world α) (T : Table) :
    run ((family.world.query (.inr x) : OracleComp family.world _) >>= k) T =
      (match T.find? (fun p => p.1 == x) with
        | some p => pure p.2
        | none => $ᵗ CompressionBaseline.Digest) >>= fun y => run (k y) ((x,y)::T) := by
  simp [run, impl]
  change ((answer x T) >>= _) = _
  cases h : T.find? (fun p => p.1 == x) <;> simp [answer, h]

theorem length_le {α : Type} (c : OracleComp family.world α) (T : Table)
    (p : α × Table) (hp : p ∈ support (run c T)) : T.length ≤ p.2.length := by
  induction c using OracleComp.inductionOn generalizing T with
  | pure a =>
      simp only [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact le_rfl
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [run_coin] at hp
      simp only [support_bind, Set.mem_iUnion] at hp
      obtain ⟨u, _, hu⟩ := hp
      exact ih u T hu
    | inr x =>
      rw [run_query] at hp
      simp only [support_bind, Set.mem_iUnion] at hp
      obtain ⟨u, _, hu⟩ := hp
      have h := ih u ((x,u)::T) hu
      simp only [List.length_cons] at h
      omega

lemma good_cons_of_mem {p : List Bool × CompressionBaseline.Digest} {T : Table}
    (hp : p ∈ T) (hg : Good T) : Good (p::T) := by
  intro a ha b hb
  have ha' : a ∈ T := by rcases List.mem_cons.mp ha with rfl | h <;> assumption
  have hb' : b ∈ T := by rcases List.mem_cons.mp hb with rfl | h <;> assumption
  exact hg a ha' b hb'

lemma bad_cons {x : List Bool} {y : CompressionBaseline.Digest} {T : Table}
    (hg : Good T) (hb : ¬ Good ((x,y)::T)) : ∃ p ∈ T, p.2 = y := by
  simp only [Good, not_forall] at hb
  obtain ⟨a, ha, b, hb, heq, hne⟩ := hb
  rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
  · exact (hne rfl).elim
  · exact ⟨b, hb, heq.symm⟩
  · exact ⟨a, ha, heq⟩
  · exact (hne (hg a ha b hb heq)).elim

lemma fresh_bad_le (x : List Bool) (T : Table) (hg : Good T) :
    Pr[fun y => ¬ Good ((x,y)::T) | $ᵗ CompressionBaseline.Digest] ≤
      CompressionBaseline.pL T.length := by
  classical
  rw [probEvent_uniformSample, CompressionBaseline.pL_def]
  have hc : (Finset.univ.filter fun y => ¬ Good ((x,y)::T)).card ≤ T.length + 1 := by
    calc _ ≤ (T.map Prod.snd).toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨p,hp,he⟩ := bad_cons hg (Finset.mem_filter.mp hy).2
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,he⟩)
      _ ≤ T.length := (List.toFinset_card_le _).trans (by simp)
      _ ≤ T.length + 1 := Nat.le_succ _
  rw [Fintype.card_bitVec]
  exact ENNReal.div_le_div_right (by exact_mod_cast hc) _

theorem collision_bound {α : Type} (c : OracleComp family.world α) :
    ∀ (T : Table) (n : Nat), Good T →
      Pr[fun p => ¬ Good p.2 ∧ p.2.length ≤ T.length + n | run c T] ≤
        ∑ j ∈ Finset.range n, CompressionBaseline.pL (T.length+j) := by
  classical
  induction c using OracleComp.inductionOn with
  | pure a =>
      intro T n hg
      simp [hg]
  | query_bind t k ih =>
      intro T n hg
      cases t with
      | inl m =>
          rw [run_coin]
          exact probEvent_bind_le_of_forall_le fun u _ => ih u T n hg
      | inr x =>
          rw [run_query]
          cases n with
          | zero =>
              simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
              apply le_of_eq
              apply probEvent_eq_zero
              intro p hp he
              simp only [support_bind, Set.mem_iUnion] at hp
              obtain ⟨u, _, hu⟩ := hp
              have h := length_le (k u) ((x,u)::T) p hu
              simp only [List.length_cons] at h
              omega
          | succ n =>
              have hn : T.length + (n+1) = ((x, (0 : CompressionBaseline.Digest))::T).length+n := by simp; omega
              cases hf : T.find? (fun p => p.1 == x) with
              | some p =>
                  simp only [pure_bind]
                  have hm := List.mem_of_find?_eq_some hf
                  have hx : p.1 = x := by simpa using List.find?_some hf
                  subst x
                  have hh := ih p.2 (p::T) n (good_cons_of_mem hm hg)
                  have hthr : T.length + (n+1) = (p::T).length+n := by simp; omega
                  rw [hthr]
                  exact hh.trans (by simpa only [List.length_cons] using CompressionBaseline.sum_pL_mono T.length n)
              | none =>
                  rw [CompressionBaseline.sum_pL_succ]
                  apply le_trans (probEvent_bind_le_probEvent_add
                    (p := fun y => ¬ Good ((x,y)::T)) (ε := ∑ j ∈ Finset.range n, CompressionBaseline.pL (T.length+1+j)) ?_)
                  · exact add_le_add (fresh_bad_le x T hg) le_rfl
                  · intro y _ hy
                    have hthr : T.length + (n+1) = ((x,y)::T).length+n := by simp; omega
                    rw [hthr]
                    simpa only [List.length_cons] using ih y ((x,y)::T) n (not_not.mp hy)

def Agrees (H : family.Realization) (T : Table) : Prop := ∀ p ∈ T, H p.1 = p.2

def fixedAnswer (H : family.Realization) : QueryImpl family.spec (StateT Table ProbComp) :=
  fun x T => pure (H x, (x,H x)::T)

@[simp] theorem fixedAnswer_run (H : family.Realization) (x : List Bool) (T : Table) :
    (fixedAnswer H x).run T = pure (H x, (x,H x)::T) := rfl

def fixedImpl (H : family.Realization) : QueryImpl family.world (StateT Table ProbComp) :=
  (fun n => (liftM (unifSpec.query n : ProbComp _) : StateT Table ProbComp _)) +
  fixedAnswer H
def fixedRun (H : family.Realization) {α : Type}
    (c : OracleComp family.world α) (T : Table) : ProbComp (α × Table) :=
  (simulateQ (fixedImpl H) c).run T

@[simp] theorem fixedRun_pure (H : family.Realization) {α : Type} (a : α) (T : Table) :
    fixedRun H (pure a) T = pure (a,T) := by simp [fixedRun]
theorem fixedRun_coin (H : family.Realization) {α : Type} (n : Nat)
    (k : Fin (n+1) → OracleComp family.world α) (T : Table) :
    fixedRun H ((family.world.query (.inl n) : OracleComp family.world _) >>= k) T =
      (unifSpec.query n : ProbComp _) >>= fun u => fixedRun H (k u) T := by simp [fixedRun, fixedImpl]
theorem fixedRun_query (H : family.Realization) {α : Type} (x : List Bool)
    (k : CompressionBaseline.Digest → OracleComp family.world α) (T : Table) :
    fixedRun H ((family.world.query (.inr x) : OracleComp family.world _) >>= k) T =
      fixedRun H (k (H x)) ((x,H x)::T) := by
  simp [fixedRun, fixedImpl]
  rw [fixedAnswer_run H x T]
  simp

/-- Every lazy execution has a fixed-function explanation agreeing with its entire log. -/
theorem fixed_witness {α : Type} (c : OracleComp family.world α) (T : Table)
    (hc : ∃ H, Agrees H T) (p : α × Table) (hp : p ∈ support (run c T)) :
    ∃ H, Agrees H T ∧ Agrees H p.2 ∧ p ∈ support (fixedRun H c T) := by
  classical
  induction c using OracleComp.inductionOn generalizing T with
  | pure a =>
      simp only [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst p
      obtain ⟨H,hH⟩ := hc
      exact ⟨H,hH,hH, by simp⟩
  | query_bind t k ih =>
      cases t with
      | inl n =>
          rw [run_coin] at hp
          simp only [support_bind, Set.mem_iUnion] at hp
          obtain ⟨u,hu,hp⟩ := hp
          obtain ⟨H,hT,hpT,hp⟩ := ih u T hc hp
          refine ⟨H,hT,hpT,?_⟩
          rw [fixedRun_coin]
          simp only [support_bind, Set.mem_iUnion]
          exact ⟨u,hu,hp⟩
      | inr x =>
          rw [run_query] at hp
          simp only [support_bind, Set.mem_iUnion] at hp
          obtain ⟨u,hu,hp⟩ := hp
          have hnew : ∃ H, Agrees H ((x,u)::T) := by
            obtain ⟨H,hH⟩ := hc
            cases hf : T.find? (fun p => p.1 == x) with
            | some v =>
                simp only [hf, support_pure, Set.mem_singleton_iff] at hu
                have hv := List.mem_of_find?_eq_some hf
                have hx : v.1 = x := by simpa using List.find?_some hf
                refine ⟨H, ?_⟩
                intro a ha
                rcases List.mem_cons.mp ha with rfl | ha
                · simpa [hx, hu] using hH v hv
                · exact hH a ha
            | none =>
                refine ⟨Function.update H x u, ?_⟩
                intro a ha
                rcases List.mem_cons.mp ha with rfl | ha
                · simp
                · have hne : a.1 ≠ x := by
                    have := List.find?_eq_none.mp hf a ha
                    simpa using this
                  simpa [Function.update_of_ne hne] using hH a ha
          obtain ⟨H,hT,hpT,hp⟩ := ih u ((x,u)::T) hnew hp
          have hx : H x = u := hT (x,u) (by simp)
          refine ⟨H,fun a ha => hT a (List.mem_cons_of_mem _ ha),hpT,?_⟩
          rw [fixedRun_query, hx]
          exact hp

def toCache (T : Table) : family.State := fun x => (T.find? (fun p => p.1 == x)).map Prod.snd

lemma toCache_cons (x : List Bool) (y : CompressionBaseline.Digest) (T : Table) :
    toCache ((x,y)::T) = (toCache T).cacheQuery x y := by
  funext z
  by_cases h : z = x
  · subst z; simp [toCache]
  · simp [toCache, QueryCache.cacheQuery_of_ne _ _ h, Ne.symm h]

lemma answer_cache (x : List Bool) (T : Table) :
    (fun p => (p.1, toCache p.2)) <$> answer x T = (family.sharedAnswer x).run (toCache T) := by
  change _ = (RandomOracleFixedOutput.answer DIGEST_BITS x).run (toCache T)
  rw [randomOracle.run_eq]
  cases hf : T.find? (fun p => p.1 == x) with
  | none => simp [answer, toCache, hf, map_eq_bind_pure_comp, toCache_cons]
  | some p =>
      have hc : toCache ((x,p.2)::T) = toCache T := by
        rw [toCache_cons]
        funext z
        by_cases h : z = x
        · subst z; simp [toCache, hf]
        · exact QueryCache.cacheQuery_of_ne _ _ h
      simp [answer, toCache, hf]
      exact hc

lemma run_cache {α : Type} (c : OracleComp family.world α) (T : Table) :
    (fun p => (p.1, toCache p.2)) <$> run c T =
      (simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT family.State ProbComp) +
        family.sharedAnswer) c).run (toCache T) := by
  induction c using OracleComp.inductionOn generalizing T with
  | pure a => simp [run]
  | query_bind t k ih =>
      cases t with
      | inl n =>
          rw [run_coin]
          simp only [map_bind]
          simp [simulateQ_bind, StateT.run_bind]
          exact bind_congr fun u => ih u T
      | inr x =>
          simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
            StateT.run_bind]
          rw [← answer_cache]
          simp only [bind_map_left]
          change (fun p => (p.1,toCache p.2)) <$> (answer x T >>= fun p => run (k p.1) p.2) = _
          rw [map_bind]
          exact bind_congr fun p => ih p.1 p.2
end CommitGolf.RandomOracleBaseline



