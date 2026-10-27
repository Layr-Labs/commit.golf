import CommitGolfCandidate.Xof.XofProof.Sampling

/-! A proof-only XOF execution log. Each public query records one 256-bit prefix, even
when the caller requests fewer bits. The extra hidden reads are justified by `Semantics`.
The collision bound counts public requests, independently of their requested output lengths. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx FreeMonoid
abbrev Table := RandomOracleBaseline.Table
abbrev Good := RandomOracleBaseline.Good
abbrev State := Cache × Table

def Valid (s : State) : Prop :=
  (∀ p ∈ s.2, ∀ i, i < DIGEST_BITS → s.1 (p.1,i) = some (p.2.getMsbD i)) ∧
  (∀ x, (∀ p ∈ s.2, p.1 ≠ x) → ∀ i, s.1 (x,i) = none)

def read (x : IdealXof.Input) (n : Nat) : StateT Cache ProbComp (BitVec n) :=
  IdealXof.readBits (fun i => Bits.randomOracle (x,i)) 0 n

def answer : QueryImpl family.spec (StateT State ProbComp) := fun q s => do
  let (v,cache) ← (read q.1 DIGEST_BITS).run s.1
  let (out,cache') ← (read q.1 q.2).run cache
  return (out,(cache',(q.1,v)::s.2))

def impl : QueryImpl family.world (StateT State ProbComp) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := StateT State ProbComp) + answer

def run {α : Type} (c : OracleComp family.world α) (s : State) : ProbComp (α × State) :=
  (simulateQ impl c).run s

lemma answer_valid (q : family.Domain) (s : State) (p : family.spec.Range q × State)
    (hv : Valid s) (hp : p ∈ support ((answer q).run s)) :
    Valid p.2 ∧ p.2.2.length = s.2.length+1 := by
  change p ∈ support (answer q s) at hp
  simp only [answer,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hp
  obtain ⟨a,ha,b,hb,hp⟩ := hp
  subst p
  obtain ⟨hae,hap,hao⟩ := readBits_support q.1 0 DIGEST_BITS s.1 a ha
  obtain ⟨hbe,_,hbo⟩ := readBits_support q.1 0 q.2 a.2 b hb
  refine ⟨⟨?_,?_⟩,rfl⟩
  · intro v hmem i hi
    rcases List.mem_cons.mp hmem with rfl | hmem
    · apply hbe (q.1,i) _
      exact Eq.mp (congrArg (fun j => a.2 (q.1,j) = some (a.1.getMsbD i)) (Nat.zero_add i)) (hap i hi)
    · exact hbe (v.1,i) _ (hae (v.1,i) _ (hv.1 v hmem i hi))
  · intro x hx i
    have hn : x ≠ q.1 := Ne.symm (hx (q.1,a.1) (by simp))
    change b.2 (x,i) = none
    rw [hbo (x,i) hn,hao (x,i) hn]
    exact hv.2 x (fun v hmem => hx v (List.mem_cons_of_mem _ hmem)) i

lemma read_cached (x : IdealXof.Input) (v : BitVec DIGEST_BITS) (s : Cache)
    (hcache : ∀ i, i < DIGEST_BITS → s (x,i) = some (v.getMsbD i))
    (p : BitVec DIGEST_BITS × Cache) (hp : p ∈ support ((read x DIGEST_BITS).run s)) : p.1 = v := by
  obtain ⟨he,hp',_⟩ := readBits_support x 0 DIGEST_BITS s p hp
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have h1 := he (x,i) _ (hcache i hi)
  have h2 := hp' i hi
  have h2' : p.2 (x,i) = some (p.1.getMsbD i) := by
    exact Eq.mp (congrArg (fun j => p.2 (x,j) = some (p.1.getMsbD i)) (Nat.zero_add i)) h2
  exact Option.some.inj (h2'.symm.trans h1)

lemma answer_bad_le (q : family.Domain) (s : State) (hv : Valid s) (hg : Good s.2) :
    Pr[fun p => ¬Good p.2.2 | (answer q).run s] ≤ CompressionBaseline.pL s.2.length := by
  classical
  change Pr[fun p => ¬Good p.2.2 | answer q s] ≤ _
  have he : Pr[fun p => ¬Good p.2.2 | answer q s] =
      Pr[fun a => ¬Good ((q.1,a.1)::s.2) | (read q.1 DIGEST_BITS).run s.1] := by
    unfold answer
    rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro a
    simp only
    rw [probEvent_bind_eq_tsum]
    simp only [probEvent_pure]
    by_cases h : Good ((q.1,a.1)::s.2) <;> simp [h]
  rw [he]
  by_cases hx : ∃ v ∈ s.2, v.1 = q.1
  · obtain ⟨v,hvT,hvx⟩ := hx
    apply le_trans (le_of_eq ?_) (zero_le)
    apply probEvent_eq_zero
    intro a ha hbad
    have hav := read_cached q.1 v.2 s.1 (by
      intro i hi
      exact hvx ▸ hv.1 v hvT i hi) a ha
    apply hbad
    rw [hav,← hvx]
    exact RandomOracleBaseline.good_cons_of_mem hvT hg
  · have hf : ∀ i, s.1 (q.1,i) = none := hv.2 q.1 (by simpa only [not_exists,not_and] using hx)
    have heq := readBits_fresh q.1 0 DIGEST_BITS s.1 (fun i _ _ => hf i)
    have hevent : Pr[fun a => ¬Good ((q.1,a)::s.2) | (read q.1 DIGEST_BITS).run' s.1] =
        Pr[fun a => ¬Good ((q.1,a)::s.2) | $ᵗ CompressionBaseline.Digest] := by
      apply probEvent_congr' (fun _ _ => Iff.rfl)
      exact heq
    rw [StateT.run'_eq,probEvent_map] at hevent
    exact hevent.le.trans (RandomOracleBaseline.fresh_bad_le q.1 s.2 hg)

@[simp] lemma run_pure {α : Type} (a : α) (s : State) : run (pure a) s = pure (a,s) := by simp [run]
lemma run_bind {α β : Type} (c : OracleComp family.world α) (k : α → OracleComp family.world β) (s : State) :
    run (c >>= k) s = run c s >>= fun p => run (k p.1) p.2 := by simp [run]
lemma run_coin {α : Type} (n : Nat) (k : Fin (n+1) → OracleComp family.world α) (s : State) :
    run ((family.world.query (.inl n) : OracleComp family.world _) >>= k) s =
      (unifSpec.query n : ProbComp _) >>= fun u => run (k u) s := by simp [run,impl]
lemma run_query {α : Type} (x : family.Domain) (k : family.spec.Range x → OracleComp family.world α) (s : State) :
    run ((family.world.query (.inr x) : OracleComp family.world _) >>= k) s =
      (answer x).run s >>= fun p => run (k p.1) p.2 := by simp [run,impl]

lemma length_le {α : Type} (c : OracleComp family.world α) (s : State)
    (hv : Valid s) (p : α × State) (hp : p ∈ support (run c s)) : s.2.length ≤ p.2.2.length := by
  induction c using OracleComp.inductionOn generalizing s p with
  | pure a => simp only [run_pure,support_pure,Set.mem_singleton_iff] at hp; subst p; rfl
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [run_coin] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,_,hu⟩ := hp
      exact ih u s hv p hu
    | inr x =>
      rw [run_query] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,hu,hp⟩ := hp
      obtain ⟨hv',hl⟩ := answer_valid x s u hv hu
      have hh := ih u.1 u.2 hv' p hp
      omega

theorem collision_bound {α : Type} (c : OracleComp family.world α) :
    ∀ (s : State) (n : Nat), Valid s → Good s.2 →
      Pr[fun p => ¬Good p.2.2 ∧ p.2.2.length ≤ s.2.length+n | run c s] ≤
        ∑ j ∈ Finset.range n, CompressionBaseline.pL (s.2.length+j) := by
  classical
  induction c using OracleComp.inductionOn with
  | pure a => intro s n hv hg; simp [hg]
  | query_bind t k ih =>
    intro s n hv hg
    cases t with
    | inl m =>
      rw [run_coin]
      exact probEvent_bind_le_of_forall_le fun u _ => ih u s n hv hg
    | inr x =>
      rw [run_query]
      cases n with
      | zero =>
        simp only [Finset.range_zero,Finset.sum_empty,Nat.add_zero]
        apply le_of_eq
        apply probEvent_eq_zero
        intro p hp he
        simp only [support_bind,Set.mem_iUnion] at hp
        obtain ⟨u,hu,hp⟩ := hp
        obtain ⟨hv',hl⟩ := answer_valid x s u hv hu
        have hh := length_le (k u.1) u.2 hv' p hp
        omega
      | succ n =>
        rw [CompressionBaseline.sum_pL_succ]
        apply le_trans (probEvent_bind_le_probEvent_add
          (p := fun a => ¬Good a.2.2)
          (ε := ∑ j ∈ Finset.range n, CompressionBaseline.pL (s.2.length+1+j)) ?_)
        · exact add_le_add (answer_bad_le x s hv hg) le_rfl
        · intro a ha hg'
          obtain ⟨hv',hl⟩ := answer_valid x s a hv ha
          have ht : s.2.length+(n+1) = a.2.2.length+n := by omega
          rw [ht]
          simpa only [hl] using ih a.1 a.2 n hv' (not_not.mp hg')
end CommitGolf.XofBaseline
