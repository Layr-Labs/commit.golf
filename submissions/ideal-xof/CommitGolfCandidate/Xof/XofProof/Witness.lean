import CommitGolfCandidate.Xof.XofProof.Lazy

/-! Every supported cached XOF execution can be explained by one fixed collection of
bit streams. This connects lazy sampling to the deterministic Merkle collision argument. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def Agrees (H : family.Realization) (s : Cache) : Prop :=
  ∀ x i b, s (x,i) = some b → H x i = b

def digest (H : family.Realization) (x : IdealXof.Input) : BitVec DIGEST_BITS :=
  IdealXof.eval H (x,DIGEST_BITS)

def fixedAnswer (H : family.Realization) : QueryImpl family.spec (StateT Table ProbComp) :=
  fun q T => pure (IdealXof.eval H q, (q.1,digest H q.1)::T)
@[simp] lemma fixedAnswer_run (H : family.Realization) (q : family.Domain) (T : Table) :
    (fixedAnswer H q).run T = pure (IdealXof.eval H q,(q.1,digest H q.1)::T) := rfl
def fixedImpl (H : family.Realization) : QueryImpl family.world (StateT Table ProbComp) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := StateT Table ProbComp) + fixedAnswer H
def fixedRun (H : family.Realization) {α : Type}
    (c : OracleComp family.world α) (T : Table) : ProbComp (α × Table) :=
  (simulateQ (fixedImpl H) c).run T
@[simp] lemma fixedRun_pure (H : family.Realization) {α : Type} (a : α) (T : Table) :
    fixedRun H (pure a) T = pure (a,T) := by simp [fixedRun]
lemma fixedRun_bind (H : family.Realization) {α β : Type}
    (c : OracleComp family.world α) (k : α → OracleComp family.world β) (T : Table) :
    fixedRun H (c >>= k) T = fixedRun H c T >>= fun p => fixedRun H (k p.1) p.2 := by simp [fixedRun]
lemma fixedRun_coin (H : family.Realization) {α : Type} (n : Nat)
    (k : Fin (n+1) → OracleComp family.world α) (T : Table) :
    fixedRun H ((family.world.query (.inl n) : OracleComp family.world _) >>= k) T =
      (unifSpec.query n : ProbComp _) >>= fun u => fixedRun H (k u) T := by simp [fixedRun,fixedImpl]
lemma fixedRun_query (H : family.Realization) {α : Type} (x : family.Domain)
    (k : family.spec.Range x → OracleComp family.world α) (T : Table) :
    fixedRun H ((family.world.query (.inr x) : OracleComp family.world _) >>= k) T =
      fixedRun H (k (IdealXof.eval H x)) ((x.1,digest H x.1)::T) := by
  simp [fixedRun,fixedImpl]
  rw [fixedAnswer_run]
  simp

lemma read_fixed (H : family.Realization) (x : IdealXof.Input) (n : Nat) (s : Cache)
    (p : BitVec n × Cache) (hp : p ∈ support ((read x n).run s)) (h : Agrees H p.2) :
    p.1 = IdealXof.eval H (x,n) := by
  obtain ⟨_,hr,_⟩ := readBits_support x 0 n s p hp
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have he := h x (0+i) _ (hr i hi)
  have hh := IdealXof.readBits_getMsbD (H x) 0 n i hi
  exact he.symm.trans hh.symm

lemma answer_extends (q : family.Domain) (s : State) (p : family.spec.Range q × State)
    (hp : p ∈ support ((answer q).run s)) : Extends s.1 p.2.1 := by
  simp only [answer,StateT.run,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hp
  obtain ⟨a,ha,b,hb,rfl⟩ := hp
  have ha' := (readBits_support q.1 0 DIGEST_BITS s.1 a ha).1
  have hb' := (readBits_support q.1 0 q.2 a.2 b hb).1
  exact fun x v hx => hb' x v (ha' x v hx)

lemma answer_fixed (H : family.Realization) (q : family.Domain) (s : State)
    (p : family.spec.Range q × State) (hp : p ∈ support ((answer q).run s))
    (h : Agrees H p.2.1) : p.1 = IdealXof.eval H q ∧ p.2.2 = (q.1,digest H q.1)::s.2 := by
  simp only [answer,StateT.run,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hp
  obtain ⟨a,ha,b,hb,rfl⟩ := hp
  have hb' := (readBits_support q.1 0 q.2 a.2 b hb).1
  have haH : Agrees H a.2 := fun x i v hx => h x i v (hb' (x,i) v hx)
  have av := read_fixed H q.1 DIGEST_BITS s.1 a ha haH
  have bv := read_fixed H q.1 q.2 a.2 b hb h
  exact ⟨bv,by change (q.1,a.1)::s.2 = _; rw [av]; rfl⟩

lemma run_extends {α : Type} (c : OracleComp family.world α) (s : State) (p : α × State)
    (hp : p ∈ support (run c s)) : Extends s.1 p.2.1 := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a => simp only [run_pure,support_pure,Set.mem_singleton_iff] at hp; subst p; exact fun _ _ h => h
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [run_coin] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,_,hu⟩ := hp
      exact ih u s hu
    | inr q =>
      rw [run_query] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,hu,hp⟩ := hp
      have h1 := answer_extends q s u hu
      have h2 := ih u.1 u.2 hp
      exact fun x b hx => h2 x b (h1 x b hx)

lemma run_fixed_support {α : Type} (c : OracleComp family.world α) (s : State) (p : α × State)
    (hp : p ∈ support (run c s)) (H : family.Realization) (h : Agrees H p.2.1) :
    (p.1,p.2.2) ∈ support (fixedRun H c s.2) := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a => simp only [run_pure,support_pure,Set.mem_singleton_iff] at hp; subst p; simp
  | query_bind q k ih =>
    cases q with
    | inl n =>
      rw [run_coin] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,hu,hp⟩ := hp
      rw [fixedRun_coin]
      simp only [support_bind,Set.mem_iUnion]
      exact ⟨u,hu,ih u s hp⟩
    | inr q =>
      rw [run_query] at hp
      simp only [support_bind,Set.mem_iUnion] at hp
      obtain ⟨u,hu,hp⟩ := hp
      have he := run_extends (k u.1) u.2 p hp
      have hH : Agrees H u.2.1 := fun x i b hx => h x i b (he (x,i) b hx)
      obtain ⟨hval,hlog⟩ := answer_fixed H q s u hu hH
      rw [fixedRun_query]
      have hh := ih u.1 u.2 hp
      simpa only [hval,hlog] using hh

lemma fixed_witness {α : Type} (c : OracleComp family.world α) (s : State) (p : α × State)
    (hp : p ∈ support (run c s)) :
    ∃ H, (p.1,p.2.2) ∈ support (fixedRun H c s.2) := by
  let H : family.Realization := fun x i => (p.2.1 (x,i)).getD false
  have ha : Agrees H p.2.1 := by intro x i b hb; simp [H,hb]
  exact ⟨H,run_fixed_support c s p hp H ha⟩
end CommitGolf.XofBaseline
