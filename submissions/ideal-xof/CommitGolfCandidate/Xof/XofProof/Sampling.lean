import CommitGolfCandidate.Xof.RandomOracleProof.Certificate
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-! XOF bit sampling and deferred sampling. Reading and discarding a prefix preserves the
distribution of every later observation; a fresh 256-bit prefix is uniform. -/

namespace CommitGolf.XofBaseline
open OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
abbrev Bits := IdealXof.BitSpec
abbrev Cache := IdealXof.Cache
abbrev BitWorld := unifSpec + Bits
abbrev bitImpl : QueryImpl BitWorld (StateT Cache ProbComp) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := StateT Cache ProbComp) + Bits.randomOracle

def bitRun {α : Type} (c : OracleComp BitWorld α) (s : Cache) : ProbComp α :=
  (simulateQ bitImpl c).run' s

lemma cache_comm (s : Cache) (x y : Bits.Domain) (a b : Bool) (h : x ≠ y) :
    (s.cacheQuery x a).cacheQuery y b = (s.cacheQuery y b).cacheQuery x a := by
  funext z
  by_cases hx : z = x
  · subst z; simp [QueryCache.cacheQuery_of_ne _ _ h]
  · by_cases hy : z = y
    · subst z; simp [QueryCache.cacheQuery_of_ne _ _ (Ne.symm h)]
    · simp [QueryCache.cacheQuery_of_ne _ _ hx,QueryCache.cacheQuery_of_ne _ _ hy]

lemma bit_comm {α : Type} (x y : Bits.Domain) (s : Cache)
    (k : Bool → Bool → StateT Cache ProbComp α) :
    𝒮[(do let a ← Bits.randomOracle x; let b ← Bits.randomOracle y; k a b).run s] =
    𝒮[(do let b ← Bits.randomOracle y; let a ← Bits.randomOracle x; k a b).run s] := by
  by_cases h : x = y
  · subst y
    simp only [StateT.run_bind,randomOracle.run_eq]
    cases hs : s x with
    | none => simp [QueryCache.cacheQuery_self]
    | some a => simp [hs]
  · simp only [StateT.run_bind,randomOracle.run_eq]
    cases hx : s x <;> cases hy : s y
    · simp only [hx,hy,bind_assoc,pure_bind,QueryCache.cacheQuery_of_ne _ _ h,
        QueryCache.cacheQuery_of_ne _ _ (Ne.symm h)]
      rw [evalSPMF_bind_comm]
      apply evalSPMF_bind_congr_left
      intro b
      apply evalSPMF_bind_congr_left
      intro a
      rw [cache_comm s x y a b h]
    · simp [hx,hy,QueryCache.cacheQuery_of_ne _ _ (Ne.symm h)]
    · simp [hx,hy,QueryCache.cacheQuery_of_ne _ _ h]
    · simp [hx,hy]

lemma bit_comm_out {α : Type} (x y : Bits.Domain) (s : Cache)
    (k : Bool → Bool → StateT Cache ProbComp α) :
    𝒮[(do let a ← Bits.randomOracle x; let b ← Bits.randomOracle y; k a b).run' s] =
    𝒮[(do let b ← Bits.randomOracle y; let a ← Bits.randomOracle x; k a b).run' s] := by
  simpa only [StateT.run'_eq,evalSPMF_map] using congrArg (fun d : SPMF (α × Cache) => Prod.fst <$> d) (bit_comm x y s k)

lemma forget_bit {α : Type} (c : OracleComp BitWorld α) (x : Bits.Domain) (s : Cache) :
    𝒮[(Bits.randomOracle x >>= fun _ => simulateQ bitImpl c).run' s] = 𝒮[bitRun c s] := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure,StateT.run'_eq,StateT.run_bind,StateT.run_pure,map_bind,map_pure]
    change 𝒮[(Bits.randomOracle x).run s >>= fun _ => pure a] = 𝒮[pure a]
    exact evalSPMF_bind_const_neverFails _ (by simp) _
  | query_bind q k ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
      simp only [bitRun,simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inl]
      simp only [StateT.run'_eq,StateT.run_bind,map_bind]
      simp only [randomOracle.run_eq]
      cases hx : s x with
      | some b =>
        simp only [pure_bind]
      | none =>
        simp only [bind_assoc,pure_bind]
        change 𝒮[($ᵗ Bool) >>= fun b => (unifSpec.query n : ProbComp _) >>= fun u =>
            bitRun (k u) (s.cacheQuery x b)] =
          𝒮[(unifSpec.query n : ProbComp _) >>= fun u => bitRun (k u) s]
        rw [evalSPMF_bind_comm]
        apply evalSPMF_bind_congr_left
        intro u
        have h := ih u s
        simpa only [bitRun,StateT.run'_eq,StateT.run_bind,map_bind,randomOracle.run_eq,hx,
          bind_assoc,pure_bind] using h
    | inr y =>
      simp only [simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr]
      apply (bit_comm_out x y s (fun _ b => simulateQ bitImpl (k b))).trans
      simp only [bitRun,simulateQ_bind,simulateQ_spec_query,QueryImpl.add_apply_inr,
        StateT.run'_eq,StateT.run_bind,map_bind]
      apply evalSPMF_bind_congr_left
      intro p
      simpa only [bitRun,StateT.run'_eq,StateT.run_bind,map_bind] using ih p.1 p.2

lemma forget_program {α β : Type} (d : OracleComp BitWorld β) (c : OracleComp BitWorld α)
    (s : Cache) : 𝒮[bitRun (d >>= fun _ => c) s] = 𝒮[bitRun c s] := by
  induction d using OracleComp.inductionOn generalizing s with
  | pure b => simp
  | query_bind q k ih =>
    simp only [bind_assoc,bitRun,simulateQ_bind,simulateQ_spec_query,
      StateT.run'_eq,StateT.run_bind,map_bind]
    trans 𝒮[(bitImpl q).run s >>= fun p => bitRun c p.2]
    · apply evalSPMF_bind_congr_left
      intro p
      simpa only [bitRun,simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind] using ih p.1 p.2
    · cases q with
      | inl n =>
        change 𝒮[(unifSpec.query n : ProbComp _) >>= fun _ => bitRun c s] = _
        exact evalSPMF_bind_const_neverFails _ (by simp) _
      | inr x =>
        have h := forget_bit c x s
        simp only [bitRun,StateT.run'_eq,StateT.run_bind,map_bind] at h
        convert h using 1
        rfl

def expand : QueryImpl family.world (OracleComp BitWorld)
  | .inl n => (BitWorld.query (.inl n) :)
  | .inr q => IdealXof.readBits (fun i => (BitWorld.query (.inr (q.1,i)) : OracleComp BitWorld Bool)) 0 q.2

def fillPrefix (x : IdealXof.Input) : OracleComp BitWorld (BitVec DIGEST_BITS) :=
  IdealXof.readBits (fun i => (BitWorld.query (.inr (x,i)) : OracleComp BitWorld Bool)) 0 DIGEST_BITS

def paddedExpand : QueryImpl family.world (OracleComp BitWorld)
  | .inl n => (BitWorld.query (.inl n) :)
  | .inr q => fillPrefix q.1 >>= fun _ => expand (.inr q)

lemma padding_preserves {α : Type} (c : OracleComp family.world α) (s : Cache) :
    𝒮[bitRun (simulateQ paddedExpand c) s] = 𝒮[bitRun (simulateQ expand c) s] := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,bitRun,StateT.run'_eq,
      StateT.run_bind,map_bind]
    trans 𝒮[(simulateQ bitImpl (paddedExpand q)).run s >>= fun p =>
      bitRun (simulateQ expand (k p.1)) p.2]
    · apply evalSPMF_bind_congr_left
      intro p
      simpa only [bitRun,simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind] using ih p.1 p.2
    · cases q with
      | inl n => rfl
      | inr q =>
        have h := forget_program (fillPrefix q.1)
          (expand (.inr q) >>= fun y => simulateQ expand (k y)) s
        simpa only [paddedExpand,bitRun,simulateQ_bind,StateT.run'_eq,
          StateT.run_bind,map_bind,bind_assoc] using h

def consEquiv (n : Nat) : Bool × BitVec n ≃ BitVec (n+1) where
  toFun p := BitVec.cons p.1 p.2
  invFun v := (v.msb,v.setWidth n)
  left_inv p := by simp
  right_inv v := by simp

lemma uniform_cons (n : Nat) :
    𝒮[(do let b ← $ᵗ Bool; let v ← $ᵗ BitVec n; return BitVec.cons b v : ProbComp (BitVec (n+1)))] =
      𝒮[$ᵗ BitVec (n+1)] := by
  apply SPMF.ext
  intro v
  change Pr[= v | _] = Pr[= v | _]
  have h := probOutput_map_bijective_uniform_cross (α := Bool × BitVec n)
    (consEquiv n) (consEquiv n).bijective v
  convert h using 1
  simp only [uniformSample,SampleableType.selectElem,seq_eq_bind_map,map_eq_bind_pure_comp,
    bind_assoc,pure_bind,Function.comp_def]
  rfl


lemma readBits_uniform (start n : Nat) :
    𝒮[IdealXof.readBits (fun _ => ($ᵗ Bool : ProbComp Bool)) start n] = 𝒮[$ᵗ BitVec n] := by
  induction n generalizing start with
  | zero =>
      apply SPMF.ext
      intro v
      change Pr[= v | pure 0] = Pr[= v | $ᵗ BitVec 0]
      simp [probOutput_uniformSample,Subsingleton.elim v (0 : BitVec 0)]
  | succ n ih =>
      simp only [IdealXof.readBits]
      trans 𝒮[(do let b ← $ᵗ Bool; let v ← $ᵗ BitVec n; return BitVec.cons b v : ProbComp (BitVec (n+1)))]
      · apply evalSPMF_bind_congr_left
        intro b
        simp only [evalSPMF_bind,evalSPMF_pure,ih]
      · exact uniform_cons n

lemma readBits_fresh (x : IdealXof.Input) (start n : Nat) (s : Cache)
    (hfresh : ∀ i, start ≤ i → i < start+n → s (x,i) = none) :
    𝒮[(IdealXof.readBits (fun i => Bits.randomOracle (x,i)) start n).run' s] =
      𝒮[$ᵗ BitVec n] := by
  induction n generalizing start s with
  | zero =>
    apply SPMF.ext
    intro v
    simp [IdealXof.readBits,Subsingleton.elim v (0 : BitVec 0)]
  | succ n ih =>
    have h0 := hfresh start le_rfl (by omega)
    simp only [IdealXof.readBits,StateT.run'_eq,StateT.run_bind,StateT.run_pure,
      map_bind,map_pure,randomOracle.run_eq,h0,bind_assoc,pure_bind]
    trans 𝒮[(do let b ← $ᵗ Bool; let v ← $ᵗ BitVec n; return BitVec.cons b v : ProbComp (BitVec (n+1)))]
    · apply evalSPMF_bind_congr_left
      intro b
      have ht : ∀ i, start+1 ≤ i → i < start+1+n → (s.cacheQuery (x,start) b) (x,i) = none := by
        intro i hi hj
        rw [QueryCache.cacheQuery_of_ne _ _ (by intro h; have := congrArg Prod.snd h; dsimp at this; omega)]
        exact hfresh i (by omega) (by omega)
      have h := ih (start+1) (s.cacheQuery (x,start) b) ht
      have hm := congrArg (fun d : SPMF (BitVec n) => BitVec.cons b <$> d) h
      simpa only [StateT.run'_eq,evalSPMF_map,Functor.map_map,evalSPMF_bind,evalSPMF_pure,
        map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def] using hm
    · exact uniform_cons n

def Extends (s t : Cache) : Prop := ∀ x b, s x = some b → t x = some b

lemma bit_step (x : Bits.Domain) (s : Cache) (p : Bool × Cache)
    (hp : p ∈ support ((Bits.randomOracle x).run s)) :
    p.2 x = some p.1 ∧ Extends s p.2 ∧ ∀ y, y ≠ x → p.2 y = s y := by
  rw [randomOracle.run_eq] at hp
  cases hx : s x with
  | some b =>
    simp only [hx,support_pure,Set.mem_singleton_iff] at hp
    subst p
    exact ⟨hx,fun _ _ h => h,fun _ _ => rfl⟩
  | none =>
    simp only [hx,support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hp
    obtain ⟨b,_,hp⟩ := hp
    subst p
    refine ⟨by simp,?_,fun y hy => QueryCache.cacheQuery_of_ne _ _ hy⟩
    intro y v hy
    by_cases he : y = x
    · subst y; simp [hx] at hy
    · simpa [QueryCache.cacheQuery_of_ne _ _ he] using hy

lemma readBits_support (x : IdealXof.Input) (start n : Nat) (s : Cache)
    (p : BitVec n × Cache)
    (hp : p ∈ support ((IdealXof.readBits (fun i => Bits.randomOracle (x,i)) start n).run s)) :
    Extends s p.2 ∧
    (∀ i, i < n → p.2 (x,start+i) = some (p.1.getMsbD i)) ∧
    (∀ y, y.1 ≠ x → p.2 y = s y) := by
  induction n generalizing start s with
  | zero =>
    simp only [IdealXof.readBits,StateT.run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst p
    exact ⟨fun _ _ h => h,by omega,fun _ _ => rfl⟩
  | succ n ih =>
    simp only [IdealXof.readBits,StateT.run_bind,StateT.run_pure,
      support_bind,Set.mem_iUnion,support_pure,Set.mem_singleton_iff] at hp
    obtain ⟨a,ha,b,hb,hp⟩ := hp
    subst p
    obtain ⟨ha0,ha1,ha2⟩ := bit_step (x,start) s a ha
    obtain ⟨hb0,hb1,hb2⟩ := ih (start+1) a.2 b hb
    refine ⟨fun y v hy => hb0 y v (ha1 y v hy),?_,?_⟩
    · intro i hi
      cases i with
      | zero => simpa using hb0 (x,start) a.1 ha0
      | succ i =>
        have h := hb1 i (by omega)
        rw [show start+1+i = start+(i+1) by omega] at h
        simpa only [BitVec.getMsbD_cons_succ] using h
    · intro y hy
      rw [hb2 y hy,ha2 y (by intro h; exact hy (congrArg Prod.fst h))]
end CommitGolf.XofBaseline
