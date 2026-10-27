import CommitGolfCandidate.Xof.RandomOracleProof.Support
import CommitGolfCandidate.Xof.RandomOracleProof.Cost
namespace CommitGolf.RandomOracleBaseline
open OracleComp OracleSpec Scheme
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
abbrev Result := Claim × Nat × Bool × Bool

def check (c : OracleComp CompressionBaseline.HashSpec Bool) : OracleComp family.world Bool :=
  simulateQ interface.worldImpl (liftM c)

def experiment (A : Adversary family) : OracleComp family.world Result := do
  let (claim,calls) ← counted A
  let a₀ ← check (CompressionBaseline.merkle.check claim.root claim.positions₀ claim.values₀ claim.proof₀)
  let a₁ ← check (CompressionBaseline.merkle.check claim.root claim.positions₁ claim.values₁ claim.proof₁)
  return (claim,calls,a₀,a₁)

noncomputable def attack (A : Adversary family) : OracleComp family.world Result := do
  let r ← experiment A
  let _ ← simulateQ interface.worldImpl (CompressionBaseline.recheck r.1)
  return r

def Wins (q : Nat) (r : Result) : Prop :=
  r.1.Conflicting ∧ r.2.1 ≤ q ∧ r.2.2.1 = true ∧ r.2.2.2 = true

lemma check_shared (c : OracleComp CompressionBaseline.HashSpec Bool) :
    simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT family.State ProbComp) +
      family.sharedAnswer) (check c) =
      family.checkShared (simulateQ interface.impl c) := by
  induction c using OracleComp.inductionOn with
  | pure a => simp [check,OracleFamily.checkShared]
  | query_bind x k ih =>
    simp only [check,liftM_bind,simulateQ_bind] at ih ⊢
    have hq : (liftM (liftM (CompressionBaseline.HashSpec.query x) : OracleComp CompressionBaseline.HashSpec _) :
        OracleComp CompressionBaseline.HashWorld _) =
        (CompressionBaseline.HashWorld.query (.inr x) : OracleComp CompressionBaseline.HashWorld _) := by
      rw [← OracleComp.liftComp_eq_liftM (mx := liftM _),OracleComp.liftComp_query]
      rfl
    rw [hq]
    simp [MerkleAdapter.Interface.worldImpl,interface,OracleFamily.checkShared,
      MerkleAdapter.Interface.impl] at ih ⊢
    exact congrArg (fun f => family.sharedAnswer (encode x) >>= f) (funext ih)

lemma fixedRun_experiment (H : family.Realization) (A : Adversary family) (p : Result × Table)
    (hp : p ∈ support (fixedRun H (experiment A) [])) (q : Nat) (hw : Wins q p.1) :
    CompressionBaseline.merkle.Breaks (interface.project H) p.1.1 ∧
      p.2.length ≤ q + 2 * (LENGTH * LOG_LENGTH) := by
  rw [experiment,fixedRun_bind] at hp
  simp only [support_bind,Set.mem_iUnion] at hp
  obtain ⟨a,ha,hp⟩ := hp
  rw [fixedRun_bind] at hp
  simp only [support_bind,Set.mem_iUnion] at hp
  obtain ⟨b,hb,hp⟩ := hp
  rw [fixedRun_bind] at hp
  simp only [support_bind,Set.mem_iUnion] at hp
  obtain ⟨c,hc,hp⟩ := hp
  simp only [fixedRun_pure,support_pure,Set.mem_singleton_iff] at hp
  subst p
  obtain ⟨hconf,hcalls,hbtrue,hctrue⟩ := hw
  have hcount := fixedRun_counted_support H A [] a ha
  obtain ⟨hbval,hblen⟩ := fixedRun_source_check H _ a.2 b hb
  obtain ⟨hcval,hclen⟩ := fixedRun_source_check H _ b.2 c hc
  refine ⟨⟨hconf,?_,?_⟩,?_⟩
  · simpa only [CompressionBaseline.Hash.family_eval] using hbval.symm.trans hbtrue
  · simpa only [CompressionBaseline.Hash.family_eval] using hcval.symm.trans hctrue
  · have hcb := CompressionBaseline.check_cost_le (interface.project H) a.1.1.root
      a.1.1.positions₀ a.1.1.values₀ a.1.1.proof₀
    have hcc := CompressionBaseline.check_cost_le (interface.project H) a.1.1.root
      a.1.1.positions₁ a.1.1.values₁ a.1.1.proof₁
    simp only [List.length_nil,zero_add] at hcount
    change b.2.length = a.2.length + ((interface.project H).eval
      (CompressionBaseline.merkle.check a.1.1.root a.1.1.positions₀ a.1.1.values₀ a.1.1.proof₀)).2 at hblen
    change c.2.length = b.2.length + ((interface.project H).eval
      (CompressionBaseline.merkle.check a.1.1.root a.1.1.positions₁ a.1.1.values₁ a.1.1.proof₁)).2 at hclen
    dsimp only at hcalls ⊢
    calc c.2.length = b.2.length + _ := hclen
      _ ≤ b.2.length + LENGTH*LOG_LENGTH := Nat.add_le_add_left hcc _
      _ = a.2.length + ((interface.project H).eval
          (CompressionBaseline.merkle.check a.1.1.root a.1.1.positions₀ a.1.1.values₀ a.1.1.proof₀)).2 + LENGTH*LOG_LENGTH := by rw [hblen]
      _ ≤ a.2.length + LENGTH*LOG_LENGTH + LENGTH*LOG_LENGTH := Nat.add_le_add_right (Nat.add_le_add_left hcb _) _
      _ = a.1.2 + LENGTH*LOG_LENGTH + LENGTH*LOG_LENGTH := by rw [hcount]
      _ ≤ q + LENGTH*LOG_LENGTH + LENGTH*LOG_LENGTH := Nat.add_le_add_right (Nat.add_le_add_right hcalls _) _
      _ = q + 2*(LENGTH*LOG_LENGTH) := by omega

lemma attack_bad (A : Adversary family) (q : Nat) (p : Result × Table)
    (hp : p ∈ support (run (attack A) [])) (hw : Wins q p.1) :
    ¬Good p.2 ∧ p.2.length ≤ q + (2*(LENGTH*LOG_LENGTH)+48) := by
  obtain ⟨H,_,_,hp⟩ := fixed_witness (attack A) [] ⟨fun _ => 0,by simp [Agrees]⟩ p hp
  rw [attack,fixedRun_bind] at hp
  simp only [support_bind,Set.mem_iUnion] at hp
  obtain ⟨a,ha,hp⟩ := hp
  rw [fixedRun_bind] at hp
  simp only [support_bind,Set.mem_iUnion] at hp
  obtain ⟨b,hb,hp⟩ := hp
  simp only [fixedRun_pure,support_pure,Set.mem_singleton_iff] at hp
  subst p
  obtain ⟨hbreak,hlen⟩ := fixedRun_experiment H A a ha q hw
  obtain ⟨T,hr,hbad,hT⟩ := fixedRun_recheck H a.1.1 hbreak a.2
  rw [hr,support_pure,Set.mem_singleton_iff] at hb
  subst b
  exact ⟨hbad,by dsimp only; omega⟩
def game (A : Adversary family) : ProbComp Result := do
  let (s,claim,calls) ← bindingGame A
  let ((a₀,a₁),_) ← (merkle.checkClaim claim).run s
  return (claim,calls,a₀,a₁)

lemma experiment_shared (A : Adversary family) :
    simulateQ (HasQuery.toQueryImpl (spec := unifSpec) (m := StateT family.State ProbComp) +
      family.sharedAnswer) (experiment A) = (do
        let r ← family.runShared A
        let b₀ ← family.checkShared (simulateQ interface.impl (CompressionBaseline.merkle.check
          r.1.root r.1.positions₀ r.1.values₀ r.1.proof₀))
        let b₁ ← family.checkShared (simulateQ interface.impl (CompressionBaseline.merkle.check
          r.1.root r.1.positions₁ r.1.values₁ r.1.proof₁))
        return (r.1,r.2,b₀,b₁) : StateT family.State ProbComp Result) := by
  change simulateQ _ (counted A >>= _) = _
  rw [simulateQ_bind,counted_shared]
  apply congrArg (fun f => family.runShared A >>= f)
  funext r
  change simulateQ _ (check _ >>= _) = _
  rw [simulateQ_bind,check_shared]
  congr 1
  funext b₀
  rw [simulateQ_bind,check_shared]
  congr 1

lemma game_eq_run (A : Adversary family) : game A = Prod.fst <$> run (experiment A) [] := by
  have h := congrArg (fun c => Prod.fst <$> c) (run_cache (experiment A) [])
  simp only [Functor.map_map] at h
  rw [h,experiment_shared]
  unfold game bindingGame
  have hinit : family.initialState = pure (toCache []) := rfl
  rw [hinit,pure_bind]
  simp only [bind_assoc,pure_bind,StateT.run_bind,StateT.run_pure,map_eq_bind_pure_comp]
  apply bind_congr
  intro r
  change ((do
    let b₀ ← family.checkShared (simulateQ interface.impl (CompressionBaseline.merkle.check
      r.1.1.root r.1.1.positions₀ r.1.1.values₀ r.1.1.proof₀))
    let b₁ ← family.checkShared (simulateQ interface.impl (CompressionBaseline.merkle.check
      r.1.1.root r.1.1.positions₁ r.1.1.values₁ r.1.1.proof₁))
    return (b₀,b₁) : StateT family.State ProbComp (Bool × Bool)).run r.2 >>= _) = _
  simp only [StateT.run_bind,StateT.run_pure,bind_assoc,pure_bind]
  rfl

lemma run_bind {α β : Type} (c : OracleComp family.world α)
    (k : α → OracleComp family.world β) (T : Table) :
    run (c >>= k) T = run c T >>= fun p => run (k p.1) p.2 := by simp [run]

lemma attack_probability (A : Adversary family) (q : Nat) :
    Pr[Wins q | game A] = Pr[fun p => Wins q p.1 | run (attack A) []] := by
  classical
  rw [game_eq_run,probEvent_map]
  simp only [attack,run_bind,run_pure]
  rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
  apply tsum_congr
  intro r
  by_cases hr : Wins q r.1
  · simp only [Function.comp_def,hr,ite_true]
    rw [probEvent_bind_eq_tsum]
    have hpure (s : Unit × Table) :
        Pr[fun p => Wins q p.1 | (pure (r.1,s.2) : ProbComp (Result × Table))] = 1 := by
      rw [probEvent_pure,if_pos hr]
    conv_rhs => enter [2,1,s]; rw [hpure s]
    simp
  · simp only [Function.comp_def,hr,ite_false]
    apply Eq.symm
    apply mul_eq_zero_of_right
    apply probEvent_eq_zero
    intro s hs hw
    simp only [support_bind,Set.mem_iUnion] at hs
    obtain ⟨t,_,ht⟩ := hs
    simp only [support_pure,Set.mem_singleton_iff] at ht
    subst s
    exact hr hw


set_option exponentiation.threshold 2000
theorem binding_arith (q : Nat) (h1 : 1 ≤ q) (h2 : q < 2 ^ 128) :
    2 ^ 128 * (∑ j ∈ Finset.range (q + (2*(LENGTH*LOG_LENGTH)+48)), (j + 1)) ≤ q * 2 ^ 256 := by
  change 2^128 * (∑ j ∈ Finset.range (q+805306416), (j+1)) ≤ q*2^256
  have hs := CompressionBaseline.sum_closed (q+805306416)
  set S := ∑ j ∈ Finset.range (q+805306416), (j+1)
  zify at hs ⊢
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast h1
  have hq2 : (q : ℤ) ≤ 2 ^ 128 - 1 := by
    have : (q : ℤ) < 2 ^ 128 := by exact_mod_cast h2
    omega
  have hqq : (q : ℤ) * q ≤ q * (2 ^ 128 - 1) := mul_le_mul_of_nonneg_left hq2 hq0
  nlinarith [hqq, hq1, hs]

theorem sum_le (q : Nat) (h1 : 1 ≤ q) (h2 : q < 2 ^ 128) :
    ∑ j ∈ Finset.range (q + (2*(LENGTH*LOG_LENGTH)+48)), ((j + 1 : Nat) : ENNReal) / ((2 ^ 256 : Nat) : ENNReal) ≤
      (q : ENNReal) / 2 ^ 128 := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have h := binding_arith q h1 h2
  have h' : (2 : ENNReal) ^ 128 * ∑ j ∈ Finset.range (q + (2*(LENGTH*LOG_LENGTH)+48)), ((j + 1 : Nat) : ENNReal) ≤
      (q : ENNReal) * 2 ^ 256 := by exact_mod_cast h
  calc _ = ((2 : ENNReal) ^ 128 * ∑ j ∈ Finset.range (q + (2*(LENGTH*LOG_LENGTH)+48)), ((j + 1 : Nat) : ENNReal)) /
        (2 ^ 128 * 2 ^ 256) := by
          rw [ENNReal.mul_div_mul_left] <;> norm_num [div_eq_mul_inv]
    _ ≤ ((q : ENNReal) * 2 ^ 256) / (2 ^ 128 * 2 ^ 256) :=
      ENNReal.div_le_div_right h' _
    _ = _ := by
      rw [ENNReal.mul_div_mul_right] <;> norm_num [div_eq_mul_inv]



theorem merkle_binding : merkle.Binding := by
  intro A q hq
  change Pr[Wins q | game A] ≤ (q : ENNReal) / 2^SECURITY_BITS
  by_cases hbig : 2^128 ≤ q
  · refine probEvent_le_one.trans ?_
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp),one_mul]
    exact_mod_cast hbig
  · push Not at hbig
    rw [attack_probability]
    calc _ ≤ Pr[fun p => ¬Good p.2 ∧ p.2.length ≤ q+(2*(LENGTH*LOG_LENGTH)+48) | run (attack A) []] :=
        probEvent_mono (fun p hp hw => attack_bad A q p hp hw)
      _ ≤ ∑ j ∈ Finset.range (q+(2*(LENGTH*LOG_LENGTH)+48)), CompressionBaseline.pL j := by
        simpa only [List.length_nil,zero_add] using collision_bound (attack A) []
          (q+(2*(LENGTH*LOG_LENGTH)+48)) (by simp [Good])
      _ ≤ _ := by
        simp only [CompressionBaseline.pL_def]
        exact sum_le q hq hbig
end CommitGolf.RandomOracleBaseline
