import CommitGolfCandidate.ReconstructedHidingMarkedPath
import CommitGolfCandidate.TwoPermutationPosterior

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp TwoPermutationPrototype.Sampling HidingTape
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false

theorem checked_pure {A : Type} (allow : Reply → Reply → Bool) (a : A) (flag : Bool) :
    checkedQueries allow (pure a) flag = pure (a,flag) := rfl

theorem checked_bind {A B : Type} (allow : Reply → Reply → Bool)
    (g : OracleComp World A) (next : A → OracleComp World B) (flag : Bool) :
    checkedQueries allow (g >>= next) flag =
      (checkedQueries allow g flag >>= fun result => checkedQueries allow (next result.1) result.2) := by
  induction g using OracleComp.inductionOn generalizing flag with
  | pure a => simp only [pure_bind,checked_pure]
  | query_bind q k ih =>
    rw [bind_assoc,checked_query,checked_query,bind_assoc]
    apply bind_congr
    intro v
    exact ih v _

def cacheAllow (allow : Reply → Reply → Bool) (c : Cache) := c.entries.all (fun r => allow r.1 r.2)

private theorem stored_allow (allow : Reply → Reply → Bool) (c : Cache) (row : Row) (stored : row ∈ c.entries) :
    (cacheAllow allow c && allow row.1 row.2) = cacheAllow allow c := by
  cases h : cacheAllow allow c with
  | false => rfl
  | true => exact (List.all_eq_true.mp h row stored)

private theorem fwd_cache_allow (allow : Reply → Reply → Bool) (c : Cache) (x : Reply) (r : Reply × Cache)
    (atStep : r ∈ support (c.forward x)) :
    (cacheAllow allow c && allow x r.1) = cacheAllow allow r.2 := by
  classical
  unfold PermutationCache.forward at atStep
  split at atStep
  · obtain ⟨a,_,same⟩ := (mem_support_bind_iff _ _ _).mp atStep
    try simp only [support_pure,Set.mem_singleton_iff] at same
    subst r
    exact Bool.and_comm _ _
  · rename_i occupied
    simp only [support_pure,Set.mem_singleton_iff] at atStep
    subst r
    simp only [UnusedInput,not_forall,not_not] at occupied
    obtain ⟨⟨u,y⟩,seen,eq⟩ := occupied
    change u=x at eq
    subst u
    have same := c.example.property (x,y) seen
    change c.example.val.forward x=y at same
    change (cacheAllow allow c && allow x (c.example.val.forward x)) = _
    rw [same]
    exact stored_allow allow c (x,y) seen

private theorem inv_cache_allow (allow : Reply → Reply → Bool) (c : Cache) (y : Reply) (r : Reply × Cache)
    (atStep : r ∈ support (c.inverse y)) :
    (cacheAllow allow c && allow r.1 y) = cacheAllow allow r.2 := by
  classical
  unfold PermutationCache.inverse at atStep
  split at atStep
  · obtain ⟨a,_,same⟩ := (mem_support_bind_iff _ _ _).mp atStep
    try simp only [support_pure,Set.mem_singleton_iff] at same
    subst r
    exact Bool.and_comm _ _
  · rename_i occupied
    simp only [support_pure,Set.mem_singleton_iff] at atStep
    subst r
    simp only [UnusedOutput,not_forall,not_not] at occupied
    obtain ⟨⟨x,v⟩,seen,eq⟩ := occupied
    change v=y at eq
    subst v
    have same := c.example.property (x,y) seen
    change c.example.val.forward x=y at same
    have inv : c.example.val.inverse y=x := by rw [←same,c.example.val.leftInverse]
    change (cacheAllow allow c && allow (c.example.val.inverse y) y) = _
    rw [inv]
    exact stored_allow allow c (x,y) seen

private theorem lazy_query_expand {A : Type} (c : Compression) (q : World.Domain)
    (next : World.Range q → OracleComp World A) (base : Cache) :
    lazyRun c ((liftM (World.query q) : OracleComp World _) >>= next) base =
      ((lazyHandler c q).run base >>= fun r => lazyRun c (next r.1) r.2) := by
  simp [lazyRun,simulateQ_bind,StateT.run_bind]

private theorem step_cache_allow (allow : Reply → Reply → Bool) (c : Compression) (base : Cache)
    (q : World.Domain) (r : World.Range q × Cache) (seen : r ∈ support ((lazyHandler c q).run base)) :
    (cacheAllow allow base && allowAnswer allow q r.1) = cacheAllow allow r.2 := by
  rcases q with coins | inp | x | y
  · simp only [lazyHandler, StateT.run_monadLift, mem_support_bind_iff, support_pure,Set.mem_singleton_iff] at seen
    obtain ⟨_,_,rfl⟩ := seen
    exact Bool.and_true _
  · simp only [lazyHandler,StateT.run_pure,support_pure,Set.mem_singleton_iff] at seen
    subst r
    exact Bool.and_true _
  · exact fwd_cache_allow allow base x r seen
  · exact inv_cache_allow allow base y r seen

theorem checked_lazy_cache {A : Type} (allow : Reply → Reply → Bool) (c : Compression)
    (g : OracleComp World A) (base : Cache) :
    lazyRun c (checkedQueries allow g (cacheAllow allow base)) base =
      ((fun v : A × Cache => ((v.1,cacheAllow allow v.2),v.2)) <$> lazyRun c g base) := by
  induction g using OracleComp.inductionOn generalizing base with
  | pure a => simp only [checked_pure,lazyRun,simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind q next ih =>
    rw [checked_query,lazy_query_expand,lazy_query_expand,map_bind]
    apply bind_congr_of_forall_mem_support
    intro v seen
    rw [step_cache_allow allow c base q v seen]
    exact ih v.1 v.2

end CommitGolfCandidate.Reconstruction.HidingTraffic
