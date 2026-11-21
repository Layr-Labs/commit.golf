import CommitGolfCandidate.Quad2NonceView
import CommitGolfCandidate.TwoPermutationQuad3Spec

/-! Quad3 analogue of `Quad2NonceView`: the public view queries the leaf digests (`2·LENGTH`), the
`LENGTH/4` level-1 nodes, the `LENGTH/16` level-2 nodes and the `LENGTH/64` level-3 nodes, and
tabulates the quad function on those honest inputs only (`Quad3BuildLocal`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
local instance quad3ChainDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192

def queryQuad3Node (qf : QuadFunction) (ds : DigestTape) (m : Nat) : OracleComp World (BitVec 256) := do
  let a ← World.query (.inr (.inr (.inl (quadInput (quad3Group qf ds m)))))
  return a.extractLsb' 0 256

theorem query_quad3_node_bound (qf : QuadFunction) (ds : DigestTape) (m : Nat) :
    PublicQueryBound (queryQuad3Node qf ds m) 1 := by
  unfold queryQuad3Node
  exact ⟨(by change 1 ≤ 1; omega), fun _ => trivial⟩

theorem query_quad3_node_run (o : Oracle) (qf : QuadFunction) (ds : DigestTape) (m : Nat) :
    fixedOracleRun o (queryQuad3Node qf ds m) = pure (quadFunction o.permutation (quad3Group qf ds m)) := by
  rw [queryQuad3Node, fixed_oracle_run_public, fixed_oracle_run_pure]
  rfl

open Classical in
/-- Three-level node table: the two-level table on level-1/2 inputs, then the level-3 inputs. -/
noncomputable def quad3Table (ds : DigestTape) (ns ms ls : List (BitVec 256)) : QuadFunction := fun c =>
  if (∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = c) ∨
      (∃ j, j < LENGTH / 16 ∧ quad2Group (quadTable ds ns) ds j = c) then quad2Table ds ns ms c
  else if h : ∃ m, m < LENGTH / 64 ∧ quad3Group (quad2Table ds ns ms) ds m = c then ls[Classical.choose h]?.getD 0
  else 0

/-- True level lists. -/
def trueOnes (π : Block → Block) (ds : DigestTape) : List (BitVec 256) :=
  (List.range (LENGTH / 4)).map fun j => quadFunction π (quadGroupLeaves ds j)
noncomputable def trueTwos (π : Block → Block) (ds : DigestTape) : List (BitVec 256) :=
  (List.range (LENGTH / 16)).map fun j => quadFunction π (quad2Group (quadTable ds (trueOnes π ds)) ds j)
noncomputable def trueThrees (π : Block → Block) (ds : DigestTape) : List (BitVec 256) :=
  (List.range (LENGTH / 64)).map fun m =>
    quadFunction π (quad3Group (quad2Table ds (trueOnes π ds) (trueTwos π ds)) ds m)

theorem quad2_table_true (π : Block → Block) (ds : DigestTape) (c : Fin 4 → BitVec 256)
    (level : (∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = c) ∨
      (∃ j, j < LENGTH / 16 ∧ quad2Group (quadTable ds (trueOnes π ds)) ds j = c)) :
    quad2Table ds (trueOnes π ds) (trueTwos π ds) c = quadFunction π c := by
  rcases level with ⟨g, lt, rfl⟩ | ⟨j, lt, rfl⟩
  · exact quad2_table_agrees_one π ds _ g lt
  · exact quad2_table_agrees_two π ds j lt

theorem quad2_group_of_agree (f f' : QuadFunction) (ds : DigestTape)
    (one : ∀ g, g < LENGTH / 4 → f (quadGroupLeaves ds g) = f' (quadGroupLeaves ds g))
    (j : Nat) (inside : j < LENGTH / 16) : quad2Group f ds j = quad2Group f' ds j := by
  funext k
  unfold quad2Group quadValue
  exact one _ (by have := k.isLt; have : LENGTH = 16777216 := rfl; omega)

theorem quad3_group_of_agree (f f' : QuadFunction) (ds : DigestTape)
    (one : ∀ g, g < LENGTH / 4 → f (quadGroupLeaves ds g) = f' (quadGroupLeaves ds g))
    (two : ∀ j, j < LENGTH / 16 → f (quad2Group f ds j) = f' (quad2Group f' ds j))
    (m : Nat) (inside : m < LENGTH / 64) : quad3Group f ds m = quad3Group f' ds m := by
  funext k
  unfold quad3Group quad2Value
  exact two _ (by have := k.isLt; have : LENGTH = 16777216 := rfl; omega)

theorem quad3_table_facts (π : Block → Block) (ds : DigestTape) :
    let T := quad3Table ds (trueOnes π ds) (trueTwos π ds) (trueThrees π ds)
    (∀ g, g < LENGTH / 4 → T (quadGroupLeaves ds g) = quadFunction π (quadGroupLeaves ds g)) ∧
    (∀ j, j < LENGTH / 16 → T (quad2Group T ds j) = quadFunction π (quad2Group T ds j)) ∧
    (∀ m, m < LENGTH / 64 → T (quad3Group T ds m) = quadFunction π (quad3Group T ds m)) := by
  intro T
  let ns := trueOnes π ds
  let ms := trueTwos π ds
  let T1 := quadTable ds ns
  let T2 := quad2Table ds ns ms
  -- T agrees with T2 on level-1/2 inputs, and T2 is true there.
  have onLevels : ∀ c, ((∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = c) ∨
      (∃ j, j < LENGTH / 16 ∧ quad2Group T1 ds j = c)) → T c = quadFunction π c := by
    intro c level
    change quad3Table ds ns ms (trueThrees π ds) c = _
    unfold quad3Table
    rw [if_pos level]
    exact quad2_table_true π ds c level
  have one : ∀ g, g < LENGTH / 4 → T (quadGroupLeaves ds g) = quadFunction π (quadGroupLeaves ds g) :=
    fun g lt => onLevels _ (Or.inl ⟨g, lt, rfl⟩)
  have T1one : ∀ g, g < LENGTH / 4 → T1 (quadGroupLeaves ds g) = quadFunction π (quadGroupLeaves ds g) :=
    fun g lt => quad_table_agrees π ds g lt
  have groupT : ∀ j, j < LENGTH / 16 → quad2Group T ds j = quad2Group T1 ds j := by
    intro j lt
    exact quad2_group_of_agree T T1 ds (fun g lt' => (one g lt').trans (T1one g lt').symm) j lt
  have two : ∀ j, j < LENGTH / 16 → T (quad2Group T ds j) = quadFunction π (quad2Group T ds j) := by
    intro j lt
    rw [groupT j lt]
    exact onLevels _ (Or.inr ⟨j, lt, rfl⟩)
  have T2one : ∀ g, g < LENGTH / 4 → T2 (quadGroupLeaves ds g) = quadFunction π (quadGroupLeaves ds g) :=
    fun g lt => quad2_table_agrees_one π ds ms g lt
  have groupT2 : ∀ j, j < LENGTH / 16 → quad2Group T2 ds j = quad2Group T1 ds j := by
    intro j lt
    exact quad2_group_of_agree T2 T1 ds (fun g lt' => (T2one g lt').trans (T1one g lt').symm) j lt
  have T2two : ∀ j, j < LENGTH / 16 → T2 (quad2Group T2 ds j) = quadFunction π (quad2Group T2 ds j) := by
    intro j lt
    rw [groupT2 j lt]
    exact quad2_table_true π ds _ (Or.inr ⟨j, lt, rfl⟩)
  have group3 : ∀ m, m < LENGTH / 64 → quad3Group T ds m = quad3Group T2 ds m := by
    intro m lt
    apply quad3_group_of_agree T T2 ds (fun g lt' => (one g lt').trans (T2one g lt').symm)
    · intro j lt'
      rw [two j lt', T2two j lt', groupT j lt', groupT2 j lt']
    · exact lt
  refine ⟨one, two, ?_⟩
  intro m lt
  rw [group3 m lt]
  by_cases level : (∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = quad3Group T2 ds m) ∨
      (∃ j, j < LENGTH / 16 ∧ quad2Group T1 ds j = quad3Group T2 ds m)
  · exact onLevels _ level
  · change quad3Table ds ns ms (trueThrees π ds) _ = _
    unfold quad3Table
    rw [if_neg level]
    have hh : ∃ m', m' < LENGTH / 64 ∧ quad3Group (quad2Table ds ns ms) ds m' = quad3Group T2 ds m :=
      ⟨m, lt, rfl⟩
    rw [dif_pos hh]
    obtain ⟨lt', eq⟩ := Classical.choose_spec hh
    simp only [trueThrees, List.getElem?_map, List.getElem?_range lt', Option.map_some, Option.getD_some]
    exact congrArg (quadFunction π) eq

noncomputable def queryQuad3 (ds : DigestTape) : OracleComp World QuadFunction := do
  let ns ← queryList (queryQuadNode ds) (List.range (LENGTH / 4))
  let ms ← queryList (queryQuad2Node (quadTable ds ns) ds) (List.range (LENGTH / 16))
  let ls ← queryList (queryQuad3Node (quad2Table ds ns ms) ds) (List.range (LENGTH / 64))
  return quad3Table ds ns ms ls

attribute [local irreducible] List.range queryList queryQuadNode queryQuad2Node queryQuad3Node

theorem query_quad3_bound (ds : DigestTape) :
    PublicQueryBound (queryQuad3 ds) (LENGTH / 4 + (LENGTH / 16 + LENGTH / 64)) := by
  unfold queryQuad3
  apply public_query_bound_bind
    (by simpa only [List.length_range, Nat.mul_one] using
      query_list_bound _ 1 (query_quad_node_bound ds) (List.range (LENGTH / 4)))
  intro ns
  apply public_query_bound_bind
    (by simpa only [List.length_range, Nat.mul_one] using
      query_list_bound _ 1 (query_quad2_node_bound (quadTable ds ns) ds) (List.range (LENGTH / 16)))
  intro ms
  have h := public_query_bound_bind
    (query_list_bound _ 1 (query_quad3_node_bound (quad2Table ds ns ms) ds) (List.range (LENGTH / 64)))
    (fun ls => show PublicQueryBound (pure (quad3Table ds ns ms ls) : OracleComp World _) 0 from trivial)
  simpa only [List.length_range, Nat.add_zero, Nat.mul_one] using h

theorem query_quad3_run (o : Oracle) (ds : DigestTape) :
    fixedOracleRun o (queryQuad3 ds) =
      pure (quad3Table ds (trueOnes o.permutation ds) (trueTwos o.permutation ds) (trueThrees o.permutation ds)) := by
  rw [queryQuad3, fixed_oracle_run_bind,
    query_list_reference o _ _ _ (fun g _ => query_quad_node_run o ds g), pure_bind, fixed_oracle_run_bind,
    query_list_reference o _ _ _ (fun h _ => query_quad2_node_run o _ ds h), pure_bind, fixed_oracle_run_bind,
    query_list_reference o _ _ _ (fun m _ => query_quad3_node_run o _ ds m), pure_bind, fixed_oracle_run_pure]
  rfl

noncomputable def chainQuad3Comp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (build : QuadTranscriptBuilder) (c : Compression) (b : Bool) (r : CompleteSaltTape) :
    OracleComp World O := do
  let ch ← a.choose
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let qf ← queryQuad3 ds
  let view := build c qf ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] queryDigests guardedView queryQuad3

theorem chain_quad3_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (c : Compression) (b : Bool)
    (r : CompleteSaltTape) :
    PublicQueryBound (chainQuad3Comp a t build c b r)
      (t + 2*LENGTH + (LENGTH/4 + (LENGTH/16 + LENGTH/64)) + t) := by
  unfold chainQuad3Comp
  rw [show t + 2*LENGTH + (LENGTH/4 + (LENGTH/16 + LENGTH/64)) + t =
    t + (2*LENGTH + ((LENGTH/4 + (LENGTH/16 + LENGTH/64)) + t)) by omega]
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (query_digests_bound _ _)
  intro ds
  apply public_query_bound_bind (query_quad3_bound _)
  intro qf
  exact guarded_view_bound a t ch.aux _ _

theorem quad3_table_build (build : QuadTranscriptBuilder) (isLocal : Quad3BuildLocal build) (o : Oracle)
    (ds : DigestTape) (positions : Positions) (salts : OpenedSalts positions) :
    build o.compression (quad3Table ds (trueOnes o.permutation ds) (trueTwos o.permutation ds)
      (trueThrees o.permutation ds)) positions salts ds =
      build o.compression (quadFunction o.permutation) positions salts ds := by
  obtain ⟨one, two, three⟩ := quad3_table_facts o.permutation ds
  exact isLocal o.compression _ (quadFunction o.permutation) positions salts ds one two three

theorem chain_quad3_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (isLocal : Quad3BuildLocal build)
    (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (chainQuad3Comp a t build o.compression b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (quadHonestView build) o.compression ch b
            (BiPermutation.equiv Block o.permutation) r) := by
  rw [chainQuad3Comp, fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind, query_digests_run, pure_bind, fixed_oracle_run_bind, query_quad3_run, pure_bind,
    reached_view o a h ch hit, quad3_table_build build isLocal o]
  simp only [observeTranscriptView, quadHonestView, fixedOracle, Equiv.symm_apply_apply]
  rfl

end TwoPermutationPrototype.Sampling
