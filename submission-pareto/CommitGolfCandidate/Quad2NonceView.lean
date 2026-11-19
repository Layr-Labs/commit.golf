import CommitGolfCandidate.QuadNonceView
import CommitGolfCandidate.TwoPermutationQuad2Spec

/-! Quad2 analogue of `QuadNonceView`: the public view is produced by a public-query computation
(leaf digests `2·LENGTH` queries, the `LENGTH/4` quad nodes, then the `LENGTH/16` quad2 nodes) so the
nonce-chain replacement theorem applies. The quad node function is tabulated on the honest level-1
and level-2 inputs only; `Quad2BuildLocal` says the builder needs nothing else. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
local instance quad2ChainDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192

def queryQuad2Node (qf : QuadFunction) (ds : DigestTape) (h : Nat) : OracleComp World (BitVec 256) := do
  let a ← World.query (.inr (.inr (.inl (quadInput (quad2Group qf ds h)))))
  return a.extractLsb' 0 256

theorem query_quad2_node_bound (qf : QuadFunction) (ds : DigestTape) (h : Nat) :
    PublicQueryBound (queryQuad2Node qf ds h) 1 := by
  unfold queryQuad2Node
  exact ⟨(by change 1 ≤ 1; omega), fun _ => trivial⟩

theorem query_quad2_node_run (o : Oracle) (qf : QuadFunction) (ds : DigestTape) (h : Nat) :
    fixedOracleRun o (queryQuad2Node qf ds h) = pure (quadFunction o.permutation (quad2Group qf ds h)) := by
  rw [queryQuad2Node, fixed_oracle_run_public, fixed_oracle_run_pure]
  rfl

open Classical in
/-- Two-level node table: level-1 inputs first, then the level-2 inputs over the level-1 table. -/
noncomputable def quad2Table (ds : DigestTape) (ns ms : List (BitVec 256)) : QuadFunction := fun c =>
  if ∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = c then quadTable ds ns c
  else if h : ∃ j, j < LENGTH / 16 ∧ quad2Group (quadTable ds ns) ds j = c then ms[Classical.choose h]?.getD 0
  else 0

private theorem quad2_group_table (π : Block → Block) (ds : DigestTape) (h : Nat) (inside : h < LENGTH / 16) :
    quad2Group (quadTable ds ((List.range (LENGTH / 4)).map fun j => quadFunction π (quadGroupLeaves ds j))) ds h =
      quad2Group (quadFunction π) ds h := by
  funext k
  unfold quad2Group quadValue
  exact quad_table_agrees π ds _ (by have := k.isLt; have : LENGTH = 16777216 := rfl; omega)

theorem quad2_table_agrees_one (π : Block → Block) (ds : DigestTape) (ms : List (BitVec 256))
    (g : Nat) (inside : g < LENGTH / 4) :
    quad2Table ds ((List.range (LENGTH / 4)).map fun j => quadFunction π (quadGroupLeaves ds j)) ms
      (quadGroupLeaves ds g) = quadFunction π (quadGroupLeaves ds g) := by
  unfold quad2Table
  rw [if_pos ⟨g, inside, rfl⟩]
  exact quad_table_agrees π ds g inside

theorem quad2_table_agrees_two (π : Block → Block) (ds : DigestTape) (h : Nat) (inside : h < LENGTH / 16) :
    let ns := (List.range (LENGTH / 4)).map fun j => quadFunction π (quadGroupLeaves ds j)
    let ms := (List.range (LENGTH / 16)).map fun j => quadFunction π (quad2Group (quadTable ds ns) ds j)
    quad2Table ds ns ms (quad2Group (quadTable ds ns) ds h) = quadFunction π (quad2Group (quadTable ds ns) ds h) := by
  intro ns ms
  unfold quad2Table
  by_cases one : ∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = quad2Group (quadTable ds ns) ds h
  · rw [if_pos one]
    obtain ⟨g, lt, eq⟩ := one
    rw [← eq]
    exact quad_table_agrees π ds g lt
  · rw [if_neg one]
    have hh : ∃ j, j < LENGTH / 16 ∧ quad2Group (quadTable ds ns) ds j = quad2Group (quadTable ds ns) ds h :=
      ⟨h, inside, rfl⟩
    rw [dif_pos hh]
    obtain ⟨lt, eq⟩ := Classical.choose_spec hh
    simp only [ms, List.getElem?_map, List.getElem?_range lt, Option.map_some, Option.getD_some, eq]

noncomputable def queryQuad2 (ds : DigestTape) : OracleComp World QuadFunction := do
  let ns ← queryList (queryQuadNode ds) (List.range (LENGTH / 4))
  let ms ← queryList (queryQuad2Node (quadTable ds ns) ds) (List.range (LENGTH / 16))
  return quad2Table ds ns ms

attribute [local irreducible] List.range queryList queryQuadNode queryQuad2Node

theorem query_quad2_bound (ds : DigestTape) : PublicQueryBound (queryQuad2 ds) (LENGTH / 4 + LENGTH / 16) := by
  unfold queryQuad2
  apply public_query_bound_bind
    (by simpa only [List.length_range, Nat.mul_one] using
      query_list_bound _ 1 (query_quad_node_bound ds) (List.range (LENGTH / 4)))
  intro ns
  have h := public_query_bound_bind
    (query_list_bound _ 1 (query_quad2_node_bound (quadTable ds ns) ds) (List.range (LENGTH / 16)))
    (fun ms => show PublicQueryBound (pure (quad2Table ds ns ms) : OracleComp World _) 0 from trivial)
  simpa only [List.length_range, Nat.add_zero, Nat.mul_one] using h

theorem query_quad2_run (o : Oracle) (ds : DigestTape) :
    fixedOracleRun o (queryQuad2 ds) =
      pure (let ns := (List.range (LENGTH / 4)).map fun j => quadFunction o.permutation (quadGroupLeaves ds j)
            quad2Table ds ns ((List.range (LENGTH / 16)).map fun j =>
              quadFunction o.permutation (quad2Group (quadTable ds ns) ds j))) := by
  rw [queryQuad2, fixed_oracle_run_bind,
    query_list_reference o _ _ _ (fun g _ => query_quad_node_run o ds g), pure_bind, fixed_oracle_run_bind,
    query_list_reference o _ _ _ (fun h _ => query_quad2_node_run o _ ds h), pure_bind, fixed_oracle_run_pure]

noncomputable def chainQuad2Comp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (build : QuadTranscriptBuilder) (c : Compression) (b : Bool) (r : CompleteSaltTape) :
    OracleComp World O := do
  let ch ← a.choose
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let qf ← queryQuad2 ds
  let view := build c qf ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] queryDigests guardedView queryQuad2

theorem chain_quad2_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (c : Compression) (b : Bool)
    (r : CompleteSaltTape) :
    PublicQueryBound (chainQuad2Comp a t build c b r) (t + 2*LENGTH + (LENGTH/4 + LENGTH/16) + t) := by
  unfold chainQuad2Comp
  rw [show t + 2*LENGTH + (LENGTH/4 + LENGTH/16) + t = t + (2*LENGTH + ((LENGTH/4 + LENGTH/16) + t)) by omega]
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (query_digests_bound _ _)
  intro ds
  apply public_query_bound_bind (query_quad2_bound _)
  intro qf
  exact guarded_view_bound a t ch.aux _ _

theorem quad2_table_build (build : QuadTranscriptBuilder) (isLocal : Quad2BuildLocal build) (o : Oracle)
    (ds : DigestTape) (positions : Positions) (salts : OpenedSalts positions) :
    build o.compression
      (let ns := (List.range (LENGTH / 4)).map fun j => quadFunction o.permutation (quadGroupLeaves ds j)
       quad2Table ds ns ((List.range (LENGTH / 16)).map fun j =>
          quadFunction o.permutation (quad2Group (quadTable ds ns) ds j))) positions salts ds =
      build o.compression (quadFunction o.permutation) positions salts ds := by
  let ns := (List.range (LENGTH / 4)).map fun j => quadFunction o.permutation (quadGroupLeaves ds j)
  let ms := (List.range (LENGTH / 16)).map fun j => quadFunction o.permutation (quad2Group (quadTable ds ns) ds j)
  have one : ∀ g, g < LENGTH / 4 →
      quad2Table ds ns ms (quadGroupLeaves ds g) = quadFunction o.permutation (quadGroupLeaves ds g) :=
    fun g inside => quad2_table_agrees_one o.permutation ds ms g inside
  have groupSame : ∀ j, j < LENGTH / 16 → quad2Group (quad2Table ds ns ms) ds j = quad2Group (quadTable ds ns) ds j := by
    intro j inside
    funext k
    unfold quad2Group quadValue
    have kk : 4 * j + k.val < LENGTH / 4 := by have := k.isLt; have : LENGTH = 16777216 := rfl; omega
    rw [one _ kk, quad_table_agrees o.permutation ds _ kk]
  have two : ∀ j, j < LENGTH / 16 →
      quad2Table ds ns ms (quad2Group (quad2Table ds ns ms) ds j) =
        quadFunction o.permutation (quad2Group (quad2Table ds ns ms) ds j) := by
    intro j inside
    rw [groupSame j inside]
    exact quad2_table_agrees_two o.permutation ds j inside
  exact isLocal o.compression (quad2Table ds ns ms) (quadFunction o.permutation) positions salts ds one two

theorem chain_quad2_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (isLocal : Quad2BuildLocal build)
    (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (chainQuad2Comp a t build o.compression b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (quadHonestView build) o.compression ch b
            (BiPermutation.equiv Block o.permutation) r) := by
  rw [chainQuad2Comp, fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind, query_digests_run, pure_bind, fixed_oracle_run_bind, query_quad2_run, pure_bind,
    reached_view o a h ch hit, quad2_table_build build isLocal o]
  simp only [observeTranscriptView, quadHonestView, fixedOracle, Equiv.symm_apply_apply]
  rfl

end TwoPermutationPrototype.Sampling
