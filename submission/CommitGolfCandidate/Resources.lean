import CommitGolf.Oracle
import VCVio.OracleComp.QueryTracking.CostModel.Simulation
import VCVio.OracleComp.QueryTracking.MeasuredProgram
import ArkLib.Interaction.Oracle.Source
import CompPoly.Univariate.Raw.Size
import Mathlib.Data.List.FinRange

/-! # This candidate's salted-leaf compression resources

This candidate helper reads the eight ordered blocks of an entry through ArkLib's immutable source,
stores them in a CompPoly raw coefficient array, and hashes the stored elements. Its scalar `Nat`
profile counts one per compression query, with standard addition and order. VCVio bounds every
possible response path, then transfers that bound to the challenge's actual public oracle route.

These are concrete worst-case query counts. Source/view construction, coefficient encoding,
polynomial operations, handler evaluation and pure Lean computation are outside this profile.
The separate RISC-V proof remains the authority for charged machine cycles. ArkLib's measured
extractor paths require an extractor contract; no knowledge or extractor claim is introduced here.
-/

namespace CommitGolfCandidate.Resources
open CommitGolf OracleComp OracleSpec

abbrev Digest := BitVec COMPRESSION_OUTPUT_LENGTH

/-- Explicit width evidence changes no bits. -/
def compressionInput (block state : Digest) : BitVec COMPRESSION_INPUT_LENGTH :=
  (block ++ state).cast (by decide)

def entryBlock (value : Entry) (i : Nat) : Digest :=
  (value.extractLsb' (256 * i) 256).cast (by decide)

@[simp] theorem compressionInput_eq (block state : Digest) :
    compressionInput block state = block ++ state := rfl

@[simp] theorem entryBlock_eq (value : Entry) (i : Nat) :
    entryBlock value i = value.extractLsb' (256 * i) 256 := rfl

def compressCost : CostModel CompressionSpec Nat := ⟨fun _ => 1⟩

def hashBlocks : Digest → List Digest → OracleComp CompressionSpec Digest
  | salt, [] => pure salt
  | salt, block :: rest => do
      let next ← (CompressionSpec.query (compressionInput block salt) :)
      hashBlocks next rest

/-- Sequential stage bounds compose over the actual intermediate compression reply. -/
theorem hashBlocks_bound (salt : Digest) (input : List Digest) :
    WorstCaseCostBound (hashBlocks salt input) compressCost input.length := by
  induction input generalizing salt with
  | nil => exact (worstCaseCostBound_pure _ _ _).mpr le_rfl
  | cons block rest ih =>
    simpa only [hashBlocks, compressCost, List.length_cons, Nat.add_comm] using
      (worstCaseCostBound_query (compressionInput block salt) compressCost).bind ih

def blocks (value : Entry) : List Digest := (List.range 8).map (entryBlock value)

/-- A deterministic entry view, rather than a fresh cryptographic oracle. Its reads are uncharged. -/
def entrySource : Interaction.Oracle.SourceCtx (Fin 8) Entry where
  spec := Fin 8 →ₒ Digest
  impl i value := entryBlock value i.val

def sourceBlocks (value : Entry) : List Digest :=
  (List.finRange 8).map (entrySource.handler value)

theorem sourceBlocks_result (value : Entry) : sourceBlocks value = blocks value := by
  apply List.ext_getElem
  · change ((List.finRange 8).map (entrySource.handler value)).length =
      ((List.range 8).map (entryBlock value)).length
    calc
      _ = (List.finRange 8).length := List.length_map ..
      _ = 8 := List.length_finRange
      _ = (List.range 8).length := List.length_range.symm
      _ = _ := (List.length_map ..).symm
  · intro i hi hj
    simp [sourceBlocks, Interaction.Oracle.SourceCtx.handler, entrySource, blocks]
    rfl

/-- Raw storage retains all eight coefficients, including zero blocks. -/
def leafCoefficients (value : Entry) : CompPoly.CPolynomial.Raw Digest :=
  (sourceBlocks value).toArray

@[simp] theorem leafCoefficients_size (value : Entry) : (leafCoefficients value).size = 8 := by
  change (sourceBlocks value).toArray.size = 8
  rw [List.size_toArray, sourceBlocks_result]
  simp only [blocks, List.length_map, List.length_range]

def hashRawCoefficients {F : Type} (encode : F → Digest) (salt : Digest)
    (p : CompPoly.CPolynomial.Raw F) : OracleComp CompressionSpec Digest :=
  hashBlocks salt (p.toList.map encode)

theorem hashRawCoefficients_bound {F : Type} (encode : F → Digest) (salt : Digest)
    (p : CompPoly.CPolynomial.Raw F) :
    WorstCaseCostBound (hashRawCoefficients encode salt p) compressCost p.size := by
  simpa [hashRawCoefficients] using hashBlocks_bound salt (p.toList.map encode)

/-- A separate stored-product client: only subsequent hashing calls are charged, not multiplication
or coefficient encoding. This generic helper is not a polynomial commitment security claim. -/
theorem hashRawProduct_bound {F : Type} [Semiring F] (encode : F → Digest) (salt : Digest)
    (p q : CompPoly.CPolynomial.Raw F) :
    WorstCaseCostBound
      (hashRawCoefficients encode salt (CompPoly.CPolynomial.Raw.mulRaw p q)) compressCost
      (p.size + q.size - 1) := by
  intro result reached
  exact ((hashRawCoefficients_bound encode salt
    (CompPoly.CPolynomial.Raw.mulRaw p q)) result reached).trans
      (CompPoly.CPolynomial.Raw.size_mulRaw_le p q)

/-- The active leaf program consumes the actual source-backed stored array. -/
def leaf (input : Digest × Entry) : OracleComp CompressionSpec Digest :=
  hashRawCoefficients id input.1 (leafCoefficients input.2)

theorem leaf_eq_hashBlocks (input : Digest × Entry) :
    leaf input = hashBlocks input.1 (blocks input.2) := by
  simp [leaf, hashRawCoefficients, leafCoefficients, sourceBlocks_result]

theorem leaf_bound (input : Digest × Entry) :
    WorstCaseCostBound (leaf input) compressCost 8 := by
  simpa only [leaf, leafCoefficients_size] using
    hashRawCoefficients_bound id input.1 (leafCoefficients input.2)

def compressionAnswer (compress : Compression) : QueryImpl CompressionSpec Id := compress

theorem hashBlocks_result (compress : Compression) (salt : Digest) (input : List Digest) :
    simulateQ (compressionAnswer compress) (hashBlocks salt input) =
      input.foldl (fun state block => compress (compressionInput block state)) salt := by
  induction input generalizing salt with
  | nil => rfl
  | cons block rest ih =>
    simp only [hashBlocks, simulateQ_bind, simulateQ_query, compressionAnswer, List.foldl_cons]
    exact ih _

def referenceLeaf (compress : Compression) (input : Digest × Entry) : Digest :=
  (blocks input.2).foldl (fun state block => compress (compressionInput block state)) input.1

def measuredLeaf (compress : Compression) : MeasuredProgram (Digest × Entry) Digest Nat where
  View := Digest × Entry
  view := id
  Op := BitVec COMPRESSION_INPUT_LENGTH
  spec _ := CompressionSpec
  program := leaf
  answer _ := compressionAnswer compress
  cost _ := 1

theorem measuredLeaf_realizes (compress : Compression) :
    (measuredLeaf compress).Realizes (referenceLeaf compress) := by
  intro input
  simp only [MeasuredProgram.run, measuredLeaf, id_eq, leaf_eq_hashBlocks]
  exact (hashBlocks_result compress input.1 (blocks input.2)).symm

theorem measuredLeaf_cost (compress : Compression) : (measuredLeaf compress).CostAtMost 8 :=
  leaf_bound

def budgetedLeaf (compress : Compression) : BudgetedProgram (referenceLeaf compress) Nat :=
  ⟨measuredLeaf compress, 8, measuredLeaf_realizes compress, measuredLeaf_cost compress⟩

/-- Expand compression instructions into the challenge's existing public compression branch. -/
def worldCompressionRoute : QueryImpl CompressionSpec (OracleComp World) :=
  fun input => World.query (.inr (.inl input))

def publicCost : CostModel World Nat := ⟨Oracle.callCost⟩

def privateCost : CostModel World Nat := ⟨fun query => match query with | .inl _ => 1 | .inr _ => 0⟩

def hashWorld (salt : Digest) (input : List Digest) : OracleComp World Digest :=
  simulateQ worldCompressionRoute (hashBlocks salt input)

theorem hashWorld_cons (salt block : Digest) (rest : List Digest) :
    hashWorld salt (block :: rest) =
      (do let next ← (World.query (.inr (.inl (compressionInput block salt))) :)
          hashWorld next rest) := by
  simp only [hashWorld, hashBlocks, simulateQ_bind, simulateQ_spec_query, worldCompressionRoute]
  rfl

def leafWorld (input : Digest × Entry) : OracleComp World Digest :=
  simulateQ worldCompressionRoute (leaf input)

theorem leafWorld_eq_hashWorld (input : Digest × Entry) :
    leafWorld input = hashWorld input.1 (blocks input.2) := by
  rw [leafWorld, leaf_eq_hashBlocks]
  rfl

/-- The named budget applies to every response path, independently of the deterministic handler
chosen to name its realized function. No handler evaluation is charged by this theorem. -/
theorem leafWorld_bound (input : Digest × Entry) :
    WorstCaseCostBound (leafWorld input) publicCost 8 := by
  have localBound := (budgetedLeaf (fun _ => 0)).costAtMost input
  change WorstCaseCostBound (leaf input) compressCost 8 at localBound
  apply localBound.simulateQ worldCompressionRoute
  intro query
  simpa only [worldCompressionRoute, publicCost, compressCost, Oracle.callCost] using
    worstCaseCostBound_query (.inr (.inl query)) publicCost

private theorem hashWorld_no_private (salt : Digest) (input : List Digest) :
    WorstCaseCostBound (hashWorld salt input) privateCost 0 := by
  induction input generalizing salt with
  | nil => simpa only [hashWorld, hashBlocks, simulateQ_pure] using
      ((worstCaseCostBound_pure salt privateCost 0).mpr le_rfl)
  | cons block rest ih =>
    rw [hashWorld_cons, worstCaseCostBound_query_bind_iff]
    intro answer result reached
    simpa only [privateCost, Nat.zero_add] using ih answer result reached

theorem leafWorld_no_private_queries (input : Digest × Entry) :
    WorstCaseCostBound (leafWorld input) privateCost 0 := by
  rw [leafWorld_eq_hashWorld]
  exact hashWorld_no_private input.1 (blocks input.2)

private theorem world_run_pure (oracle : Oracle) {A : Type} (value : A) :
    oracle.run (pure value : OracleComp World A) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

private theorem world_run_bind (oracle : Oracle) {A B : Type}
    (program : OracleComp World A) (next : A → OracleComp World B) :
    oracle.run (program >>= next) =
      (do let (value, first) ← oracle.run program
          let (result, second) ← oracle.run (next value)
          return (result, first + second)) := by
  simp only [Oracle.run, simulateQ_bind, WriterT.run_bind, map_eq_bind_pure_comp]
  rfl

private theorem world_run_compression (oracle : Oracle) (input : BitVec COMPRESSION_INPUT_LENGTH) :
    oracle.run (World.query (.inr (.inl input))) = pure (oracle.compression input, 1) := by
  simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
    QueryImpl.withAddCost, QueryImpl.withCost]
  rfl

private theorem hashWorld_run (oracle : Oracle) (salt : Digest) (input : List Digest) :
    oracle.run (hashWorld salt input) =
      pure (input.foldl (fun state block => oracle.compression (compressionInput block state)) salt,
        input.length) := by
  induction input generalizing salt with
  | nil =>
    simp only [hashWorld, hashBlocks, simulateQ_pure, List.foldl_nil, List.length_nil]
    exact world_run_pure oracle salt
  | cons block rest ih =>
    rw [hashWorld_cons, world_run_bind, world_run_compression]
    simp only [pure_bind]
    rw [ih]
    simp only [pure_bind, List.foldl_cons, List.length_cons, Nat.add_comm]

/-- Exact value and public count under each fixed challenge oracle realization. -/
theorem leafWorld_run (oracle : Oracle) (input : Digest × Entry) :
    oracle.run (leafWorld input) = pure (referenceLeaf oracle.compression input, 8) := by
  rw [leafWorld_eq_hashWorld, hashWorld_run]
  simp only [referenceLeaf, blocks, List.length_map, List.length_range]

end CommitGolfCandidate.Resources
