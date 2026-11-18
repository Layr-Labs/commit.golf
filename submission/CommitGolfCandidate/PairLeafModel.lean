import CommitGolfCandidate.TwoPermutationPinnedReplay
import CommitGolfCandidate.QuartetTransport

/-!
# Pair-heads leaf model: the shared interface between the machine proofs and the security proofs

One keyed generator reply fills the salt slots of two adjacent leaves (one even, one odd). Leaves come in two shapes
(entry of leaf `i` at byte `M = 4096 + 256·i`, value `v = v[0..256)`, salt `s` = 16 bytes = `Words 2`):

* **odd leaf**: exactly the existing pinned leaf `pinnedLeafDigest` (first call `P(v[0..200))`, second call
  `P(tag | s | R1[112..200) | v[168..256))`, tag `pinnedPositionTag i = M + 56` at word 0);
* **even leaf** (this file): first call `P(v[56..256))` (`evenFirstInput`), second call
  `P(tag | R1[160..200) | v[0..136) | s)` (`evenSecondInput`), tag `evenPositionTag i = M - 48` at word 0.
  The bytes `v[56..136)` are read raw by both calls (80 bytes); the chain is `R1[160..200)` (40 bytes).

All tags sit at word 0 of the second-call input. Even tags are `≡ 208 (mod 256)`, odd tags `≡ 56 (mod 256)`.
Executable specification: `stack/emu/phmodel2.py` (`digest`), checked against the commit image
(`stack/image/programs-ph-frozen.json`) by `stack/emu/emu_dump.c`.

Targets for the security side (stated here as `Prop`s so both sides compile against fixed names):
* `PairIidHiding`: the pair-leaf analog of `Quartet.final_reference_hiding_sharp`;
* `EvenLeafSmallBound`: the even-leaf analog of `fixed_compression_pinned_leaf_bound_small` (binding; this is what
  the checker lane consumes). `PairReplayBound` (the analog of `PinnedReplayBound`) is kept but not used.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory TwoPermutationPrototype.RV64 CommitGolfCandidate
set_option maxRecDepth 8192

/-- Tag of an even leaf's second call: its entry address minus 48. -/
def evenPositionTag (index : Index) : BitVec 64 :=
  BitVec.ofNat 64 (4048 + 256 * index.val)

/-- First call of an even leaf: value words 7..31 (bytes 56..256). -/
def evenFirstInput (message : Words 32) : Words 25 :=
  fun i => message ⟨i.val + 7, by omega⟩

/-- Second call of an even leaf: tag | first-reply words 20..24 | value words 0..16 | salt. -/
def evenSecondInput (index : Index) (nonce : Words 2) (firstReply : Words 25) (message : Words 32) : Words 25 :=
  fun i =>
    if i.val = 0 then evenPositionTag index
    else if h : i.val < 6 then firstReply ⟨i.val + 19, by omega⟩
    else if h : i.val < 23 then message ⟨i.val - 6, by omega⟩
    else nonce ⟨i.val - 23, by omega⟩

def evenFirstRow (perm : Block → Block) (message : Words 32) : Row :=
  let address := packBuffer (evenFirstInput message)
  (address, perm address)

def evenSecondRow (perm : Block → Block) (index : Index) (nonce : Words 2) (firstReply : Block)
    (message : Words 32) : Row :=
  let address := packBuffer (evenSecondInput index nonce (replyWords firstReply) message)
  (address, perm address)

def evenLeafDigest (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32) : BitVec 256 :=
  outputDigest (evenSecondRow perm index nonce (evenFirstRow perm message).2 message).2

/-- The pair-heads leaf digest: even positions use the even shape, odd positions the existing pinned leaf. -/
def pairLeafDigest (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32) : BitVec 256 :=
  if index.val % 2 = 0 then evenLeafDigest perm index nonce message else pinnedLeafDigest perm index nonce message

def pairFullLeafDigests (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i => pairLeafDigest p.forward i (saltWords (salts i)) (messageWords message i)

theorem pair_leaf_odd (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32)
    (odd : index.val % 2 = 1) : pairLeafDigest perm index nonce message = pinnedLeafDigest perm index nonce message := by
  unfold pairLeafDigest; rw [if_neg (by omega)]

theorem pair_leaf_even (perm : Block → Block) (index : Index) (nonce : Words 2) (message : Words 32)
    (even : index.val % 2 = 0) : pairLeafDigest perm index nonce message = evenLeafDigest perm index nonce message := by
  unfold pairLeafDigest; rw [if_pos even]

/-! ## Structural facts (the API the hiding and binding proofs reuse, mirroring `TaggedPinnedModel`) -/

theorem even_position_tag_injective : Function.Injective evenPositionTag := by
  intro i j same
  have left : 4048 + 256 * i.val < 2^64 := by have range : i.val < 2^24 := i.isLt; omega
  have right : 4048 + 256 * j.val < 2^64 := by have range : j.val < 2^24 := j.isLt; omega
  have raw := congrArg BitVec.toNat same
  simp only [evenPositionTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt left, Nat.mod_eq_of_lt right] at raw
  exact Fin.ext (by omega)

/-- An even tag is never an odd tag (residues 208 and 56 mod 256). -/
theorem even_tag_ne_pinned_tag (i j : Index) : evenPositionTag i ≠ pinnedPositionTag j := by
  intro same
  have left : 4048 + 256 * i.val < 2^64 := by have range : i.val < 2^24 := i.isLt; omega
  have right : 4152 + 256 * j.val < 2^64 := by have range : j.val < 2^24 := j.isLt; omega
  have raw := congrArg BitVec.toNat same
  simp only [evenPositionTag, pinnedPositionTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt left,
    Nat.mod_eq_of_lt right] at raw
  omega

theorem even_second_tag (index : Index) (nonce : Words 2) (reply : Block) (message : Words 32) :
    (packBuffer (evenSecondInput index nonce (replyWords reply) message)).extractLsb' 0 64 =
      evenPositionTag index := by
  have first := packed_word (evenSecondInput index nonce (replyWords reply) message) (0 : Fin 25)
  simpa only [evenSecondInput, Fin.val_zero, Nat.mul_zero, ite_true] using first

theorem even_second_input_nonce_injective (index : Index) (reply : Block) (message : Words 32) :
    Function.Injective (fun nonce : Words 2 => packBuffer (evenSecondInput index nonce (replyWords reply) message)) := by
  intro first second same
  have words := packBuffer_injective same
  funext i
  let slot : Fin 25 := ⟨i.val + 23, by omega⟩
  have sameWord := congrFun words slot
  have nonzero : i.val + 23 ≠ 0 := by omega
  have notChain : ¬ (i.val + 23 < 6) := by omega
  have notMessage : ¬ (i.val + 23 < 23) := by omega
  simpa only [slot, evenSecondInput, nonzero, ite_false, notChain, notMessage, dite_false,
    Nat.add_sub_cancel, Fin.eta] using sameWord

theorem even_second_input_distinct_indices (i j : Index) (r s : Words 2)
    (reply reply' : Block) (message message' : Words 32)
    (same : packBuffer (evenSecondInput i r (replyWords reply) message) =
      packBuffer (evenSecondInput j s (replyWords reply') message')) : i = j := by
  have tag := congrArg (fun word : Block => word.extractLsb' 0 64) same
  exact even_position_tag_injective
    ((even_second_tag i r reply message).symm.trans (tag.trans (even_second_tag j s reply' message')))

/-- An even second-call input never equals an odd (pinned) second-call input: their word-0 tags differ. -/
theorem even_second_ne_pinned_second (i j : Index) (r s : Words 2) (reply reply' : Block)
    (message message' : Words 32) :
    packBuffer (evenSecondInput i r (replyWords reply) message) ≠
      packBuffer (pinnedSecondInput j s (replyWords reply') message') := by
  intro same
  have tag := congrArg (fun word : Block => word.extractLsb' 0 64) same
  exact even_tag_ne_pinned_tag i j
    ((even_second_tag i r reply message).symm.trans (tag.trans (pinned_second_tag j s reply' message')))

/-- Only the top 320 bits of the first reply (words 20..24) enter the even second call. -/
theorem even_chaining_preserved (index : Index) (nonce : Words 2) (tail : BitVec 320)
    (low₀ low₁ : BitVec 1280) (message : Words 32) :
    evenSecondInput index nonce (replyWords (tail ++ low₀)) message =
      evenSecondInput index nonce (replyWords (tail ++ low₁)) message := by
  funext i
  unfold evenSecondInput
  split
  · rfl
  split
  · let start := 64 * (i.val + 19)
    change (tail ++ low₀).extractLsb' start 64 = (tail ++ low₁).extractLsb' start 64
    have inTail : 1280 ≤ start := by dsimp [start]; omega
    exact (BitVec.extractLsb'_append_eq_of_le inTail).trans
      (BitVec.extractLsb'_append_eq_of_le inTail).symm
  · rfl

/-! ## Binding target -/

/-- Two recorded even-shape leaf computations at one index with equal digests and different values. -/
def EvenLeafWitness (rows : List PublicRow) : Prop :=
  ∃ (perm : Block → Block) (index : Index) (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32),
    let a₀ := evenFirstRow perm message₀
    let a₁ := evenFirstRow perm message₁
    let b₀ := evenSecondRow perm index nonce₀ a₀.2 message₀
    let b₁ := evenSecondRow perm index nonce₁ a₁.2 message₁
    PublicRow.permutation a₀.1 a₀.2 ∈ rows ∧ PublicRow.permutation a₁.1 a₁.2 ∈ rows ∧
      PublicRow.permutation b₀.1 b₀.2 ∈ rows ∧ PublicRow.permutation b₁.1 b₁.2 ∈ rows ∧
      outputDigest b₀.2 = outputDigest b₁.2 ∧ message₀ ≠ message₁

def PairReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ PinnedLeafWitness rows ∨ EvenLeafWitness rows

/-- Security-side target (binding): the pair-leaf analog of `PinnedReplayBound`, same budget. -/
abbrev PairReplayBound :=
  ∀ (program : OracleComp World Unit) (q calls : Nat),
    1 ≤ q → q ≤ 2 ^ 120 → calls ≤ q + 2 ^ 31 → PublicQueryBound (recordRows program) calls →
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      PairReplayEvidence result.2] ≤ (q : ENNReal) / 2 ^ 120

/-- **Binding target used by the checker lane** (supersedes `PairReplayBound`, which leaves no room for the quartet-node
term): the even-leaf analog of `fixed_compression_pinned_leaf_bound_small` (QuadReplay.lean) — fixed compression,
uniformly random permutation, `Pr[EvenLeafWitness] ≤ q/2^124`. The checker's total is then
`3q/2^122 + q/2^124 (odd) + q/2^124 (even) + q/2^124 (quartet) = 15q/2^124 ≤ q/2^120`. -/
def EvenLeafSmallBound : Prop :=
  ∀ {α : Type} (compress : Compression) (program : OracleComp World α) (q calls : Nat), 1 ≤ q → q ≤ 2^120 →
    calls ≤ q+2^31 → PublicQueryBound (recordRows program) calls →
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      EvenLeafWitness result.2] ≤ (q : ENNReal)/2^124

theorem PairReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : PairReplayEvidence earlier) : PairReplayEvidence later := by
  rcases evidence with ⟨x,y,a,b,left,right,different,equal⟩ |
    ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,a₀,a₁,b₀,b₁,digest,conflict⟩ |
    ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,a₀,a₁,b₀,b₁,digest,conflict⟩
  · exact Or.inl ⟨x,y,a,b,contained _ left,contained _ right,different,equal⟩
  · exact Or.inr (Or.inl ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,
      contained _ a₀,contained _ a₁,contained _ b₀,contained _ b₁,digest,conflict⟩)
  · exact Or.inr (Or.inr ⟨perm,index,nonce₀,nonce₁,msg₀,msg₁,
      contained _ a₀,contained _ a₁,contained _ b₀,contained _ b₁,digest,conflict⟩)

/-! ## Hiding target -/

namespace Quartet
local instance pairModelDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

/-- `Quartet.honestView` with the pair-heads leaf digests. -/
def pairHonestView (build : QuartetBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build (quartetLookup p) compress positions (fun index => salts index.val) (pairFullLeafDigests p message salts)

/-- `Quartet.viewReference` (independent salts) with the pair-heads leaf digests. -/
noncomputable def pairViewReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : QuartetBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let permutation ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress permutation.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeTranscriptView adversary (pairHonestView build) compress challenge which permutation.val salts

/-- Security-side target (hiding): the pair-leaf analog of `final_reference_hiding_sharp`. -/
def PairIidHiding : Prop :=
  ∀ {State Output : Type} {openingSize : Nat} (adversary : Hiding.HidingAdversary State Output openingSize)
    (build : QuartetBuilder) (compress : Compression) (budget : Nat),
    Hiding.QueryBound adversary budget → budget + 1 ≤ 2^120 →
    measureTVDist (pairViewReference adversary build compress false)
      (pairViewReference adversary build compress true) ≤ ((budget : ℝ) + 1) / 2^121

end Quartet

end TwoPermutationPrototype.Sampling
