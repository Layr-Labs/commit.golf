import CommitGolfCandidate.QuartetFinal
import CommitGolfCandidate.QuartetOldFrame
import CommitGolfCandidate.QuartetOpeningSchedule

namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf CommitGolfCandidate
local instance QuartetConcreteLocalInstance1 {α : Type} : MeasurableSpace α := ⊤

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2048

def leafAt (leaves : DigestTape) (i : Nat) : BitVec 256 :=
  if inside : i < LENGTH then leaves ⟨i,inside⟩ else 0

/-- Little-endian readBuffer puts the highest-address child in the highest bits. -/
def quartetPayload (leaves : DigestTape) (group : Nat) : BitVec 1024 :=
  leafAt leaves (4*group+3) ++ leafAt leaves (4*group+2) ++
    leafAt leaves (4*group+1) ++ leafAt leaves (4*group)

def upperHeap (lookup : BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) : Nat → BitVec 256 :=
  referenceHeap (projectInternal true compress) 4194304 (fun g => lookup (quartetPayload leaves g))

def openingRecord (leaves : DigestTape) (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) : Proof :=
  saltBytes salt ++
    ([1, 2, 3] : List Nat).flatMap (fun j => digestBytes (leafAt leaves (index.val ^^^ j))) ++
    (List.range 14).flatMap (fun level =>
      proofDigestBytes (level != 0) (heap ((((4194304 + index.val/4) / 2^level)) ^^^ 1)))

def builder : QuartetBuilder :=
  fun lookup compress positions salts leaves =>
    let heap := upperHeap lookup compress leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let records := ordered.flatMap (fun i => openingRecord leaves heap i.val (salts i))
    (heap 1, records ++ frontierProof true heap (ordered.map (capGroup ∘ Subtype.val)))

theorem opening_record_length (leaves : DigestTape) (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) :
    (openingRecord leaves heap index salt).length = 534 := by
  unfold openingRecord saltBytes digestBytes
  simp only [List.length_append,List.length_ofFn,List.length_flatMap,
    proof_digest_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  decide

theorem transcript_128 (lookup : BitVec 1024 → BitVec 256) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (count : positions.card = 128) :
    (builder lookup compress positions salts leaves).2.length ≤ 72192 := by
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let heap := upperHeap lookup compress leaves
  have boundary := frontier_proof_bound true heap (ordered.map (capGroup ∘ Subtype.val))
  have cardinal : ordered.length = 128 := by simp [ordered, count]
  change ((ordered.flatMap (fun i => openingRecord leaves heap i.val (salts i))) ++
    frontierProof true heap (ordered.map (capGroup ∘ Subtype.val))).length ≤ _
  simp only [List.length_append,List.length_flatMap]
  simp [Function.comp_def,opening_record_length,cardinal] at boundary ⊢
  omega

theorem abstract_reference_hiding {State Output : Type} {k : Nat}
    (attacker : Hiding.HidingAdversary State Output k) (compress : Compression)
    (budget : Nat) (bounded : Hiding.QueryBound attacker budget) :
    measureTVDist (viewReference attacker builder compress false) (viewReference attacker builder compress true)
      ≤ min 1 (((budget : ℝ) + 1) / 2^120) :=
  final_reference_hiding global_frame attacker builder compress budget bounded

theorem concrete_hiding_of_refinement (scheme : Scheme) (refines : QuartetRefines scheme builder) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2^120)) :=
  scheme_hiding_of_transcript scheme builder refines abstract_reference_hiding

end TwoPermutationPrototype.Sampling.Quartet
