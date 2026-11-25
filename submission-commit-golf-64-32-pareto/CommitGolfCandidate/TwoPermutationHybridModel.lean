import CommitGolfCandidate.TwoPermutationHybridPaths
import CommitGolfCandidate.TwoPermutationAllPackedSchedule
import CommitGolfCandidate.TwoPermutationPinnedHidingTransport

namespace TwoPermutationPrototype.Hybrid
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

def heap (compress : Compression) (leaves : DigestTape) (node : Nat) : Digest :=
  if branch : 0 < node ∧ node < LENGTH then
    normalize node (combine compress (heap compress leaves (2*node)) (heap compress leaves (2*node+1)))
  else if leaf : LENGTH ≤ node ∧ node < 2*LENGTH then leaves ⟨node-LENGTH,by omega⟩
  else 0
termination_by 2*LENGTH-node
decreasing_by all_goals omega

theorem heap_parent (compress : Compression) (leaves : DigestTape) (node : Nat)
    (branch : 0 < node ∧ node < LENGTH) :
    heap compress leaves node = normalize node (combine compress (heap compress leaves (2*node))
      (heap compress leaves (2*node+1))) := by rw [heap,dif_pos branch]

def record (tree : Nat → Digest) (index : Index) (salt : BitVec 128) : List Byte :=
  saltBytes salt ++ (List.range 9).flatMap (fun level =>
    digestBytes (tree (((LENGTH+index.val)/2^level) ^^^ 1))) ++
    (List.range 7).flatMap (fun j => proofDigestBytes true (tree (((LENGTH+index.val)/2^(j+9)) ^^^ 1)))

theorem record_bytes (tree : Nat → Digest) (index : Index) (salt : BitVec 128) :
    (record tree index salt).length = 514 := by
  simp [record,saltBytes,List.length_flatMap,digestBytes_length,proof_digest_length,List.range_succ]

def builder : TranscriptBuilder := fun compress positions salts leaves =>
  let tree := heap compress leaves
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  (tree 1, ordered.flatMap (fun index => record tree index.val (salts index)) ++
    frontierProof true tree (ordered.map (capGroup ∘ Subtype.val)))

theorem proof_bound (compress : Compression) (positions : Positions) (salts : OpenedSalts positions)
    (leaves : DigestTape) (batch : positions.card = 128) :
    (builder compress positions salts leaves).2.length ≤ 69632 := by
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let tree := heap compress leaves
  have size : ordered.length = 128 := by simp [ordered,batch]
  have cap := frontier_proof_bound true tree (ordered.map (capGroup ∘ Subtype.val))
  change (ordered.flatMap (fun index => record tree index.val (salts index)) ++
    frontierProof true tree (ordered.map (capGroup ∘ Subtype.val))).length ≤ _
  simp [List.length_flatMap,record_bytes, size] at cap ⊢
  omega

def openingCycles (positions : Positions) : Nat := AllPacked.scheduledCycles positions + 16*positions.card
def proofLength (positions : Positions) : Nat := AllPacked.proofLength positions + 16*positions.card

theorem opening_bound (positions : Positions) (count : positions.card = BATCH) :
    openingCycles positions ≤ 87559 ∧ proofLength positions ≤ 69632 := by
  obtain ⟨a,b⟩ := AllPacked.scheduled_scored_limits positions count
  have n : positions.card = 128 := count
  simp [openingCycles,proofLength,n]
  omega

theorem exact_opening_bounds : ∃ positions : Positions, positions.card = BATCH ∧
    openingCycles positions = 87559 ∧ proofLength positions = 69632 := by
  obtain ⟨positions,n,a,b⟩ := AllPacked.scheduled_scored_attainment
  exact ⟨positions,n,by rw [openingCycles,a,n];rfl,by rw [proofLength,b,n];rfl⟩

end TwoPermutationPrototype.Hybrid
