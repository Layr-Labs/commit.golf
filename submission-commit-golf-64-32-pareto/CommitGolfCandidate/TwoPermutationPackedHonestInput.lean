import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.InputOrder
import CommitGolfCandidate.TwoPermutationPackedTrustedInput
import CommitGolfCandidate.TwoPermutationPackedCertificate
import CommitGolfCandidate.TwoPermutationOpeningABI

namespace TwoPermutationPrototype.PackedHonest
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)

set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def honestHeap (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Digest :=
  transcriptHeap true oracle.compression
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

def honestOrder (positions : Positions) : List {index // index ∈ positions} :=
  positions.attach.sort (fun i j => i.val ≤ j.val)

theorem honest_order_length (positions : Positions) : (honestOrder positions).length = positions.card := by
  simp [honestOrder]

def honestIndex (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    {index // index ∈ positions} :=
  (honestOrder positions)[ordinal]'(by simpa only [honest_order_length] using present)

private theorem honest_groups (positions : Positions) :
    (honestOrder positions).map (capGroup ∘ Subtype.val) = Opening.groupsBefore positions positions.card := by
  unfold Opening.groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← CommitGolfCandidate.sorted_value_indices positions, List.map_map]
  rfl

theorem honest_proof_parts (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof =
      (honestOrder positions).flatMap (fun i : {i // i ∈ positions} =>
        lowerRecord true (honestHeap oracle message salts) i.val (salts i.val)) ++
      (Opening.openingNodes positions).flatMap (fun node => proofDigestBytes true (honestHeap oracle message salts node)) := by
  change _ ++ frontierProof true _ ((honestOrder positions).map (capGroup ∘ Subtype.val)) = _
  rw [honest_groups]
  have size : (Opening.groupsBefore positions positions.card).length = positions.card := by
    simp [Opening.groupsBefore]
  have empty : (Opening.groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
    rw [List.isEmpty_iff]
    simpa only [size] using (List.length_eq_zero_iff (l := Opening.groupsBefore positions positions.card)).symm
  unfold frontierProof Opening.openingNodes
  by_cases noPositions : positions.card = 0
  · rw [ite_eq_left (empty.mpr noPositions), ite_eq_left noPositions, List.flatMap_nil]
    rfl
  · have someGroup : (Opening.groupsBefore positions positions.card).isEmpty = false :=
      Bool.eq_false_of_not_eq_true (mt empty.mp noPositions)
    rw [ite_eq_right (by rw [someGroup]; decide), ite_eq_right noPositions]
    rfl

private theorem fixed_flatmap_length {α β : Type} (f : α → List β) (width : Nat)
    (fixed : ∀ a, (f a).length = width) (xs : List α) :
    (xs.flatMap f).length = width * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [fixed, ih, Nat.mul_succ, Nat.add_comm]

private theorem fixed_flatmap_byte {α β : Type} (f : α → List β) (width : Nat)
    (fixed : ∀ a, (f a).length = width) (xs : List α) (ordinal offset : Nat)
    (present : ordinal < xs.length) (inside : offset < width) :
    (xs.flatMap f)[width*ordinal+offset]? = (f xs[ordinal])[offset]? := by
  induction xs generalizing ordinal with
  | nil => simp at present
  | cons x xs inductionHypothesis =>
    cases ordinal with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by simpa only [fixed] using inside)
    | succ ordinal =>
      simp only [List.flatMap_cons, Nat.mul_succ, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [fixed]; omega), fixed,
        show width*ordinal+width+offset-width = width*ordinal+offset by omega]
      exact inductionHypothesis ordinal (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using present)

theorem honest_proof_length (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length =
      496*positions.card + 30*(Opening.openingNodes positions).length := by
  rw [honest_proof_parts, List.length_append,
    fixed_flatmap_length _ 496 (fun _ => lower_record_length true _ _ _) _,
    fixed_flatmap_length _ 30 (fun _ => proof_digest_length true _) _, honest_order_length]

theorem honest_input_records_fit (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    496*positions.card ≤ (honestCheckInput oracle message positions salts).proof.length := by
  rw [honest_proof_length]
  omega

theorem honest_input_empty (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (empty : positions.card = 0) :
    (honestCheckInput oracle message positions salts).proof.length = 0 := by
  rw [honest_proof_length]
  simp [Opening.openingNodes, empty]

theorem honest_record_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < positions.card) (inside : offset < 496) :
    (honestCheckInput oracle message positions salts).proof[496*ordinal+offset]? =
      (lowerRecord true (honestHeap oracle message salts) (honestIndex positions ordinal present)
        (salts (honestIndex positions ordinal present)))[offset]? := by
  let record := fun i : {i // i ∈ positions} => lowerRecord true (honestHeap oracle message salts) i.val (salts i)
  have width (i : {i // i ∈ positions}) : (record i).length = 496 := lower_record_length true _ _ _
  have length := fixed_flatmap_length record 496 width (honestOrder positions)
  rw [honest_order_length] at length
  have within : 496*ordinal+offset < ((honestOrder positions).flatMap record).length := by rw [length]; omega
  rw [honest_proof_parts, List.getElem?_append_left within]
  exact fixed_flatmap_byte record 496 width (honestOrder positions) ordinal offset
    (by simpa only [honest_order_length]) inside

theorem honest_frontier_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < (Opening.openingNodes positions).length) (inside : offset < 30) :
    (honestCheckInput oracle message positions salts).proof[496*positions.card+30*ordinal+offset]? =
      (proofDigestBytes true (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]))[offset]? := by
  let record := fun i : {i // i ∈ positions} => lowerRecord true (honestHeap oracle message salts) i.val (salts i)
  have length := fixed_flatmap_length record 496 (fun _ => lower_record_length true _ _ _) (honestOrder positions)
  rw [honest_order_length] at length
  rw [honest_proof_parts, List.getElem?_append_right (by rw [length]; omega), length,
    show 496*positions.card+30*ordinal+offset-496*positions.card = 30*ordinal+offset by omega]
  exact fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ ordinal offset present inside

theorem nonce_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 16) :
    (lowerRecord true heap index salt)[offset]? = some (salt.extractLsb' (8*offset) 8) := by
  unfold lowerRecord
  rw [List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes, List.getElem?_ofFn, dite_eq_left inside]


theorem record_fields (heap : Nat → Digest) (index : Index) (salt : BitVec 128) :
    lowerRecord true heap index salt =
      saltBytes salt ++
        (List.range 16).flatMap (fun j => proofDigestBytes true (heap (Opening.lowerNode index j ^^^ 1))) := by
  rfl

theorem sibling_byte (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (level offset : Nat) (within : level < 16) (inside : offset < 30) :
    (lowerRecord true heap index salt)[16+30*level+offset]? =
      some ((heap (Opening.lowerNode index level ^^^ 1)).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.getElem?_append_right (by simp [saltBytes]; omega)]
  rw [show (saltBytes salt).length=16 by simp [saltBytes], show 16+30*level+offset-16 = 30*level+offset by omega]
  rw [fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ level offset (by simpa using within) inside]
  rw [List.getElem_range]
  simp only [proofDigestBytes, ite_true, List.getElem?_take, ite_eq_left inside,
    digestBytes, List.getElem?_ofFn, Nat.lt_trans inside (by decide : 30<32), dite_true]

theorem honest_projected_node (compress : Compression) (leaves : DigestTape) (node : Nat)
    (pos : 0<node) (internal : node<LENGTH) :
    (0#16) ++ (transcriptHeap true compress leaves node).extractLsb' 0 240 =
      transcriptHeap true compress leaves node := by
  rw [transcript_heap_parent true compress leaves node pos internal]
  simp [projectInternal]
  rw [BitVec.extractLsb'_append_eq_right]

theorem honest_input_admitted (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length ≤ PackedChecker.submission.sizes.proof := by
  rw [honest_proof_length]
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have nodes := Opening.opening_nodes_bound positions
  have room : 496*16777216+30*128 ≤ PackedChecker.submission.sizes.proof := by decide
  change positions.card ≤ 16777216 at cardinal
  omega

private theorem read_field {bits : Nat} (input : CheckInput)
    (valid : input.proof.length ≤ PackedChecker.submission.sizes.proof)
    (value : BitVec bits) (start count : Nat) (within : start+count ≤ input.proof.length)
    (serialized : ∀ j, j<count → input.proof[start+j]? = some (value.extractLsb' (8*j) 8)) :
    readBuffer (PackedChecker.submission.initialState .check input)
      (PackedChecker.submission.layout.proof+start) count = value.extractLsb' 0 (8*count) := by
  apply read_serialized_slice _ value _ 0 count
  intro j small
  have bounded : start+j < input.proof.length := by omega
  rw [Nat.add_assoc, PackedChecker.check_input_proof_byte input valid _ bounded]
  have byte := serialized j small
  rw [List.getElem?_eq_getElem bounded, Option.some_inj] at byte
  simpa only [Nat.zero_add] using byte

theorem honest_input_nonce (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+496*ordinal) 16 = salts (honestIndex positions ordinal present) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) (salts (honestIndex positions ordinal present))
    (496*ordinal) 16 (by omega) (by
      intro j bound
      rw [honest_record_byte oracle message positions salts _ _ present (by omega),nonce_byte _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

/-- The 30 recorded bytes of the sibling at `level`. -/
theorem honest_input_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal level : Nat) (present : ordinal < positions.card) (within : level<16) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(496*ordinal+16+30*level)) 30 =
      (honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) level ^^^ 1)).extractLsb' 0 240 := by
  have enough := honest_input_records_fit oracle message positions salts
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ (by omega)
  intro j bound
  rw [show 496*ordinal+16+30*level+j=496*ordinal+(16+30*level+j) by omega,
    honest_record_byte oracle message positions salts _ _ present (by omega),
    sibling_byte _ _ _ level j within bound]

theorem honest_frontier_digest (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < (Opening.openingNodes positions).length) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(496*positions.card+30*ordinal)) 30 =
      (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]).extractLsb' 0 240 := by
  have length := honest_proof_length oracle message positions salts
  have enough : 496*positions.card+30*ordinal+30 ≤ (honestCheckInput oracle message positions salts).proof.length := by
    rw [length]
    omega
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ enough
  intro j bound
  rw [honest_frontier_byte oracle message positions salts ordinal j present bound]
  simp only [proofDigestBytes, ite_true, List.getElem?_take, ite_eq_left bound,
    digestBytes, List.getElem?_ofFn, Nat.lt_trans bound (by decide : 30<32), dite_true]

end TwoPermutationPrototype.PackedHonest
