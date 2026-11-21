import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.InputOrder
import CommitGolfCandidate.TwoPermutationPackedTrustedInput
import CommitGolfCandidate.QuartetCertificate
import CommitGolfCandidate.QuartetCheckHeap
import CommitGolfCandidate.QuartetOpeningSchedule
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule
import CommitGolfCandidate.TwoPermutationPackedOpeningProofBytes

namespace TwoPermutationPrototype.PackedHonest
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
open TwoPermutationPrototype.Sampling.Quartet (upperHeap quartetLookup openingRecord leafAt opening_record_length
  packEight packedSlot frontierProof238 pack_nodes_length)

set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def honestLeaves (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts

/-- The honest Quartet upper heap: quartet nodes at `2^22+g`, binary projected parents above. -/
def honestHeap (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Digest :=
  upperHeap (quartetLookup (BiPermutation.equiv Block oracle.permutation)) oracle.compression
    (honestLeaves oracle message salts)

def honestOrder (positions : Positions) : List {index // index ∈ positions} :=
  positions.attach.sort (· ≤ ·)

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
        openingRecord (honestLeaves oracle message salts) (honestHeap oracle message salts) i.val (salts i.val)) ++
      frontierProof238 (honestHeap oracle message salts) (Opening.groupsBefore positions positions.card) := by
  rw [← honest_groups]
  rfl

theorem fixed_flatmap_length {α β : Type} (f : α → List β) (width : Nat)
    (fixed : ∀ a, (f a).length = width) (xs : List α) :
    (xs.flatMap f).length = width * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [fixed, ih, Nat.mul_succ, Nat.add_comm]

theorem fixed_flatmap_byte {α β : Type} (f : α → List β) (width : Nat)
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

/-- The packed frontier: `30 f - 2 ⌊f/8⌋` bytes for the `f` cap frontier nodes. -/
theorem honest_frontier_length (heap : Nat → Digest) (positions : Positions) :
    (frontierProof238 heap (Opening.groupsBefore positions positions.card)).length =
      30*(Opening.openingNodes positions).length - 2*((Opening.openingNodes positions).length/8) := by
  have size : (Opening.groupsBefore positions positions.card).length = positions.card := by
    simp [Opening.groupsBefore]
  unfold frontierProof238 Opening.openingNodes
  by_cases noPositions : positions.card = 0
  · have empty : (Opening.groupsBefore positions positions.card).isEmpty = true := by
      rw [List.isEmpty_iff]; exact List.length_eq_zero_iff.mp (size.trans noPositions)
    rw [if_pos empty, if_pos noPositions]
    rfl
  · have some : (Opening.groupsBefore positions positions.card).isEmpty = false := by
      apply Bool.eq_false_of_not_eq_true
      rw [List.isEmpty_iff]
      intro nil
      exact noPositions (size.symm.trans (by rw [nil]; rfl))
    rw [if_neg (by rw [some]; decide), if_neg noPositions]
    have packed := pack_nodes_length ((capFrontierNodes (Opening.groupsBefore positions positions.card) 1 8).map heap)
    rw [List.length_map] at packed
    omega

theorem honest_proof_length (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length =
      534*positions.card +
        (30*(Opening.openingNodes positions).length - 2*((Opening.openingNodes positions).length/8)) := by
  rw [honest_proof_parts, List.length_append,
    fixed_flatmap_length _ 534 (fun _ => opening_record_length _ _ _ _) _, honest_order_length,
    honest_frontier_length]

theorem honest_input_records_fit (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    534*positions.card ≤ (honestCheckInput oracle message positions salts).proof.length := by
  rw [honest_proof_length]
  exact Nat.le_add_right _ _

theorem honest_input_empty (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (empty : positions.card = 0) :
    (honestCheckInput oracle message positions salts).proof.length = 0 := by
  rw [honest_proof_length]
  simp [Opening.openingNodes, empty]

theorem honest_record_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < positions.card) (inside : offset < 534) :
    (honestCheckInput oracle message positions salts).proof[534*ordinal+offset]? =
      (openingRecord (honestLeaves oracle message salts) (honestHeap oracle message salts)
        (honestIndex positions ordinal present) (salts (honestIndex positions ordinal present)))[offset]? := by
  let record := fun i : {i // i ∈ positions} =>
    openingRecord (honestLeaves oracle message salts) (honestHeap oracle message salts) i.val (salts i)
  have width (i : {i // i ∈ positions}) : (record i).length = 534 := opening_record_length _ _ _ _
  have length := fixed_flatmap_length record 534 width (honestOrder positions)
  rw [honest_order_length] at length
  have within : 534*ordinal+offset < ((honestOrder positions).flatMap record).length := by rw [length]; omega
  rw [honest_proof_parts, List.getElem?_append_left within]
  exact fixed_flatmap_byte record 534 width (honestOrder positions) ordinal offset
    (by simpa only [honest_order_length]) inside

/-- A record: salt, the three quartet mates, the 32-byte siblings of loop levels 0 and 1, the 30-byte siblings of
levels 2..5, and the packed block of levels 6..13, all beside the checker's path (`flipIndex index`). -/
theorem record_fields (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128) :
    openingRecord leaves heap index salt =
      saltBytes salt ++ ([1, 2, 3] : List Nat).flatMap (fun j => digestBytes (leafAt leaves (index.val ^^^ j))) ++
        (digestBytes (heap (Opening.lowerNode (QuartetCheck.flipIndex index) 2 ^^^ 1)) ++ digestBytes (heap (Opening.lowerNode (QuartetCheck.flipIndex index) 3 ^^^ 1)) ++
          (List.range 4).flatMap (fun j => proofDigestBytes true (heap (Opening.lowerNode (QuartetCheck.flipIndex index) (j+4) ^^^ 1))) ++
          packEight ((List.range 8).map (fun k => heap (Opening.lowerNode (QuartetCheck.flipIndex index) (k+8) ^^^ 1)))) := by
  have node (level : Nat) :
      (4194304 + (index.val/4 ^^^ 1)) / 2^level = Opening.lowerNode (QuartetCheck.flipIndex index) (level+2) :=
    (QuartetCheck.lower_node_shift_flip index level).symm
  have mid : (List.range 6).flatMap (fun level =>
      proofDigestBytes (2 ≤ level) (heap ((((4194304 + (index.val/4 ^^^ 1)) / 2^level)) ^^^ 1))) =
      digestBytes (heap (Opening.lowerNode (QuartetCheck.flipIndex index) 2 ^^^ 1)) ++ digestBytes (heap (Opening.lowerNode (QuartetCheck.flipIndex index) 3 ^^^ 1)) ++
        (List.range 4).flatMap (fun j => proofDigestBytes true (heap (Opening.lowerNode (QuartetCheck.flipIndex index) (j+4) ^^^ 1))) := by
    rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, node]
    rfl
  have pack : (List.range 8).map (fun k => heap ((((4194304 + index.val/4) / 2^(6+k))) ^^^ 1)) =
      (List.range 8).map (fun k => heap (Opening.lowerNode (QuartetCheck.flipIndex index) (k+8) ^^^ 1)) := by
    congr 1
    funext k
    rw [← QuartetCheck.lower_node_shift index (6+k), show 6+k+2 = k+8 by omega,
      QuartetCheck.lower_node_flip index (k+8) (by omega)]
  unfold openingRecord
  rw [mid, pack]
  simp only [List.append_assoc]

private theorem quartet_part_length (leaves : DigestTape) (index : Index) :
    (([1, 2, 3] : List Nat).flatMap (fun j => digestBytes (leafAt leaves (index.val ^^^ j)))).length = 96 := by
  simp [digestBytes_length]

private theorem head_length (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    (saltBytes salt ++ ([1, 2, 3] : List Nat).flatMap (fun j => digestBytes (leafAt leaves (index.val ^^^ j)))).length = 112 := by
  rw [List.length_append, quartet_part_length]
  simp [saltBytes]

theorem nonce_byte (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 16) :
    (openingRecord leaves heap index salt)[offset]? = some (salt.extractLsb' (8*offset) 8) := by
  rw [record_fields, List.append_assoc, List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes, List.getElem?_ofFn, dite_eq_left inside]

theorem quartet_sibling_byte (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (slot offset : Nat) (valid : slot < 3) (inside : offset < 32) :
    (openingRecord leaves heap index salt)[16+32*slot+offset]? =
      some ((leafAt leaves (index.val ^^^ (slot+1))).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.getElem?_append_left (by rw [head_length]; omega),
    List.getElem?_append_right (by simp only [saltBytes, List.length_ofFn]; omega),
    show (saltBytes salt).length = 16 by simp [saltBytes], show 16+32*slot+offset-16 = 32*slot+offset by omega,
    fixed_flatmap_byte _ 32 (fun _ => digestBytes_length _) _ slot offset (by simpa using valid) inside]
  have entry : ([1, 2, 3] : List Nat)[slot]'(by simpa using valid) = slot+1 := by
    interval_cases slot <;> rfl
  rw [entry]
  simp only [digestBytes, List.getElem?_ofFn, dite_eq_left inside]

theorem first_sibling_byte (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 32) :
    (openingRecord leaves heap index salt)[112+offset]? =
      some ((heap (Opening.lowerNode (QuartetCheck.flipIndex index) 2 ^^^ 1)).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.getElem?_append_right (by rw [head_length]; omega), head_length, Nat.add_sub_cancel_left]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simpa only [digestBytes_length] using inside)]
  simp only [digestBytes, List.getElem?_ofFn, dite_eq_left inside]

theorem second_sibling_byte (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 32) :
    (openingRecord leaves heap index salt)[144+offset]? =
      some ((heap (Opening.lowerNode (QuartetCheck.flipIndex index) 3 ^^^ 1)).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.getElem?_append_right (by rw [head_length]; omega), head_length,
    show 144+offset-112 = 32+offset by omega]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [digestBytes_length]; omega), digestBytes_length, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa only [digestBytes_length] using inside)]
  simp only [digestBytes, List.getElem?_ofFn, dite_eq_left inside]

/-- The 30-byte siblings of loop levels `2..5`. -/
theorem mid_sibling_byte (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (slot offset : Nat) (valid : slot < 4) (inside : offset < 30) :
    (openingRecord leaves heap index salt)[176+30*slot+offset]? =
      some ((heap (Opening.lowerNode (QuartetCheck.flipIndex index) (slot+4) ^^^ 1)).extractLsb' (8*offset) 8) := by
  rw [record_fields, List.getElem?_append_right (by rw [head_length]; omega), head_length,
    show 176+30*slot+offset-112 = 64+(30*slot+offset) by omega]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [digestBytes_length]; omega), digestBytes_length,
    show 64+(30*slot+offset)-32 = 32+(30*slot+offset) by omega,
    List.getElem?_append_right (by rw [digestBytes_length]; omega), digestBytes_length, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by
      rw [fixed_flatmap_length _ 30 (fun _ => proof_digest_length true _) _, List.length_range]; omega),
    fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ slot offset (by simpa using valid) inside,
    List.getElem_range]
  simp only [proofDigestBytes, ite_true, List.getElem?_take, if_pos inside,
    digestBytes, List.getElem?_ofFn, Nat.lt_trans inside (by decide : 30<32), dite_true]

/-- The packed block of loop levels `6..13`. -/
theorem packed_block_byte (leaves : DigestTape) (heap : Nat → Digest) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 238) :
    (openingRecord leaves heap index salt)[296+offset]? =
      (packEight ((List.range 8).map (fun k => heap (Opening.lowerNode (QuartetCheck.flipIndex index) (k+8) ^^^ 1))))[offset]? := by
  rw [record_fields, List.getElem?_append_right (by rw [head_length]; omega), head_length,
    show 296+offset-112 = 184+offset by omega]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by rw [digestBytes_length]; omega), digestBytes_length,
    show 184+offset-32 = 152+offset by omega,
    List.getElem?_append_right (by rw [digestBytes_length]; omega), digestBytes_length,
    show 152+offset-32 = 120+offset by omega,
    List.getElem?_append_right (by
      rw [fixed_flatmap_length _ 30 (fun _ => proof_digest_length true _) _, List.length_range]; omega),
    fixed_flatmap_length _ 30 (fun _ => proof_digest_length true _) _, List.length_range,
    show 120+offset-30*4 = offset by omega]

theorem honest_projected_node (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (node : Nat)
    (pos : 0<node) (internal : node<2097152) :
    (0#16) ++ (honestHeap oracle message salts node).extractLsb' 0 240 = honestHeap oracle message salts node :=
  QuartetCheck.upper_heap_projected _ _ _ node pos internal

theorem honest_projected238_node (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (node : Nat)
    (pos : 0<node) (internal : node<2^17) :
    pad238 (honestHeap oracle message salts node) = honestHeap oracle message salts node :=
  QuartetCheck.upper_heap_projected238 _ _ _ node pos internal

theorem honest_input_admitted (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length ≤ PackedChecker.submission.sizes.proof := by
  rw [honest_proof_length]
  have cap := QuartetOpening.capacity_all positions
  unfold QuartetOpening.proofLength at cap
  change _ ≤ 8959041024
  change _ ≤ 8959041024 at cap
  omega

theorem read_field {bits : Nat} (input : CheckInput)
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
      (PackedChecker.submission.layout.proof+534*ordinal) 16 = salts (honestIndex positions ordinal present) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) (salts (honestIndex positions ordinal present))
    (534*ordinal) 16 (by omega) (by
      intro j bound
      rw [honest_record_byte oracle message positions salts _ _ present (by omega),nonce_byte _ _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_quartet_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal slot : Nat) (present : ordinal < positions.card) (valid : slot < 3) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(534*ordinal+16+32*slot)) 32 =
      leafAt (honestLeaves oracle message salts) ((honestIndex positions ordinal present).val.val ^^^ (slot+1)) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (534*ordinal+16+32*slot) 32 (by omega) (by
      intro j bound
      rw [show 534*ordinal+16+32*slot+j = 534*ordinal+(16+32*slot+j) by omega,
        honest_record_byte oracle message positions salts _ _ present (by omega),
        quartet_sibling_byte _ _ _ _ slot j valid bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_first_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(534*ordinal+112)) 32 =
      honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) 2 ^^^ 1) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (534*ordinal+112) 32 (by omega) (by
      intro j bound
      rw [Nat.add_assoc, honest_record_byte oracle message positions salts _ _ present (by omega),
        first_sibling_byte _ _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_second_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(534*ordinal+144)) 32 =
      honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) 3 ^^^ 1) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (534*ordinal+144) 32 (by omega) (by
      intro j bound
      rw [Nat.add_assoc, honest_record_byte oracle message positions salts _ _ present (by omega),
        second_sibling_byte _ _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_mid_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal slot : Nat) (present : ordinal < positions.card) (valid : slot < 4) :
    readBuffer (PackedChecker.submission.initialState .check (honestCheckInput oracle message positions salts))
      (PackedChecker.submission.layout.proof+(534*ordinal+176+30*slot)) 30 =
      (honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (slot+4) ^^^ 1)).extractLsb' 0 240 := by
  have enough := honest_input_records_fit oracle message positions salts
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ (by omega)
  intro j bound
  rw [show 534*ordinal+176+30*slot+j=534*ordinal+(176+30*slot+j) by omega,
    honest_record_byte oracle message positions salts _ _ present (by omega),
    mid_sibling_byte _ _ _ _ slot j valid bound]

/-- The packed block of an honest record, byte by byte. -/
theorem honest_input_packed_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat) (present : ordinal < positions.card) (inside : offset < 238) :
    (honestCheckInput oracle message positions salts).proof[534*ordinal+296+offset]? =
      (packEight ((List.range 8).map (fun k =>
        honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (k+8) ^^^ 1))))[offset]? := by
  rw [show 534*ordinal+296+offset = 534*ordinal+(296+offset) by omega,
    honest_record_byte oracle message positions salts _ _ present (by omega), packed_block_byte _ _ _ _ offset inside]

end TwoPermutationPrototype.PackedHonest
