import CommitGolfCandidate.QuadInputFrame
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

namespace TwoPermutationPrototype.Quad.Honest
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Quad.Checker (honestCheckInput loaderReference)

set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def honestLeaves (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts

def honestHeap (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Digest :=
  quadHeap oracle.compression (quadFunction (BiPermutation.equiv Block oracle.permutation).forward)
    (honestLeaves oracle message salts)

def honestOrder (positions : Positions) : List {index // index ∈ positions} :=
  positions.attach.sort (fun i j => i.val ≤ j.val)

theorem honest_order_length (positions : Positions) : (honestOrder positions).length = positions.card := by
  simp [honestOrder]

def honestIndex (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    {index // index ∈ positions} :=
  (honestOrder positions)[ordinal]'(by simpa only [honest_order_length] using present)

private theorem honest_groups (positions : Positions) :
    (honestOrder positions).map (Sampling.capGroup ∘ Subtype.val) = Opening.groupsBefore positions positions.card := by
  unfold Opening.groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← CommitGolfCandidate.sorted_value_indices positions, List.map_map]
  rfl

theorem honest_proof_parts (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof =
      (honestOrder positions).flatMap (fun i : {i // i ∈ positions} =>
        quadLowerRecord (honestHeap oracle message salts) (honestLeaves oracle message salts) i.val (salts i.val)) ++
      (Opening.openingNodes positions).flatMap (fun node => proofDigestBytes true (honestHeap oracle message salts node)) := by
  change _ ++ frontierProof true _ ((honestOrder positions).map (Sampling.capGroup ∘ Subtype.val)) = _
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
    (honestCheckInput oracle message positions salts).proof.length = 534*positions.card+30*(Opening.openingNodes positions).length := by
  rw [honest_proof_parts, List.length_append,
    fixed_flatmap_length _ 534 (fun _ => quad_lower_record_length _ _ _ _) _,
    fixed_flatmap_length _ 30 (fun _ => proof_digest_length true _) _, honest_order_length]

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
      (quadLowerRecord (honestHeap oracle message salts) (honestLeaves oracle message salts) (honestIndex positions ordinal present)
        (salts (honestIndex positions ordinal present)))[offset]? := by
  let record := fun i : {i // i ∈ positions} => quadLowerRecord (honestHeap oracle message salts) (honestLeaves oracle message salts) i.val (salts i)
  have width (i : {i // i ∈ positions}) : (record i).length = 534 := quad_lower_record_length _ _ _ _
  have length := fixed_flatmap_length record 534 width (honestOrder positions)
  rw [honest_order_length] at length
  have within : 534*ordinal+offset < ((honestOrder positions).flatMap record).length := by rw [length]; omega
  rw [honest_proof_parts, List.getElem?_append_left within]
  exact fixed_flatmap_byte record 534 width (honestOrder positions) ordinal offset
    (by simpa only [honest_order_length]) inside

theorem honest_frontier_byte (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal offset : Nat)
    (present : ordinal < (Opening.openingNodes positions).length) (inside : offset < 30) :
    (honestCheckInput oracle message positions salts).proof[534*positions.card+30*ordinal+offset]? =
      (proofDigestBytes true (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]))[offset]? := by
  let record := fun i : {i // i ∈ positions} => quadLowerRecord (honestHeap oracle message salts) (honestLeaves oracle message salts) i.val (salts i)
  have length := fixed_flatmap_length record 534 (fun _ => quad_lower_record_length _ _ _ _) (honestOrder positions)
  rw [honest_order_length] at length
  rw [honest_proof_parts, List.getElem?_append_right (by rw [length]; omega), length,
    show 534*positions.card+30*ordinal+offset-534*positions.card = 30*ordinal+offset by omega]
  exact fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ ordinal offset present inside

theorem nonce_byte (heap : Nat → Digest) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset < 16) :
    (quadLowerRecord heap leaves index salt)[offset]? = some (salt.extractLsb' (8*offset) 8) := by
  simp only [quadLowerRecord,List.append_assoc]
  rw [List.getElem?_append_left (by simpa [saltBytes] using inside)]
  simp only [saltBytes,List.getElem?_ofFn,dite_eq_left inside]

private theorem child_bytes_length (leaves : DigestTape) (index : Index) :
    ((List.range 3).flatMap (fun j => digestBytes (quadLeaf leaves index (quadRotSlot index j)))).length = 96 := by
  rw [fixed_flatmap_length _ 32 (fun _ => digestBytes_length _) _]
  rfl

private theorem prefix_bytes_length (heap : Nat → Digest) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    (saltBytes salt ++
      (List.range 3).flatMap (fun j => digestBytes (quadLeaf leaves index (quadRotSlot index j))) ++
      proofDigestBytes false (heap (((LENGTH+index.val)/4) ^^^ 1))).length = 144 := by
  rw [List.length_append,List.length_append,child_bytes_length,proof_digest_length]
  simp [saltBytes]

theorem child_byte (heap : Nat → Digest) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (child offset : Nat) (which : child<3) (inside : offset<32) :
    (quadLowerRecord heap leaves index salt)[16+32*child+offset]? =
      some ((quadLeaf leaves index (quadRotSlot index child)).extractLsb' (8*offset) 8) := by
  unfold quadLowerRecord
  rw [List.getElem?_append_left (by rw [prefix_bytes_length]; omega)]
  rw [List.getElem?_append_left (by rw [List.length_append,child_bytes_length]; simp [saltBytes]; omega)]
  rw [List.getElem?_append_right (by simp [saltBytes]; omega),show (saltBytes salt).length=16 by simp [saltBytes],
    show 16+32*child+offset-16=32*child+offset by omega]
  rw [fixed_flatmap_byte _ 32 (fun _ => digestBytes_length _) _ child offset (by simpa using which) inside]
  rw [List.getElem_range]
  simp only [digestBytes,List.getElem?_ofFn,dite_eq_left inside]

theorem first_sibling_byte (heap : Nat → Digest) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (offset : Nat) (inside : offset<32) :
    (quadLowerRecord heap leaves index salt)[112+offset]? =
      some ((heap (((LENGTH+index.val)/4) ^^^ 1)).extractLsb' (8*offset) 8) := by
  have prefixLength : (saltBytes salt ++
    (List.range 3).flatMap (fun j => digestBytes (quadLeaf leaves index (quadRotSlot index j)))).length=112 := by
    rw [List.length_append,child_bytes_length]; simp [saltBytes]
  unfold quadLowerRecord
  rw [List.getElem?_append_left (by rw [prefix_bytes_length]; omega),
    List.getElem?_append_right (by rw [prefixLength]; omega),prefixLength,Nat.add_sub_cancel_left]
  simp only [proofDigestBytes, Bool.false_eq_true,ite_false,digestBytes,List.getElem?_ofFn,dite_eq_left inside]

theorem later_sibling_byte (heap : Nat → Digest) (leaves : DigestTape) (index : Index) (salt : BitVec 128)
    (sibling offset : Nat) (which : sibling<13) (inside : offset<30) :
    (quadLowerRecord heap leaves index salt)[144+30*sibling+offset]? =
      some ((heap (((LENGTH+index.val)/2^(sibling+3)) ^^^ 1)).extractLsb' (8*offset) 8) := by
  unfold quadLowerRecord
  rw [List.getElem?_append_right (by rw [prefix_bytes_length]; omega),prefix_bytes_length,
    show 144+30*sibling+offset-144=30*sibling+offset by omega]
  rw [fixed_flatmap_byte _ 30 (fun _ => proof_digest_length true _) _ sibling offset (by simpa using which) inside]
  rw [List.getElem_range]
  simp only [proofDigestBytes,ite_true,List.getElem?_take,ite_eq_left inside,
    digestBytes,List.getElem?_ofFn,Nat.lt_trans inside (by decide : 30<32),dite_true]

theorem honest_input_admitted (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (honestCheckInput oracle message positions salts).proof.length ≤ loaderReference.sizes.proof := by
  rw [honest_proof_length]
  have cardinal : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have nodes := Opening.opening_nodes_bound positions
  change 534*positions.card+30*(Opening.openingNodes positions).length≤534*16777216+7680
  change positions.card≤16777216 at cardinal
  omega

private theorem read_field {bits : Nat} (input : CheckInput)
    (valid : input.proof.length ≤ loaderReference.sizes.proof)
    (value : BitVec bits) (start count : Nat) (within : start+count ≤ input.proof.length)
    (serialized : ∀ j, j<count → input.proof[start+j]? = some (value.extractLsb' (8*j) 8)) :
    readBuffer (loaderReference.initialState .check input)
      (loaderReference.layout.proof+start) count = value.extractLsb' 0 (8*count) := by
  apply read_serialized_slice _ value _ 0 count
  intro j small
  have bounded : start+j < input.proof.length := by omega
  rw [Nat.add_assoc, Checker.check_input_proof_byte input valid _ bounded]
  have byte := serialized j small
  rw [List.getElem?_eq_getElem bounded, Option.some_inj] at byte
  simpa only [Nat.zero_add] using byte

theorem honest_input_nonce (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+534*ordinal) 16 = salts (honestIndex positions ordinal present) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) (salts (honestIndex positions ordinal present))
    (534*ordinal) 16 (by omega) (by
      intro j bound
      rw [honest_record_byte oracle message positions salts _ _ present (by omega),nonce_byte _ _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_child (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal child : Nat) (present : ordinal<positions.card) (which : child<3) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+(534*ordinal+16+32*child)) 32 =
      quadLeaf (honestLeaves oracle message salts) (honestIndex positions ordinal present)
        (quadRotSlot (honestIndex positions ordinal present) child) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (534*ordinal+16+32*child) 32 (by omega) (by
      intro j bound
      rw [show 534*ordinal+16+32*child+j=534*ordinal+(16+32*child+j) by omega,
        honest_record_byte oracle message positions salts _ _ present (by omega),
        child_byte _ _ _ _ child j which bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_first_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal<positions.card) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+(534*ordinal+112)) 32 =
      honestHeap oracle message salts (((LENGTH+(honestIndex positions ordinal present).val.val)/4) ^^^ 1) := by
  have enough := honest_input_records_fit oracle message positions salts
  have bytes := read_field (honestCheckInput oracle message positions salts)
    (honest_input_admitted oracle message positions salts) _ (534*ordinal+112) 32 (by omega) (by
      intro j bound
      rw [Nat.add_assoc,honest_record_byte oracle message positions salts _ _ present (by omega),
        first_sibling_byte _ _ _ _ j bound])
  exact bytes.trans BitVec.extractLsb'_eq_self

theorem honest_input_later_sibling (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal sibling : Nat) (present : ordinal<positions.card) (which : sibling<13) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+(534*ordinal+144+30*sibling)) 30 =
      (honestHeap oracle message salts
        (((LENGTH+(honestIndex positions ordinal present).val.val)/2^(sibling+3)) ^^^ 1)).extractLsb' 0 240 := by
  have enough := honest_input_records_fit oracle message positions salts
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ (by omega)
  intro j bound
  rw [show 534*ordinal+144+30*sibling+j=534*ordinal+(144+30*sibling+j) by omega,
    honest_record_byte oracle message positions salts _ _ present (by omega),
    later_sibling_byte _ _ _ _ sibling j which bound]

theorem honest_frontier_digest (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal<(Opening.openingNodes positions).length) :
    readBuffer (loaderReference.initialState .check (honestCheckInput oracle message positions salts))
      (loaderReference.layout.proof+(534*positions.card+30*ordinal)) 30 =
      (honestHeap oracle message salts (Opening.openingNodes positions)[ordinal]).extractLsb' 0 240 := by
  have enough : 534*positions.card+30*ordinal+30≤(honestCheckInput oracle message positions salts).proof.length := by
    rw [honest_proof_length]
    omega
  apply read_field _ (honest_input_admitted oracle message positions salts) _ _ _ enough
  intro j bound
  rw [honest_frontier_byte oracle message positions salts ordinal j present bound]
  simp only [proofDigestBytes,ite_true,List.getElem?_take,ite_eq_left bound,
    digestBytes,List.getElem?_ofFn,Nat.lt_trans bound (by decide : 30<32),dite_true]

theorem honest_projected_node (compress : Compression) (quad : QuadFunction) (leaves : DigestTape) (node : Nat)
    (positive : 0<node) (internal : node<LENGTH/4) :
    (0#16) ++ (quadHeap compress quad leaves node).extractLsb' 0 240 = quadHeap compress quad leaves node := by
  rw [quad_heap_parent compress quad leaves node positive internal]
  simp [projectInternal]
  rw [BitVec.extractLsb'_append_eq_right]

end TwoPermutationPrototype.Quad.Honest
