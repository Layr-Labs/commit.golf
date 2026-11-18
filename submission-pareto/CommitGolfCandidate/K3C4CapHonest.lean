import CommitGolfCandidate.K3C4CapCodec

/-! # The honest packed cap frontier decodes to its nodes

`Quartet.packNodes` lays the frontier out as full blocks of eight (`packEight`, 238 bytes) followed by a
trailing partial group of 30-byte slots (`packedSlot x 0`). Frontier node `i` is read from block `i / 8` at
`start + 238 * (i / 8)`, position `i % 8` (`capFrontierValue`), so memory holding the packed bytes decodes
every node to its 238-bit projection: S9-L1's `packed_node_of_bytes` inside a full block and
`packed_slot_of_bytes` for a tail slot, with the block offsets by induction along `packNodes`. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

private theorem bang_append_left {A B : List Byte} {j : Nat} (inside : j < A.length) :
    (A ++ B)[j]! = A[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left inside]

private theorem bang_append_right {A B : List Byte} (j : Nat) :
    (A ++ B)[A.length + j]! = B[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem node_take {nodes : List (BitVec 256)} {i : Nat} (small : i < 8) :
    (nodes.take 8)[i]! = nodes[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_take, if_pos small]

private theorem node_drop {nodes : List (BitVec 256)} {i : Nat} (large : 8 ≤ i) :
    (nodes.drop 8)[i-8]! = nodes[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_drop,
    show 8 + (i-8) = i by omega]

/-- Byte `30 i + j` of a run of 30-byte slots is byte `j` of slot `i`. -/
private theorem slots_byte (nodes : List (BitVec 256)) (i j : Nat) (inside : i < nodes.length) (small : j < 30) :
    (nodes.flatMap (fun x => Quartet.packedSlot x 0))[30*i+j]! = (Quartet.packedSlot (nodes[i]!) 0)[j]! := by
  induction nodes generalizing i with
  | nil => exact absurd inside (by simp)
  | cons x rest ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      have headNode : (x :: rest)[0]! = x := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero]
        rfl
      rw [Nat.mul_zero, Nat.zero_add, bang_append_left (by rw [Quartet.packed_slot_length]; omega), headNode]
    | succ k =>
      have width : (Quartet.packedSlot x 0).length = 30 := Quartet.packed_slot_length x 0
      have shift : 30*(k+1)+j = (Quartet.packedSlot x 0).length + (30*k+j) := by rw [width]; ring
      have tailNode : (x :: rest)[k+1]! = rest[k]! := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ]
      rw [shift, bang_append_right, ih k (by simpa using inside), tailNode]

/-- Memory holding `Quartet.packNodes nodes` at `start` decodes frontier node `i` to `pad238 nodes[i]`. -/
theorem cap_frontier_of_pack (state : MachineState) (start : Nat) (nodes : List (BitVec 256))
    (bytes : ∀ j < (Quartet.packNodes nodes).length,
      state.getByte (BitVec.ofNat 64 (start+j)) = (Quartet.packNodes nodes)[j]!)
    (i : Nat) (inside : i < nodes.length) :
    capFrontierValue state start i = pad238 (nodes[i]!) := by
  rw [Quartet.packNodes] at bytes
  by_cases long : 8 ≤ nodes.length
  · rw [if_pos long] at bytes
    have block : (Quartet.packEight (nodes.take 8)).length = 238 := Quartet.pack_eight_length _
    by_cases first : i < 8
    · -- node `i` sits in the first block
      have size : (nodes.take 8).length = 8 := by rw [List.length_take]; omega
      have inBlock : ∀ j < 238, state.getByte (BitVec.ofNat 64 (start+j)) =
          (Quartet.packEight (nodes.take 8))[j]! := by
        intro j small
        have whole : j < (Quartet.packEight (nodes.take 8) ++ Quartet.packNodes (nodes.drop 8)).length := by
          rw [List.length_append, block]; omega
        rw [bytes j whole, bang_append_left (by rw [block]; exact small)]
      have decoded := packed_node_of_bytes state start (nodes.take 8) size inBlock i first
      unfold capFrontierValue
      rw [show start+238*(i/8) = start by rw [Nat.div_eq_of_lt first]; ring, Nat.mod_eq_of_lt first, decoded,
        node_take first]
    · -- node `i` is node `i - 8` of the rest, one block further on
      have later : 8 ≤ i := by omega
      have rest : ∀ j < (Quartet.packNodes (nodes.drop 8)).length,
          state.getByte (BitVec.ofNat 64 ((start+238)+j)) = (Quartet.packNodes (nodes.drop 8))[j]! := by
        intro j small
        have whole : 238+j < (Quartet.packEight (nodes.take 8) ++ Quartet.packNodes (nodes.drop 8)).length := by
          rw [List.length_append, block]; omega
        have here := bytes (238+j) whole
        have idx : (Quartet.packEight (nodes.take 8) ++ Quartet.packNodes (nodes.drop 8))[238+j]! =
            (Quartet.packNodes (nodes.drop 8))[j]! := by
          have moved := bang_append_right (A := Quartet.packEight (nodes.take 8))
            (B := Quartet.packNodes (nodes.drop 8)) j
          rwa [block] at moved
        rw [show start+238+j = start+(238+j) by ring, here, idx]
      have smaller : i-8 < (nodes.drop 8).length := by rw [List.length_drop]; omega
      have decoded := cap_frontier_of_pack state (start+238) (nodes.drop 8) rest (i-8) smaller
      unfold capFrontierValue at decoded ⊢
      have offset : start+238+238*((i-8)/8) = start+238*(i/8) := by
        have q : i/8 = (i-8)/8 + 1 := by omega
        rw [q]; ring
      have residue : (i-8)%8 = i%8 := by omega
      rw [offset, residue, node_drop later] at decoded
      exact decoded
  · rw [if_neg long] at bytes
    have short : nodes.length < 8 := by omega
    -- a partial group: node `i` is a plain 30-byte slot
    have small : i < 8 := by omega
    have notLast : i % 8 ≠ 7 := by rw [Nat.mod_eq_of_lt small]; omega
    have inSlot : ∀ j < 30, state.getByte (BitVec.ofNat 64 ((start+30*i)+j)) =
        (Quartet.packedSlot (nodes[i]!) 0)[j]! := by
      intro j little
      have count : (nodes.flatMap (fun x => Quartet.packedSlot x 0)).length = 30*nodes.length := by
        rw [List.length_flatMap]
        simp only [Quartet.packed_slot_length, List.map_const', List.sum_replicate, smul_eq_mul]
        ring
      have whole : 30*i+j < (nodes.flatMap (fun x => Quartet.packedSlot x 0)).length := by rw [count]; omega
      rw [show start+30*i+j = start+(30*i+j) by ring, bytes (30*i+j) whole, slots_byte nodes i j inside little]
    have decoded := packed_slot_of_bytes state (start+30*i) (nodes[i]!) inSlot
    unfold capFrontierValue packedNodeAt
    rw [if_neg notLast, Nat.mod_eq_of_lt small, Nat.div_eq_of_lt small]
    rw [show start+238*0+30*i = start+30*i by ring]
    exact decoded
termination_by nodes.length
decreasing_by simp only [List.length_drop]; omega

end TwoPermutationPrototype.Packed.Checker
