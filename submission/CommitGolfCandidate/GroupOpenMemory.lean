import RiscvZkvm.Rv64.Bytes
import CommitGolfCandidate.TwoPermutationOpeningGeometry
import CommitGolfCandidate.GroupOpenContext

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

def trapdoorBase : Nat := 4096 + 256 * LENGTH + 32
def trapdoorBytes : Nat := 304 * LENGTH
def nonceBase : Nat := trapdoorBase + 288 * LENGTH
def indicesBase : Nat := trapdoorBase + trapdoorBytes
def proofBase : Nat := indicesBase + 8 * LENGTH + 64 + 256 * LENGTH
def proofCapacity : Nat := 534 * LENGTH + 7680

theorem heap_before_nonces : trapdoorBase+64*LENGTH ≤ nonceBase := by decide
theorem nonces_end_at_indices : nonceBase+16*LENGTH = indicesBase := by decide
theorem indices_before_records : indicesBase+8*LENGTH ≤ proofBase := by decide
theorem actual_proof_base : proofBase = quartetProofBase := rfl

def groupSlots : Nat := trapdoorBase+32*LENGTH

/-- Leaf digest `i` as the writer reads it: from the block the prefix rebuilt (inverse group reply) at
`groupSlots + 512 + 1024 ⌊i/4⌋`. -/
def leafAddress (i : Nat) : Nat :=
  groupSlots + 512 + 1024 * (i/4) + 72 + 32 * (i%4)

/-- The commit's level-22 node of the sibling quartet of leaf `i`'s quartet `q = i/4`: inside the group replies of
the pair `2 (q/2)`, at `B+136` of the even block for even `q` (node of `q+1`) and at `B+168` of the even block for
odd `q` (node of `q-1`). -/
def quadAddress (i : Nat) : Nat :=
  groupSlots + 1024 * (2 * (i/4/2)) + 136 + 32 * (i/4%2)

/-- The pointer word after the rebuilt block of leaf `i`'s quartet (`B_q + 712`). -/
def pointerAddress (i : Nat) : Nat :=
  groupSlots + 1024 * (i/4) + 712

def upperNode (index : Index) (level : Nat) : Nat := Opening.lowerNode index (level+2)

theorem upper_node_zero (index : Index) : upperNode index 0 = 4194304+index.val/4 := by
  unfold upperNode Opening.lowerNode LENGTH LOG_LENGTH
  omega

theorem upper_node_next (index : Index) (level : Nat) :
    upperNode index (level+1) = upperNode index level / 2 :=
  Opening.lower_node_next index (level+2)

theorem upper_node_bound (index : Index) (level : Nat) : upperNode index level < 2*LENGTH :=
  Opening.lower_node_bound index (level+2)

theorem upper_swap_bound (index : Index) (level : Nat) : upperNode index level ^^^ 1 < 2*LENGTH :=
  Opening.lower_swap_bound index (level+2)

theorem upper_node_heap_index (index : Index) (level : Nat) :
    upperNode index level = (4194304+index.val/4)/2^level := by
  induction level with
  | zero => simpa using upper_node_zero index
  | succ level ih =>
    rw [upper_node_next, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem upper_final_group (index : Index) : upperNode index 14 = Sampling.capGroup index := rfl

def SameOpeningInput (before after : MachineState) : Prop :=
  ∀ address : Nat, trapdoorBase ≤ address → address < proofBase → address%8=0 →
    after.getMem (BitVec.ofNat 64 address) = before.getMem (BitVec.ofNat 64 address)

theorem aligned_word_mod (w : Word) : (alignToDword w).toNat%8=0 := by
  have h := alignToDword_byteOffset_zero w
  change ((alignToDword w) &&& 7#64).toNat=0 at h
  rw [BitVec.toNat_and] at h
  change (alignToDword w).toNat &&& (2^3-1)=0 at h
  rwa [Nat.and_two_pow_sub_one_eq_mod] at h

structure OpeningLayout (s : Submission) : Prop where
  trapdoor : s.layout.trapdoor = trapdoorBase
  trapdoorSize : s.sizes.trapdoor = trapdoorBytes
  indices : s.layout.indices = indicesBase
  proof : s.layout.proof = proofBase

private theorem index_word (index : Index) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (BitVec.ofNat 8 (index.val / 2 ^ (8 * j))).toNat * 2 ^ (8 * j)) =
      BitVec.ofNat 64 index.val := by
  congr 1
  have bounded : index.val < 16777216 := index.isLt
  norm_num [Finset.sum_range_succ, BitVec.toNat_ofNat]
  omega

/-- The ABI's ordinal is the offset in the sorted set. The nonce is subsequently
addressed by the position value, independently of that ordinal. -/
theorem input_index (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (bounded : ordinal < positions.card) :
    (s.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (indicesBase + 8 * ordinal)) =
      BitVec.ofNat 64 ((positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)).val := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  erw [initial_input_word s .opening (trapdoor, positions) _ (by
    norm_num [indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH] at cardinal ⊢
    omega)]
  have bytes (j : Nat) (hj : j < 8) :
      inputByte s .opening (trapdoor, positions) (indicesBase + 8 * ordinal + j) =
        BitVec.ofNat 8 (((positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)).val /
          2 ^ (8 * j)) := by
    have before : ¬ (trapdoorBase ≤ indicesBase + 8 * ordinal + j ∧
        indicesBase + 8 * ordinal + j < trapdoorBase + (8 * trapdoorBytes + 7) / 8) := by
      norm_num [indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH]
      omega
    have inside : indicesBase ≤ indicesBase + 8 * ordinal + j ∧
        indicesBase + 8 * ordinal + j <
          indicesBase + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      omega
    have quotient : (indicesBase + 8 * ordinal + j - indicesBase) / 8 = ordinal := by omega
    have remainder : (indicesBase + 8 * ordinal + j - indicesBase) % 8 = j := by omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      layout.trapdoor, layout.trapdoorSize, layout.indices, before, inside, decide_false,
      and_true, decide_true]
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using bounded)]
  refine (congrArg (BitVec.ofNat 64) (Finset.sum_congr rfl fun j hj => ?_)).trans (index_word _)
  rw [bytes j (Finset.mem_range.mp hj)]

/-- Any slice within the serialized private state can be read at its exact offset. -/
theorem input_trapdoor_slice (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (offset bytes : Nat) (inside : offset + bytes ≤ trapdoorBytes) :
    readBuffer (s.initialState .opening (trapdoor, positions)) (trapdoorBase + offset) bytes =
      trapdoor.extractLsb' (8 * offset) (8 * bytes) := by
  apply read_serialized_slice
  intro j hj
  have bound : trapdoorBase + offset + j < 2 ^ 64 := by
    norm_num [trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH] at inside ⊢
    omega
  erw [initial_input_byte s .opening (trapdoor, positions) _ bound]
  have covered : trapdoorBase ≤ trapdoorBase + offset + j ∧
      trapdoorBase + offset + j < trapdoorBase + (8 * trapdoorBytes + 7) / 8 := by omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    layout.trapdoor, layout.trapdoorSize, covered, and_true, decide_true]
  rw [show trapdoorBase + offset + j - trapdoorBase = offset + j by omega]

/-- Sixteen bytes at a leaf's original vector index recover that leaf's nonce. -/
theorem input_nonce (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (index : Index) :
    readBuffer (s.initialState .opening (trapdoor, positions)) (nonceBase + 16 * index.val) 16 =
      trapdoor.extractLsb' (8 * (288 * LENGTH + 16 * index.val)) 128 := by
  rw [nonceBase, Nat.add_assoc]
  exact input_trapdoor_slice s layout trapdoor positions _ _ (by
    have bounded := index.isLt
    unfold trapdoorBytes
    omega)

/-- The entire heap occupies 64N bytes, before the nonce region at 80N. -/
theorem input_digest (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (node : Nat) (bounded : node < 2 * LENGTH) :
    readBuffer (s.initialState .opening (trapdoor, positions)) (trapdoorBase + 32 * node) 32 =
      trapdoor.extractLsb' (256 * node) 256 := by
  have offset : 8 * (32 * node) = 256 * node := by omega
  rw [← offset]
  exact input_trapdoor_slice s layout trapdoor positions _ _ (by unfold trapdoorBytes; omega)

theorem leaf_address_inside (i : Nat) (valid : i < LENGTH) :
    leafAddress i % 8 = 0 ∧ trapdoorBase ≤ leafAddress i ∧ leafAddress i+32 ≤ nonceBase := by
  have hb : trapdoorBase % 8 = 0 := by decide
  unfold leafAddress groupSlots nonceBase
  unfold LENGTH LOG_LENGTH at *
  omega

theorem input_leaf (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (i : Nat) (inside : i<LENGTH) :
    readBuffer (s.initialState .opening (trapdoor,positions)) (leafAddress i) 32 =
      trapdoor.extractLsb' (8*(32*LENGTH + 512 + 1024*(i/4) + 72 +32*(i%4))) 256 := by
  let off := 32*LENGTH + 512 + 1024*(i/4) + 72 +32*(i%4)
  have physical : leafAddress i = trapdoorBase+off := by unfold leafAddress groupSlots off; omega
  rw [physical]
  apply input_trapdoor_slice s layout trapdoor positions
  unfold off trapdoorBytes
  unfold LENGTH LOG_LENGTH at *
  omega

theorem quad_address_inside (i : Nat) (valid : i < LENGTH) :
    quadAddress i % 8 = 0 ∧ trapdoorBase ≤ quadAddress i ∧ quadAddress i+32 ≤ nonceBase := by
  have hb : trapdoorBase % 8 = 0 := by decide
  unfold quadAddress groupSlots nonceBase
  unfold LENGTH LOG_LENGTH at *
  omega

theorem pointer_address_inside (i : Nat) (valid : i < LENGTH) :
    pointerAddress i % 8 = 0 ∧ trapdoorBase ≤ pointerAddress i ∧ pointerAddress i+8 ≤ nonceBase := by
  have hb : trapdoorBase % 8 = 0 := by decide
  unfold pointerAddress groupSlots nonceBase
  unfold LENGTH LOG_LENGTH at *
  omega

theorem input_quad (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (i : Nat) (inside : i<LENGTH) :
    readBuffer (s.initialState .opening (trapdoor,positions)) (quadAddress i) 32 =
      trapdoor.extractLsb' (8*(quadAddress i-trapdoorBase)) 256 := by
  have facts := quad_address_inside i inside
  have physical : quadAddress i = trapdoorBase+(quadAddress i-trapdoorBase) := by omega
  rw [physical]
  rw [show trapdoorBase+(quadAddress i-trapdoorBase)-trapdoorBase=quadAddress i-trapdoorBase by omega]
  apply input_trapdoor_slice s layout trapdoor positions
  have n : nonceBase ≤ trapdoorBase+trapdoorBytes := by decide
  omega

end TwoPermutationPrototype.GroupedOpening
