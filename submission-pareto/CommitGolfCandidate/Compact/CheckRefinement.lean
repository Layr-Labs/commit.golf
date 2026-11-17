import CommitGolfCandidate.Compact.Programs
import CommitGolfCandidate.Compact.PathRefinement
import CommitGolfCandidate.Compact.BufferRefinement
import CommitGolfCandidate.HeapModel

/-! Functional refinement of the actual checker's complete position computation. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The per-position setup copies the proof salt into the leaf accumulator. -/
theorem check_position_salt (state : MachineState) (address : Nat)
    (scratch : state.getReg .x21 = 256) (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address%8 = 0) (above : 320 ≤ address) (bounded : address+32 < 2^64) :
    readBuffer (checkPositionState state) 256 32 = expandNonce192 (readBuffer state address 24) := by
  have indexScratch : (checkIndexState state).getReg .x21 = 256 := by
    simpa [checkIndexState, MachineState.getReg_setReg_ne] using scratch
  have indexPointer : (checkIndexState state).getReg .x25 = BitVec.ofNat 64 address := by
    simpa [checkIndexState, MachineState.getReg_setReg_ne] using pointer
  change readBuffer (checkPathCopyState (checkIndexState state) 15) 256 32 = _
  exact check_salt_copy_digest (checkIndexState state) address
    indexScratch indexPointer aligned above bounded

/-- The index load and salt copy preserve all words outside the accumulator. -/
theorem check_position_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkPositionState state).getMem address = state.getMem address := by
  change (checkPathCopyState (checkIndexState state) 15).getMem address = _
  exact check_salt_copy_outside (checkIndexState state) address
    (by simpa [checkIndexState, MachineState.getReg_setReg_ne] using scratch) outside

private theorem word_outside_scratch (address offset : Nat) (above : 320 ≤ address)
    (bounded : address+offset < 2^64) (i : Nat) (hi : i < 8) :
    BitVec.ofNat 64 (address+offset) ≠ BitVec.ofNat 64 (256+8*i) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at natural
  omega

private theorem check_path_setup_memory (state : MachineState) :
    (checkPathInitializedState state).mem = state.mem := rfl

attribute [local irreducible] checkPositionState checkLeafLoop checkPathLoop
  checkPathInitializedState checkEvaluation checkPositionHash

set_option maxRecDepth 4096 in
theorem check_position_hash_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (checkPositionHash state)).1 =
      (checkEvaluation oracle (checkPathLoop (checkPathInitializedState
        (((checkEvaluation oracle (checkLeafLoop
          (((checkPositionState state).setReg .x28 8).setPC 4448) 8)).1).setPC 4196)) 24)).1 := by
  rw [checkPositionHash, check_evaluation_bind]

set_option maxRecDepth 4096 in
private theorem finish_check_path (oracle : Oracle) (state leaf : MachineState)
    (proofAddress : Nat) (path : List (Bool × Digest)) (digest : Digest)
    (leafScratch : leaf.getReg .x21 = 256)
    (leafPointer : leaf.getReg .x25 = BitVec.ofNat 64 (proofAddress+24))
    (leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24))
    (leafOutside : ∀ address : Word,
      (∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) → leaf.getMem address = state.getMem address)
    (leafDigestEq : readBuffer leaf 256 32 = digest)
    (proofAligned : proofAddress%8 = 0) (proofAbove : 320 ≤ proofAddress)
    (proofBound : proofAddress+792 < 2^64) (pathLength : path.length = 24)
    (pathData : ∀ i (hi : i < path.length),
      readBuffer state (proofAddress+24+32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle
      (checkPathLoop (checkPathInitializedState (leaf.setPC 4196)) 24)).1 256 32 =
      climb oracle.compression digest path := by
  let pathReady := checkPathInitializedState (leaf.setPC 4196)
  have pathScratch : pathReady.getReg .x21 = 256 :=
    (check_path_setup_register (leaf.setPC 4196) .x21 (by decide)).trans leafScratch
  have pathPointer : pathReady.getReg .x25 = BitVec.ofNat 64 (proofAddress+24) :=
    (check_path_setup_register (leaf.setPC 4196) .x25 (by decide)).trans leafPointer
  have pathMemory (address : Word) : pathReady.getMem address = leaf.getMem address :=
    congrFun (check_path_setup_memory (leaf.setPC 4196)) address
  have afterData (i : Nat) (hi : i < path.length) :
      readBuffer pathReady (proofAddress+24+32*i) 32 = (path[i]'hi).2 := by
    have same : readBuffer pathReady (proofAddress+24+32*i) 32 =
        readBuffer state (proofAddress+24+32*i) 32 := by
      apply read_digest_congr _ _ _ (by omega)
      intro word hw
      rw [pathMemory]
      apply leafOutside
      intro j hj
      simpa only [Nat.add_assoc] using word_outside_scratch proofAddress (24+32*i+8*word) proofAbove
        (by rw [pathLength] at hi; omega) j hj
    exact same.trans (pathData i hi)
  have afterDirections (i : Nat) (hi : i < path.length) :
      (pathReady.getReg .x20).getLsbD i = (path[i]'hi).1 := by
    rw [check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC, leafIndex]
    exact directions i hi
  have folded := check_path_loop_digest oracle pathReady (proofAddress+24) path pathScratch pathPointer
    (by omega) (by omega) (by rw [pathLength]; omega) afterData afterDirections
  have startDigest : readBuffer pathReady 256 32 = digest := by
    have same : readBuffer pathReady 256 32 = readBuffer leaf 256 32 := by
      apply read_digest_congr _ _ _ (by decide)
      intro word hw
      exact pathMemory _
    exact same.trans leafDigestEq
  have sameLength := congrArg (fun count =>
    readBuffer (checkEvaluation oracle (checkPathLoop pathReady count)).1 256 32) pathLength.symm
  exact sameLength.trans (folded.trans
    (congrArg (fun value => climb oracle.compression value path) startDigest))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- One complete checker iteration computes the submitted leaf digest and folds its
24 supplied siblings in the direction determined by the submitted position. -/
theorem check_position_hash_digest (oracle : Oracle) (state : MachineState)
    (valueAddress proofAddress : Nat) (value : Entry) (salt : Digest) (path : List (Bool × Digest))
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress%8 = 0) (proofAligned : proofAddress%8 = 0)
    (valueAbove : 320 ≤ valueAddress) (proofAbove : 320 ≤ proofAddress)
    (valueBound : valueAddress+256 < 2^64) (proofBound : proofAddress+792 < 2^64)
    (saltData : expandNonce192 (readBuffer state proofAddress 24) = salt)
    (valueData : ∀ block < 8, readBuffer state (valueAddress+32*block) 32 =
      value.extractLsb' (256*block) 256)
    (pathLength : path.length = 24)
    (pathData : ∀ i (hi : i < path.length),
      readBuffer state (proofAddress+24+32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1) :
    readBuffer (checkEvaluation oracle (checkPositionHash state)).1 256 32 =
      climb oracle.compression (leafDigest oracle.compression salt value) path := by
  let ready := ((checkPositionState state).setReg .x28 8).setPC 4448
  let leaf := (checkEvaluation oracle (checkLeafLoop ready 8)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have readyPointer : ready.getReg .x8 = BitVec.ofNat 64 valueAddress :=
    (check_position_register state .x8 (by decide)).trans valuePointer
  have readySalt : readBuffer ready 256 32 = salt :=
    (check_position_salt state proofAddress scratch proofPointer proofAligned proofAbove (by omega)).trans saltData
  have readyOutside (address : Word) (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+8*i)) :
      ready.getMem address = state.getMem address := check_position_outside state address scratch outside
  have readyData (block : Nat) (hb : block < 8) :
      readBuffer ready (valueAddress+32*block) 32 = value.extractLsb' (256*block) 256 := by
    have same : readBuffer ready (valueAddress+32*block) 32 =
        readBuffer state (valueAddress+32*block) 32 := by
      apply read_digest_congr _ _ _ (by omega)
      intro word hw
      apply readyOutside
      intro i hi
      simpa only [Nat.add_assoc] using word_outside_scratch valueAddress (32*block+8*word) valueAbove (by omega) i (by omega)
    exact same.trans (valueData block hb)
  have leafDigestEq : readBuffer leaf 256 32 = leafDigest oracle.compression salt value :=
    check_leaf_digest oracle ready valueAddress salt value readyScratch readyPointer
      valueAligned valueAbove valueBound readySalt readyData
  have leafRegs := check_leaf_loop_registers ready 8 leaf (check_evaluation_support oracle _)
  have leafScratch : leaf.getReg .x21 = 256 := (leafRegs.2 .x21 (by decide)).trans readyScratch
  have leafPointer : leaf.getReg .x25 = BitVec.ofNat 64 (proofAddress+24) := by
    rw [leafRegs.2 .x25 (by decide)]
    change (checkPositionState state).getReg .x25 = _
    rw [check_position_proof_pointer, proofPointer]
    exact (BitVec.ofNat_add proofAddress 24).symm
  have leafIndex : leaf.getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [leafRegs.2 .x20 (by decide)]
    exact check_position_index state
  have leafOutside (address : Word) (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
      leaf.getMem address = state.getMem address :=
    (check_leaf_loop_outside oracle ready 8 address readyScratch outside).trans
      (readyOutside address (fun i hi => outside i (by omega)))
  rw [check_position_hash_evaluation]
  exact finish_check_path oracle state leaf proofAddress path _ leafScratch leafPointer leafIndex
    leafOutside leafDigestEq proofAligned proofAbove proofBound pathLength pathData directions

private theorem check_path_phase_outside (oracle : Oracle) (leaf : MachineState) (address : Word)
    (scratch : leaf.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle
      (checkPathLoop (checkPathInitializedState (leaf.setPC 4196)) 24)).1.getMem address =
        leaf.getMem address := by
  have pathScratch : (checkPathInitializedState (leaf.setPC 4196)).getReg .x21 = 256 :=
    (check_path_setup_register (leaf.setPC 4196) .x21 (by decide)).trans scratch
  exact (check_path_loop_outside oracle (checkPathInitializedState (leaf.setPC 4196))
    24 address pathScratch outside).trans
      (congrFun (check_path_setup_memory (leaf.setPC 4196)) address)

set_option maxRecDepth 4096 in
/-- Computing one position does not modify any input buffer or the supplied root. -/
theorem check_position_hash_outside (oracle : Oracle) (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (checkEvaluation oracle (checkPositionHash state)).1.getMem address = state.getMem address := by
  let ready := ((checkPositionState state).setReg .x28 8).setPC 4448
  let leaf := (checkEvaluation oracle (checkLeafLoop ready 8)).1
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have leafScratch : leaf.getReg .x21 = 256 :=
    ((check_leaf_loop_registers ready 8 leaf (check_evaluation_support oracle _)).2 .x21 (by decide)).trans
      readyScratch
  have initialMemory : ready.getMem address = state.getMem address :=
    check_position_outside state address scratch (fun i hi => outside i (by omega))
  have leafMemory := check_leaf_loop_outside oracle ready 8 address readyScratch outside
  rw [check_position_hash_evaluation]
  exact (check_path_phase_outside oracle leaf address leafScratch outside).trans
    (leafMemory.trans initialMemory)

/-- The four machine-word comparisons are exactly a digest equality. The root on
its right is still the supplied root, not an overwritten copy in scratch memory. -/
theorem check_position_comparison (oracle : Oracle) (state : MachineState) (rootAddress : Nat)
    (scratch : state.getReg .x21 = 256)
    (rootPointer : state.getReg .x26 = BitVec.ofNat 64 rootAddress)
    (rootAligned : rootAddress%8 = 0) (rootAbove : 320 ≤ rootAddress)
    (rootBound : rootAddress+32 < 2^64) :
    let hashed := (checkEvaluation oracle (checkPositionHash state)).1
    (∀ word < 4, hashed.getMem (hashed.getReg .x21+BitVec.ofNat 64 (8*word)) =
      hashed.getMem (hashed.getReg .x26+BitVec.ofNat 64 (8*word))) ↔
    readBuffer hashed 256 32 = readBuffer state rootAddress 32 := by
  let hashed := (checkEvaluation oracle (checkPositionHash state)).1
  have regs := check_position_hash_registers state hashed (check_evaluation_support oracle _)
  have hashedScratch : hashed.getReg .x21 = 256 := (regs.2.2.2 .x21 (by simp)).trans scratch
  have hashedRoot : hashed.getReg .x26 = BitVec.ofNat 64 rootAddress :=
    (regs.2.2.2 .x26 (by simp)).trans rootPointer
  have rootMemory : readBuffer hashed rootAddress 32 = readBuffer state rootAddress 32 := by
    apply read_digest_congr _ _ _ rootAligned
    intro word hw
    apply check_position_hash_outside oracle state _ scratch
    intro i hi
    exact word_outside_scratch rootAddress (8*word) rootAbove (by omega) i hi
  change (∀ word < 4, hashed.getMem (hashed.getReg .x21+BitVec.ofNat 64 (8*word)) =
    hashed.getMem (hashed.getReg .x26+BitVec.ofNat 64 (8*word))) ↔ _
  rw [← rootMemory, read_digest_eq_iff _ _ _ _ (by decide) rootAligned]
  constructor <;> intro words word hw
  · have agree := words word hw
    rw [hashedScratch, hashedRoot] at agree
    change hashed.getMem (BitVec.ofNat 64 256+BitVec.ofNat 64 (8*word)) = _ at agree
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add] at agree
    exact agree
  · have agree := words word hw
    rw [hashedScratch, hashedRoot]
    change hashed.getMem (BitVec.ofNat 64 256+BitVec.ofNat 64 (8*word)) = _
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact agree

/-- With a consistent commitment heap, the actual checker reconstructs its root
from the leaf salt and the siblings copied by opening. -/
theorem check_position_heap_root (oracle : Oracle) (state : MachineState)
    (valueAddress proofAddress : Nat) (value : Entry) (salt : Digest)
    (heap : Nat → Digest) (index : Index)
    (scratch : state.getReg .x21 = 256)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (proofPointer : state.getReg .x25 = BitVec.ofNat 64 proofAddress)
    (valueAligned : valueAddress%8 = 0) (proofAligned : proofAddress%8 = 0)
    (valueAbove : 320 ≤ valueAddress) (proofAbove : 320 ≤ proofAddress)
    (valueBound : valueAddress+256 < 2^64) (proofBound : proofAddress+792 < 2^64)
    (saltData : expandNonce192 (readBuffer state proofAddress 24) = salt)
    (valueData : ∀ block < 8, readBuffer state (valueAddress+32*block) 32 =
      value.extractLsb' (256*block) 256)
    (indexData : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index.val)
    (pathData : ∀ level < 24, readBuffer state (proofAddress+24+32*level) 32 =
      heap (((2^24+index.val)/2^level) ^^^ 1))
    (leafData : heap (2^24+index.val) = leafDigest oracle.compression salt value)
    (parents : ∀ parent, 0 < parent → parent < 2^24 →
      heap parent = combine oracle.compression (heap (2*parent)) (heap (2*parent+1))) :
    readBuffer (checkEvaluation oracle (checkPositionHash state)).1 256 32 = heap 1 := by
  let path := heapPath heap (2^24+index.val) 24
  have pathLength : path.length = 24 := heap_path_length _ _ _
  have data (i : Nat) (hi : i < path.length) :
      readBuffer state (proofAddress+24+32*i) 32 = (path[i]'hi).2 := by
    have below : i < 24 := by rw [pathLength] at hi; exact hi
    have entry := heap_path_get heap (2^24+index.val) 24 i below
    change readBuffer state (proofAddress+24+32*i) 32 =
      ((heapPath heap (2^24+index.val) 24)[i]'hi).2
    rw [entry]
    exact pathData i below
  have directions (i : Nat) (hi : i < path.length) :
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'hi).1 := by
    have below : i < 24 := by rw [pathLength] at hi; exact hi
    have entry := heap_path_get heap (2^24+index.val) 24 i below
    change (state.getMem (state.getReg .x24)).getLsbD i =
      ((heapPath heap (2^24+index.val) 24)[i]'hi).1
    rw [entry, indexData, BitVec.getLsbD_ofNat,
      heap_leaf_direction 24 index.val i index.isLt below]
    simp only [show i < 64 by omega, decide_true, Bool.true_and]
  have hashed := check_position_hash_digest oracle state valueAddress proofAddress value salt path
    scratch valuePointer proofPointer valueAligned proofAligned valueAbove proofAbove valueBound proofBound
    saltData valueData pathLength data directions
  exact hashed.trans ((congrArg (fun digest => climb oracle.compression digest path) leafData.symm).trans
    (reconstruct_heap_root oracle.compression heap 24 index.val index.isLt parents))

end CommitGolfCandidate.Compact
