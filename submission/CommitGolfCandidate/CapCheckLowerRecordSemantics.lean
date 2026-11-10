import CommitGolfCandidate.CapCheckLowerRecordFrame
import CommitGolfCandidate.CapCheckRecordLeafDigest
import CommitGolfCandidate.CapCheckPathSemantics

/-! Fixed-oracle lower-record refinement: the exact loaded salt and value
produce a leaf digest, followed by the seventeen serialized siblings in index
bit order. Earlier scratch writes cannot alter those later proof slots. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer checkEvaluation capCheckPathLoop
  capCheckPathInitPrefix capCheckRecordLeaf

theorem cap_check_lower_record_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (capCheckLowerRecord state)).1 =
      (checkEvaluation oracle (capCheckPathLoop
        (capCheckPathInitState (checkEvaluation oracle (capCheckRecordLeaf state)).1) 17)).1 := by
  unfold capCheckLowerRecord
  rw [check_evaluation_bind]

theorem cap_check_lower_leaf_read (state leaf : MachineState)
    (scratch : state.getReg .x21 = 256)
    (reachable : leaf ∈ support (capCheckRecordLeaf state))
    (address : Nat) (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address+32 < 2^64) :
    readBuffer (capCheckPathInitState leaf) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (cap_check_path_init_memory leaf) address 32]
  apply read_digest_congr _ _ _ aligned
  intro word inside
  apply cap_check_record_leaf_word_frame state leaf scratch reachable
  intro i hi equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address+8*word < 2^64),
    Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at numeric
  omega

theorem cap_check_lower_record_digest (oracle : Oracle) (state : MachineState)
    (saltAddress valueAddress : Nat) (value : Entry) (path : List (Bool × Digest))
    (length : path.length = 17)
    (scratch : state.getReg .x21 = 256)
    (saltPointer : state.getReg .x25 = BitVec.ofNat 64 saltAddress)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (saltAligned : saltAddress % 8 = 0) (saltAbove : 320 ≤ saltAddress)
    (saltBound : saltAddress+576 < 2^64)
    (valueAligned : valueAddress % 8 = 0) (valueAbove : 320 ≤ valueAddress)
    (valueBound : valueAddress+256 < 2^64)
    (data : ∀ i < 8, readBuffer state (valueAddress+32*i) 32 =
      value.extractLsb' (256*i) 256)
    (siblings : ∀ i (inside : i < path.length),
      readBuffer state (saltAddress+32+32*i) 32 = (path[i]'inside).2)
    (directions : ∀ i (inside : i < path.length),
      (state.getMem (state.getReg .x24)).getLsbD i = (path[i]'inside).1) :
    readBuffer (checkEvaluation oracle (capCheckLowerRecord state)).1 256 32 =
      climb oracle.compression
        (leafDigest oracle.compression (readBuffer state saltAddress 32) value) path := by
  let leaf := (checkEvaluation oracle (capCheckRecordLeaf state)).1
  have reachable : leaf ∈ support (capCheckRecordLeaf state) :=
    check_evaluation_support oracle _
  have readyScratch : (capCheckPathInitState leaf).getReg .x21 = 256 := by
    rw [cap_check_path_init_state_register leaf .x21 (by decide),
      cap_check_record_leaf_register state leaf reachable .x21 (by decide)]
    exact scratch
  have readyPointer : (capCheckPathInitState leaf).getReg .x25 =
      BitVec.ofNat 64 (saltAddress+32) := by
    rw [cap_check_path_init_state_register leaf .x25 (by decide),
      cap_check_record_leaf_cursor state leaf reachable, saltPointer, BitVec.ofNat_add]
    rfl
  have pathData (i : Nat) (inside : i < path.length) :
      readBuffer (capCheckPathInitState leaf) (saltAddress+32+32*i) 32 =
        (path[i]'inside).2 := by
    rw [cap_check_lower_leaf_read state leaf scratch reachable _ (by omega)
      (by omega) (by rw [length] at inside; omega)]
    exact siblings i inside
  have pathDirections (i : Nat) (inside : i < path.length) :
      ((capCheckPathInitState leaf).getReg .x20).getLsbD i = (path[i]'inside).1 := by
    rw [cap_check_path_init_state_register leaf .x20 (by decide),
      cap_check_record_leaf_index state leaf reachable]
    exact directions i inside
  rw [cap_check_lower_record_evaluation, ← length]
  rw [cap_check_path_loop_digest oracle (capCheckPathInitState leaf) (saltAddress+32)
    path readyScratch readyPointer (by omega) (by omega) (by rw [length]; omega)
    pathData pathDirections]
  rw [read_buffer_memory_congr _ _ (cap_check_path_init_memory leaf) 256 32]
  rw [cap_check_record_leaf_digest oracle state saltAddress valueAddress value scratch
    saltPointer valuePointer saltAligned saltAbove (by omega) valueAligned valueAbove
    valueBound data]

end CommitGolfCandidate
