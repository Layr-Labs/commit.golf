import CommitGolfCandidate.CapCheckRecordLeafWords

/-! Fixed-oracle semantics of the checked salt and leaf macro. The salt is read
from the admitted proof slot, while the value consists of the eight original
message blocks. Input separation is explicit; no hash injectivity is assumed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capCheckRecordLeafStart
  checkEvaluation capCheckLeaf

private theorem read_pc (state : MachineState) (pc : Word) :
    readBuffer (state.setPC pc) 256 32 = readBuffer state 256 32 :=
  read_buffer_memory_congr (state.setPC pc) state rfl 256 32

theorem cap_check_record_leaf_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (capCheckRecordLeaf state) =
      ((checkEvaluation oracle (capCheckLeaf (capCheckRecordLeafStart state))).1.setPC 4256,
       (checkEvaluation oracle (capCheckLeaf (capCheckRecordLeafStart state))).2) := by
  unfold capCheckRecordLeaf
  rw [check_evaluation_bind]
  simp only [check_evaluation_pure, Nat.add_zero]

theorem cap_check_record_leaf_start_salt (state : MachineState) (saltAddress : Nat)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 saltAddress)
    (aligned : saltAddress % 8 = 0) (above : 320 ≤ saltAddress)
    (bounded : saltAddress + 32 < 2^64) :
    readBuffer (capCheckRecordLeafStart state) 256 32 =
      readBuffer state saltAddress 32 :=
  (read_buffer_memory_congr _ _ (cap_check_record_leaf_start_memory state) 256 32).trans
    (cap_check_salt_digest state saltAddress scratch pointer aligned above bounded)

theorem cap_check_record_leaf_start_value (state : MachineState)
    (scratch : state.getReg .x21 = 256) (address : Nat)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 < 2^64) :
    readBuffer (capCheckRecordLeafStart state) address 32 = readBuffer state address 32 := by
  apply (read_buffer_memory_congr _ _
    (cap_check_record_leaf_start_memory state) address 32).trans
  apply read_digest_congr _ _ _ aligned
  intro word inside
  apply cap_check_salt_outside _ _ scratch
  intro i hi equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address + 8*word < 2^64),
    Nat.mod_eq_of_lt (by omega : 256+8*i < 2^64)] at numeric
  omega

theorem cap_check_record_leaf_digest (oracle : Oracle) (state : MachineState)
    (saltAddress valueAddress : Nat) (value : Entry)
    (scratch : state.getReg .x21 = 256)
    (saltPointer : state.getReg .x25 = BitVec.ofNat 64 saltAddress)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (saltAligned : saltAddress % 8 = 0) (saltAbove : 320 ≤ saltAddress)
    (saltBound : saltAddress + 32 < 2^64)
    (valueAligned : valueAddress % 8 = 0) (valueAbove : 320 ≤ valueAddress)
    (valueBound : valueAddress + 256 < 2^64)
    (data : ∀ i < 8, readBuffer state (valueAddress + 32*i) 32 =
      value.extractLsb' (256*i) 256) :
    readBuffer (checkEvaluation oracle (capCheckRecordLeaf state)).1 256 32 =
      s3LeafDigest oracle.permutation (readBuffer state saltAddress 32) value := by
  rw [cap_check_record_leaf_evaluation]
  have pcMemory : readBuffer
      ((checkEvaluation oracle (capCheckLeaf (capCheckRecordLeafStart state))).1.setPC 4256)
      256 32 =
      readBuffer (checkEvaluation oracle (capCheckLeaf (capCheckRecordLeafStart state))).1
        256 32 := read_pc _ _
  rw [pcMemory]
  apply cap_check_leaf_digest oracle (capCheckRecordLeafStart state)
    valueAddress (readBuffer state saltAddress 32) value
  · exact (cap_check_record_leaf_start_register state .x8 (by decide)).trans valuePointer
  · exact valueAligned
  · exact valueAbove
  · exact valueBound
  · exact cap_check_record_leaf_start_salt state saltAddress scratch saltPointer
      saltAligned saltAbove saltBound
  · intro i inside
    rw [cap_check_record_leaf_start_value state scratch _ (by omega) (by omega) (by omega)]
    exact data i inside

end CommitGolfCandidate
