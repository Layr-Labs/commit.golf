import CommitGolfCandidate.CapCheckLowerRecordSemantics
import CommitGolfCandidate.CapLowerReplay

/-! The logical paid-replay record is exactly the record authenticated by
the physical lower macro when its salt, sixteen sibling slots and value
blocks have the specified bytes. Actual ABI parsing supplies these premises
separately; this theorem introduces no new acceptance rule. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_lower_logical_digest (oracle : Oracle) (state : MachineState)
    (record : CapLowerRecord) (saltAddress valueAddress : Nat)
    (scratch : state.getReg .x21 = 256)
    (saltPointer : state.getReg .x25 = BitVec.ofNat 64 saltAddress)
    (valuePointer : state.getReg .x8 = BitVec.ofNat 64 valueAddress)
    (indexWord : state.getMem (state.getReg .x24) = BitVec.ofNat 64 record.index.val)
    (saltAligned : saltAddress % 8 = 0) (saltAbove : 320 ≤ saltAddress)
    (saltBound : saltAddress + 544 < 2^64)
    (valueAligned : valueAddress % 8 = 0) (valueAbove : 320 ≤ valueAddress)
    (valueBound : valueAddress + 256 < 2^64)
    (salt : readBuffer state saltAddress 32 = record.salt)
    (values : ∀ i < 8, readBuffer state (valueAddress + 32*i) 32 =
      record.value.extractLsb' (256*i) 256)
    (siblings : ∀ i : Fin 16,
      readBuffer state (saltAddress + 32 + 32*i.val) 32 = record.sibling i) :
    readBuffer (checkEvaluation oracle (capCheckLowerRecord state)).1 256 32 =
      record.root oracle.compression oracle.permutation := by
  rw [CapLowerRecord.root]
  have result := cap_check_lower_record_digest oracle state saltAddress valueAddress
    record.value record.path (cap_lower_path_length record) scratch saltPointer
    valuePointer saltAligned saltAbove saltBound valueAligned valueAbove valueBound
    values (by
      intro i inside
      have bounded : i < 16 := by simpa only [cap_lower_path_length] using inside
      simpa only [CapLowerRecord.path,List.getElem_ofFn] using siblings ⟨i,bounded⟩)
    (by
      intro i inside
      have bounded : i < 16 := by simpa only [cap_lower_path_length] using inside
      rw [indexWord,BitVec.getLsbD_ofNat]
      simp only [CapLowerRecord.path,List.getElem_ofFn,
        show decide (i < 64) = true from decide_eq_true (by omega),Bool.true_and])
  rw [salt] at result
  exact result

end CommitGolfCandidate
