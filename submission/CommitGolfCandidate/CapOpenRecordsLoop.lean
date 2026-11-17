import CommitGolfCandidate.CapOpenRecordsNext
import CommitGolfCandidate.CostedCountedLoop

/-! Actual counted record pass, with no compression queries. Every callback
derives the index load from the retained reference interval and checks the
salt/output ranges. The zero residual is the already-reached mark-header PC,
not the opening ABI's separate empty-request branch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

private theorem word_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address+8 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, bounded, aligned, decide_true, Bool.true_and]

theorem cap_open_records_loop_execute (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+544*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records reference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records reference remaining state)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (219*remaining+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capCountedRun capOpenRecordState remaining state) allowCoins
          return result.charge (222*remaining) 0) := by
  apply cap_counted_run_execute_costed _ 219 222 capOpenRecordState
    (CapOpenRecordsReady context records reference)
    (fun residual current currentReady =>
      cap_open_records_ready_next context records reference current residual
        countBound indexSpace outputSpace inputs currentReady) ?_ remaining state ready
        fuel allowCoins
  intro residual current currentReady extra coins
  have bounded := currentReady.bounded
  have ordinalBound : records.length-(residual+1) < records.length := by omega
  let position := (records[records.length-(residual+1)]'ordinalBound).val
  let cursor := context.output+544*(records.length-(residual+1))
  let indexAddress := context.indices+8*(records.length-(residual+1))
  have positionBound : position < 16777216 := by
    simpa only [position, LENGTH, LOG_LENGTH, Nat.reducePow] using
      (records[records.length-(residual+1)]'ordinalBound).isLt
  have loaded : current.getMem (current.getReg .x24) = BitVec.ofNat 64 position :=
    cap_open_records_loaded context records reference current residual
      indexSpace inputs currentReady
  have indexAligned : indexAddress % 8 = 0 := by
    have base := context.indexAligned
    dsimp only [indexAddress]
    omega
  have outputBound := context.limitBound
  have indexBound : indexAddress+8 ≤ MEMORY_BYTES := by
    dsimp only [indexAddress]
    omega
  have indexValid : accessValid (current.getReg .x24) 8 = true := by
    rw [currentReady.indices]
    exact word_access indexAddress indexAligned indexBound
  have saltBound := context.saltBound
  have outputAligned := context.outputAligned
  apply cap_open_record_execute current position context.roots context.salts cursor
    context.limit (by simpa using currentReady.pc) indexValid loaded positionBound
    currentReady.roots context.rootAligned context.rootBound currentReady.salts
    context.saltAligned (by omega) currentReady.cursor
    (by dsimp only [cursor]; omega) (by dsimp only [cursor]; omega)
    context.limitBound currentReady.leaves currentReady.marks currentReady.nonceStride extra coins

theorem cap_open_records_loop_finished (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+544*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records reference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records reference remaining state) :
    CapOpenRecordsReady context records reference 0
      (capCountedRun capOpenRecordState remaining state) := by
  exact cap_counted_run_ready capOpenRecordState (CapOpenRecordsReady context records reference)
    (fun residual current currentReady =>
      cap_open_records_ready_next context records reference current residual
        countBound indexSpace outputSpace inputs currentReady) remaining state ready

end CommitGolfCandidate
