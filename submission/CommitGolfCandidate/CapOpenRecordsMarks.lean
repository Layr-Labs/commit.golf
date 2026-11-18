import CommitGolfCandidate.CapOpenRecordMarks
import CommitGolfCandidate.CapOpenRecordsNext

/-! Occupancy refinement of the actual counted opening records. The ghost mark
fold follows the same forward ordinal as the index loads. It records a store
of one and therefore keeps repeated groups idempotent. Runtime admission and
input preservation remain supplied by the ordinary record readiness theorem. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

def capOpenRecordGroup (records : List Index) (remaining : Nat) : Nat :=
  256 + ((records[records.length-(remaining+1)]?).map Fin.val).getD 0 / 65536

def capOpenMarksFinish (records : List Index) : Nat → (Nat → Word) → Nat → Word
  | 0, marks => marks
  | remaining+1, marks => capOpenMarksFinish records remaining
      (fun node => if node = capOpenRecordGroup records remaining then 1 else marks node)

private theorem finish_pointwise (records : List Index) (remaining : Nat)
    (left right : Nat → Word) (node : Nat) (same : left node = right node) :
    capOpenMarksFinish records remaining left node =
      capOpenMarksFinish records remaining right node := by
  induction remaining generalizing left right with
  | zero => exact same
  | succ remaining ih =>
    simp only [capOpenMarksFinish]
    apply ih
    split
    · rfl
    · exact same

theorem cap_open_records_marks (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records reference remaining state)
    (node : Nat) (nodeBound : node < 512) :
    (capCountedRun capOpenRecordState remaining state).getMem (capMarkAddress node) =
      capOpenMarksFinish records remaining (fun key => state.getMem (capMarkAddress key)) node := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have bounded := ready.bounded
    have ordinalBound : records.length-(remaining+1) < records.length := by omega
    have entry := cap_open_records_entry context records reference state remaining
      indexSpace outputSpace heapBelow saltsBelow inputs ready
    have nextReady := cap_open_records_ready_next context records reference state remaining
      countBound indexSpace outputSpace heapBelow saltsBelow inputs ready
    have oneStep (key : Nat) (inside : key < 512) :=
      cap_open_record_mark entry ready.one key inside
    have group : capOpenRecordGroup records remaining =
        256+(records[records.length-(remaining+1)]'ordinalBound).val/65536 := by
      simp only [capOpenRecordGroup, List.getElem?_eq_getElem ordinalBound,
        Option.map_some, Option.getD_some]
    rw [capCountedRun.eq_2, ih _ nextReady]
    simp only [capOpenMarksFinish]
    apply finish_pointwise
    simpa only [group] using oneStep node nodeBound

end CommitGolfCandidate
