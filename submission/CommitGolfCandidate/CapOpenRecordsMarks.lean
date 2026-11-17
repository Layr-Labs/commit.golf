import CommitGolfCandidate.CapOpenRecordMarks

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

private theorem cursor_alignment (base ordinal : Nat) (aligned : base % 8 = 0) :
    (base+544*ordinal) % 8 = 0 := by omega

private theorem cursor_capacity (base count remaining limit : Nat)
    (bounded : remaining+1 ≤ count) (space : base+544*count ≤ limit) :
    base+544*(count-(remaining+1))+544 ≤ limit := by omega

theorem cap_open_records_marks (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+544*records.length ≤ context.limit)
    (high : 32800 ≤ context.output)
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
    let position := (records[records.length-(remaining+1)]'ordinalBound).val
    have positionBound : position < 16777216 := by
      simpa only [position, LENGTH, LOG_LENGTH, Nat.reducePow] using
        (records[records.length-(remaining+1)]'ordinalBound).isLt
    have loaded := cap_open_records_loaded context records reference state remaining
      indexSpace inputs ready
    have currentPC : state.pc = 4212 := by simpa using ready.pc
    have nextReady := cap_open_records_ready_next context records reference state remaining
      countBound indexSpace outputSpace inputs ready
    have oneStep (key : Nat) (inside : key < 512) :=
      cap_open_record_mark context.roots context.limit
        (context.output+544*(records.length-(remaining+1))) position state currentPC
        ready.roots ready.cursor
        (cursor_alignment context.output _ context.outputAligned)
        (cursor_capacity context.output records.length remaining context.limit bounded outputSpace)
        context.limitBound (by omega) positionBound loaded ready.leaves ready.marks ready.one
        key inside
    have group : capOpenRecordGroup records remaining = 256+position/65536 := by
      simp only [capOpenRecordGroup, List.getElem?_eq_getElem ordinalBound,
        Option.map_some, Option.getD_some, position]
    rw [capCountedRun.eq_2, ih _ nextReady]
    simp only [capOpenMarksFinish]
    apply finish_pointwise
    simpa only [group] using oneStep node nodeBound

end CommitGolfCandidate
