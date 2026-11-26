import CommitGolfCandidate.C3XLog
import CommitGolfCandidate.C3PBindingWitness

/-! # Reading a marked log for any window shape

`C3XLog` reads a marked log with the `t3` window of the unpaired leaf. The paired leaf has two
shapes (`C3PShapeWitness zField digest`): the compression reply sits in a different window of the
permutation input, and the digest in a different window of the reply. `shapeScan zField` is `scan`
with the input window as a parameter. The marked run, its rows and `ScanState` are those of
`C3XLog`: they do not depend on the shape. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp OracleSpec

set_option autoImplicit false

/-- Read one row. The targets are the `zField` windows of the inputs returned by inverse calls. -/
def shapeStep (zField : Block → BitVec 256) (state : ScanState) : MarkedRow → ScanState
  | .compression input reply _ =>
      ⟨.compression input reply :: state.rows, reply :: state.seen, state.targets,
        state.flag ∨ (reply ∉ state.seen ∧ reply ∈ state.targets)⟩
  | .forward input reply =>
      ⟨.permutation input reply :: state.rows, state.seen, state.targets, state.flag⟩
  | .inverse input output =>
      ⟨.permutation input output :: state.rows, state.seen, zField input :: state.targets,
        state.flag⟩

/-- Read a log, oldest call first. -/
def shapeScan (zField : Block → BitVec 256) (state : ScanState) (log : List MarkedRow) : ScanState :=
  log.foldl (shapeStep zField) state

theorem shape_scan_cons (zField : Block → BitVec 256) (state : ScanState) (row : MarkedRow)
    (log : List MarkedRow) :
    shapeScan zField state (row :: log) = shapeScan zField (shapeStep zField state row) log := rfl

theorem shape_step_rows (zField : Block → BitVec 256) (state : ScanState) (row : MarkedRow) :
    (shapeStep zField state row).rows = row.erase :: state.rows := by
  cases row <;> rfl

/-- The scanned state lists every erased row of the log. -/
theorem shape_scan_rows_mem (zField : Block → BitVec 256) (state : ScanState) (log : List MarkedRow)
    (row : PublicRow) (present : row ∈ log.map MarkedRow.erase) :
    row ∈ (shapeScan zField state log).rows := by
  have general : ∀ (log : List MarkedRow) (state : ScanState),
      (row ∈ state.rows ∨ row ∈ log.map MarkedRow.erase) → row ∈ (shapeScan zField state log).rows := by
    intro log
    induction log with
    | nil =>
      intro state h
      rcases h with h | h
      · exact h
      · simp at h
    | cons head tail ih =>
      intro state h
      rw [shape_scan_cons]
      apply ih
      rw [shape_step_rows]
      rcases h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rw [List.map_cons] at h
        rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h
  exact general log state (Or.inr present)

/-- A witness among the recorded rows is a witness for the scanned state. -/
theorem shape_scan_witness (zField digest : Block → BitVec 256) (log : List MarkedRow)
    (witness : C3PShapeWitness zField digest (log.map MarkedRow.erase)) :
    C3PShapeWitness zField digest (shapeScan zField ScanState.init log).rows :=
  witness.mono fun row present => shape_scan_rows_mem zField ScanState.init log row present

end TwoPermutationPrototype.Sampling
