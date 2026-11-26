import DepthPrototype.WorkSpan

/-! Small, ordinary-kernel regression clients of the work/span prototype.
No native decision procedure and no production security-certificate claim. -/

set_option autoImplicit false

namespace DepthPrototype.WorkSpan.Tests

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

example : sequentialPair.work = 22 := rfl
example : parallelPair.work = 22 := rfl
example : sequentialPair.span = 22 := rfl
example : parallelPair.span = 14 := rfl
example : parallelPair.span < sequentialPair.span := strictly_lower_span

/-- The example uses an actual four-cycle multiply, not a unit-cost placeholder. -/
example : instructionCycles (.base (.MUL .x7 .x6 .x6)) = 4 := rfl

example : (squareFinal 7).getReg .x7 = 49 := rfl
example : (squareFinal 9).getReg .x7 = 81 := rfl
example (input : BitVec 64) : (squareFinal input).mem = (inputState input).mem :=
  square_preserves_input input

example : (squareKernel 7).run =
    pure (⟨.success, squareFinal 7, 8, 0⟩ : Execution) := square_execute 7

example : haltKernel.run =
    pure (⟨.success, haltFinal 0, 3, 0⟩ : Execution) := halt_execute 0

/-- Inspection metadata, outside task execution and not a free data-computation node. -/
def sampleResults : List Execution := [
    (⟨.success, haltFinal 0, 3, 0⟩ : Execution),
    (⟨.success, squareFinal 7, 8, 0⟩ : Execution),
    (⟨.success, squareFinal 7, 8, 0⟩ : Execution),
    (⟨.success, haltFinal 0, 3, 0⟩ : Execution)]

/-- The four executed kernels include both three-cycle control-padding tasks;
they are not claimed to implement a backend's fork or join operation. -/
theorem parallel_execution : parallelPair.serialRun = pure sampleResults := by
  simp [parallelPair, Plan.serialRun, Kernel.run, haltKernel, squareKernel,
    halt_execute, square_execute, sampleResults]

theorem sequential_execution : sequentialPair.serialRun = pure sampleResults := by
  rw [← same_serialized_execution]
  exact parallel_execution

/-- Both CPU-only plans make zero public oracle calls, despite different spans.
An oracle-only round metric therefore cannot express this local parallelism. -/
example : observedOracleCalls <$> parallelPair.serialRun = pure 0 := by
  rw [parallel_execution]
  rfl

example : observedOracleCalls <$> sequentialPair.serialRun = pure 0 := by
  rw [sequential_execution]
  rfl

example : observedCycles <$> parallelPair.serialRun = pure 22 := by
  rw [parallel_execution]
  rfl

example : observedCycles <$> sequentialPair.serialRun = pure 22 := by
  rw [sequential_execution]
  rfl

/-- Only observe the two leaf outputs after execution. This is outside the
charged kernel data plane, like inspecting an execution log. -/
def outputPair : List Execution → Option (BitVec 64 × BitVec 64)
  | [_entered, left, right, _exited] => some (left.state.getReg .x7, right.state.getReg .x7)
  | _ => none

example : outputPair <$> parallelPair.serialRun = pure (some (49, 49)) := by
  rw [parallel_execution]
  rfl

example : outputPair <$> sequentialPair.serialRun = pure (some (49, 49)) := by
  rw [sequential_execution]
  rfl

/-- Span is a schedule/DAG quantity: the canonical serial interpreter still
performs 22 actual cycles. It is not claimed to execute in 14 cycles. -/
example : observedCycles [
    (⟨.success, haltFinal 0, 3, 0⟩ : Execution),
    (⟨.success, squareFinal 7, 8, 0⟩ : Execution),
    (⟨.success, squareFinal 7, 8, 0⟩ : Execution),
    (⟨.success, haltFinal 0, 3, 0⟩ : Execution)] = 22 := rfl

example (results : List Execution) (reachable : results ∈ support parallelPair.serialRun) :
    observedCycles results ≤ 22 := parallelPair.serialRun_cycles_le results reachable

example : (Plan.forkJoin haltKernel parallelPair sequentialPair haltKernel).work = 50 := rfl
example : (Plan.forkJoin haltKernel parallelPair sequentialPair haltKernel).span = 28 := rfl

end DepthPrototype.WorkSpan.Tests
