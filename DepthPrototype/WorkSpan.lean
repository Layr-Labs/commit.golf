import CommitGolf.Riscv
import VCVio.OracleComp.Support
import Lean.Elab.Tactic.Omega

/-! A bounded, structured work/span prototype over genuine RV64IM executions.

Every task owns a fresh machine state. The only shared input boundary is one
read-only 64-bit word, loaded at address zero before each task. No task receives
another task's mutable state or a pure Lean function of an earlier result.
Plan values and code images are fixed inputs of this prototype; no theorem
charges constructing a plan or its input words from a commitment message, or
links a message-indexed family of plans to one delivered artifact.

`Plan.serialRun` is an explicit canonical serialization, not a parallel runtime.
`Plan.span` is the weighted critical path of the declared structured plan. Each
declared entry/exit control kernel is executed and its full cost occurs in both
work and span. The examples use HALT control padding: these kernels do not
implement a fork/join primitive or establish actual launch, join, scheduler or
wiring costs. Those overhead bridges remain unproved. This file proves the
serial execution work bound. A finite-processor scheduler, actual parallel
backend, input loading/materialization, communication, and aggregate live memory
still need separate semantics and adequacy proofs. Metadata/list construction is not
charged and must not be read as free computation of commitment data.

This is not a production `Certificate`, nor an oracle-round or hardware-time
claim. Its small concrete clients use no oracle or randomness calls. -/

set_option autoImplicit false

namespace DepthPrototype.WorkSpan

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The fixed input boundary: one word in otherwise zeroed private memory.
Loading this input is explicitly outside the task work model. -/
def inputState (word : BitVec 64) : MachineState :=
  initialMachine.setMem 0 word

/-- A task is an actual image/fuel/input triple with a successful execution
and a worst-case cycle bound for every syntactic oracle response path. -/
structure Kernel where
  image : Image
  fuel : Nat
  input : BitVec 64
  cycles : Nat
  imageBound : image.byteSize < MAX_PROGRAM_BYTES
  noEmbeddedData : image.data = []
  fuelPositive : 0 < fuel
  fuelBound : fuel ≤ STEP_LIMIT
  executionBound : ∀ result ∈ support (execute image fuel (inputState input) false),
    result.exit = .success ∧ result.cycles ≤ cycles

/-- The task's computation is the challenge's real interpreter. -/
def Kernel.run (kernel : Kernel) : OracleComp World Execution :=
  execute kernel.image kernel.fuel (inputState kernel.input) false

theorem Kernel.run_eq_execute (kernel : Kernel) :
    kernel.run = execute kernel.image kernel.fuel (inputState kernel.input) false := rfl

/-- Structured independent tasks. `serial` and `forkJoin` differ only in their
declared precedence constraints, retaining the same executed entry/exit kernels.
There is no arbitrary host-function node or implicit data-dependent wiring. -/
inductive Plan where
  | task (kernel : Kernel)
  | serial (enter : Kernel) (left right : Plan) (leave : Kernel)
  | forkJoin (enter : Kernel) (left right : Plan) (leave : Kernel)

/-- Total certified task-cycle work, including executed entry and exit costs. -/
def Plan.work : Plan → Nat
  | .task kernel => kernel.cycles
  | .serial enter left right leave => enter.cycles + left.work + right.work + leave.cycles
  | .forkJoin enter left right leave => enter.cycles + left.work + right.work + leave.cycles

/-- Weighted dependency depth. Sequencing adds; independent branches use `max`.
An entire atomic kernel remains sequential at its certified cycle bound. -/
def Plan.span : Plan → Nat
  | .task kernel => kernel.cycles
  | .serial enter left right leave => enter.cycles + left.span + right.span + leave.cycles
  | .forkJoin enter left right leave => enter.cycles + max left.span right.span + leave.cycles

theorem Plan.work_serial (enter leave : Kernel) (left right : Plan) :
    (Plan.serial enter left right leave).work =
      enter.cycles + left.work + right.work + leave.cycles := rfl

theorem Plan.work_forkJoin (enter leave : Kernel) (left right : Plan) :
    (Plan.forkJoin enter left right leave).work =
      enter.cycles + left.work + right.work + leave.cycles := rfl

theorem Plan.span_serial (enter leave : Kernel) (left right : Plan) :
    (Plan.serial enter left right leave).span =
      enter.cycles + left.span + right.span + leave.cycles := rfl

theorem Plan.span_forkJoin (enter leave : Kernel) (left right : Plan) :
    (Plan.forkJoin enter left right leave).span =
      enter.cycles + max left.span right.span + leave.cycles := rfl

theorem Plan.span_le_work (plan : Plan) : plan.span ≤ plan.work := by
  induction plan with
  | task kernel => exact le_rfl
  | serial enter left right leave leftIH rightIH =>
      simp only [Plan.span, Plan.work]
      omega
  | forkJoin enter left right leave leftIH rightIH =>
      have hmax : max left.span right.span ≤ left.work + right.work :=
        max_le (by omega) (by omega)
      simp only [Plan.span, Plan.work]
      omega

/-- Run private tasks in a fixed left-before-right order. Fork does not silently
assert commutativity of shared effects; it uses this same serialization. -/
def Plan.serialRun : Plan → OracleComp World (List Execution)
  | .task kernel => do
      let result ← kernel.run
      pure [result]
  | .serial enter left right leave | .forkJoin enter left right leave => do
      let entered ← enter.run
      let leftResults ← left.serialRun
      let rightResults ← right.serialRun
      let exited ← leave.run
      pure (entered :: (leftResults ++ rightResults ++ [exited]))

theorem Plan.forkJoin_serializes (enter leave : Kernel) (left right : Plan) :
    (Plan.forkJoin enter left right leave).serialRun =
      (Plan.serial enter left right leave).serialRun := rfl

/-- Cycle count read from the actual execution results, not from the plan's meter. -/
def observedCycles (results : List Execution) : Nat :=
  (results.map Execution.cycles).sum

/-- Public oracle calls read from the actual execution results. -/
def observedOracleCalls (results : List Execution) : Nat :=
  (results.map Execution.oracleCalls).sum

/-- Every actual serialized execution respects the declared total work bound.
This theorem deliberately does not say that `serialRun` takes the smaller span. -/
theorem Plan.serialRun_cycles_le (plan : Plan) :
    ∀ results ∈ support plan.serialRun, observedCycles results ≤ plan.work := by
  induction plan with
  | task kernel =>
      intro results reached
      simp only [Plan.serialRun, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at reached
      obtain ⟨result, hresult, equal⟩ := reached
      subst results
      simpa only [observedCycles, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, Plan.work] using (kernel.executionBound result hresult).2
  | serial enter left right leave leftIH rightIH
  | forkJoin enter left right leave leftIH rightIH =>
      intro results reached
      simp only [Plan.serialRun, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at reached
      obtain ⟨entered, hentered, leftResults, hleft, rightResults, hright,
        exited, hexited, equal⟩ := reached
      subst results
      have enteredBound := (enter.executionBound entered hentered).2
      have leftBound := leftIH leftResults hleft
      have rightBound := rightIH rightResults hright
      have exitedBound := (leave.executionBound exited hexited).2
      simp only [observedCycles, List.map_cons, List.map_append, List.map_nil,
        List.sum_cons, List.sum_append, List.sum_nil, Nat.add_zero] at *
      simp only [Plan.work]
      omega

/-! Concrete controlled kernels. All word encodings are interpreted by the
same decoder and execution semantics as the live challenge. -/

private theorem execute_addi (image : Image) (steps : Nat) (state : MachineState)
    (rd rs : Reg) (imm : BitVec 12)
    (fetched : fetch image state = some (.base (.ADDI rd rs imm))) :
    execute image (steps + 1) state false = (do
      let result ← execute image steps (execInstrBr state (.ADDI rd rs imm)) false
      pure (result.charge 1 0)) := by
  rw [execute, fetched]
  rfl

private theorem execute_mul (image : Image) (steps : Nat) (state : MachineState)
    (rd rs rt : Reg)
    (fetched : fetch image state = some (.base (.MUL rd rs rt))) :
    execute image (steps + 1) state false = (do
      let result ← execute image steps (execInstrBr state (.MUL rd rs rt)) false
      pure (result.charge 4 0)) := by
  rw [execute, fetched]
  rfl

private theorem execute_ld (image : Image) (steps : Nat) (state : MachineState)
    (rd rs : Reg) (offset : BitVec 12)
    (fetched : fetch image state = some (.base (.LD rd rs offset)))
    (valid : accessValid (state.getReg rs + signExtend12 offset) 8 = true) :
    execute image (steps + 1) state false = (do
      let result ← execute image steps (execInstrBr state (.LD rd rs offset)) false
      pure (result.charge 1 0)) := by
  rw [execute, fetched]
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, valid]
  rfl

private theorem execute_halt (image : Image) (state : MachineState)
    (fetched : fetch image state = some (.base .ECALL))
    (flag : state.getReg .x5 = 1) (status : state.getReg .x10 = 0) :
    execute image 1 state false = pure (⟨.success, state, 1, 0⟩ : Execution) := by
  rw [execute, fetched]
  simp only [flag, status]
  rfl

/-- `addi t0,zero,1; addi a0,zero,0; ecall`: a successful three-cycle HALT kernel. -/
def haltImage : Image :=
  ⟨[0x00100293, 0x00000513, 0x00000073], []⟩

def haltFinal (word : BitVec 64) : MachineState :=
  execInstrBr (execInstrBr (inputState word) (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 0)

theorem halt_execute (word : BitVec 64) :
    execute haltImage 3 (inputState word) false =
      pure (⟨.success, haltFinal word, 3, 0⟩ : Execution) := by
  have first : fetch haltImage (inputState word) =
      some (.base (.ADDI .x5 .x0 1)) := by
    simp [fetch, haltImage, inputState, initialMachine, MachineState.setMem]
    rfl
  have second : fetch haltImage (execInstrBr (inputState word) (.ADDI .x5 .x0 1)) =
      some (.base (.ADDI .x10 .x0 0)) := by
    have pc : (execInstrBr (inputState word) (.ADDI .x5 .x0 1)).pc = 0x1004 := rfl
    rw [fetch, pc]
    simp [haltImage]
    rfl
  have third : fetch haltImage (haltFinal word) = some (.base .ECALL) := by
    have pc : (haltFinal word).pc = 0x1008 := rfl
    rw [fetch, pc]
    simp [haltImage]
    rfl
  have halted : execute haltImage 1
      (execInstrBr (execInstrBr (inputState word) (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 0))
      false = pure (⟨.success, haltFinal word, 1, 0⟩ : Execution) := by
    simpa only [haltFinal] using
      execute_halt haltImage (haltFinal word) third (by rfl) (by rfl)
  rw [execute_addi haltImage 2 (inputState word) .x5 .x0 1 first,
    execute_addi haltImage 1 _ .x10 .x0 0 second,
    halted]
  simp only [pure_bind, Execution.charge]

def haltKernel : Kernel where
  image := haltImage
  fuel := 3
  input := 0
  cycles := 3
  imageBound := by decide
  noEmbeddedData := rfl
  fuelPositive := by decide
  fuelBound := by decide
  executionBound := by
    intro result reached
    rw [halt_execute] at reached
    have equal : result = (⟨.success, haltFinal 0, 3, 0⟩ : Execution) := by
      simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst result
    exact ⟨rfl, le_rfl⟩

/-- `ld t1,0(zero); mul t2,t1,t1;` followed by the HALT kernel. The MUL costs four,
so this is eight cycles rather than merely five instructions. -/
def squareImage : Image :=
  ⟨[0x00003303, 0x026303b3, 0x00100293, 0x00000513, 0x00000073], []⟩

def squareFinal (word : BitVec 64) : MachineState :=
  execInstrBr
    (execInstrBr
      (execInstrBr (execInstrBr (inputState word) (.LD .x6 .x0 0)) (.MUL .x7 .x6 .x6))
      (.ADDI .x5 .x0 1)) (.ADDI .x10 .x0 0)

theorem square_execute (word : BitVec 64) :
    execute squareImage 5 (inputState word) false =
      pure (⟨.success, squareFinal word, 8, 0⟩ : Execution) := by
  let loaded := execInstrBr (inputState word) (.LD .x6 .x0 0)
  let squared := execInstrBr loaded (.MUL .x7 .x6 .x6)
  let flagged := execInstrBr squared (.ADDI .x5 .x0 1)
  have first : fetch squareImage (inputState word) = some (.base (.LD .x6 .x0 0)) := by
    simp [fetch, squareImage, inputState, initialMachine, MachineState.setMem]
    rfl
  have second : fetch squareImage loaded = some (.base (.MUL .x7 .x6 .x6)) := by
    have pc : loaded.pc = 0x1004 := rfl
    rw [fetch, pc]
    simp [squareImage]
    rfl
  have third : fetch squareImage squared = some (.base (.ADDI .x5 .x0 1)) := by
    have pc : squared.pc = 0x1008 := rfl
    rw [fetch, pc]
    simp [squareImage]
    rfl
  have fourth : fetch squareImage flagged = some (.base (.ADDI .x10 .x0 0)) := by
    have pc : flagged.pc = 0x100c := rfl
    rw [fetch, pc]
    simp [squareImage]
    rfl
  have fifth : fetch squareImage (squareFinal word) = some (.base .ECALL) := by
    have pc : (squareFinal word).pc = 0x1010 := rfl
    rw [fetch, pc]
    simp [squareImage]
    rfl
  have halted : execute squareImage 1 (execInstrBr flagged (.ADDI .x10 .x0 0)) false =
      pure (⟨.success, squareFinal word, 1, 0⟩ : Execution) := by
    simpa only [squareFinal, loaded, squared, flagged] using
      execute_halt squareImage (squareFinal word) fifth (by rfl) (by rfl)
  rw [execute_ld squareImage 4 (inputState word) .x6 .x0 0 first (by rfl),
    execute_mul squareImage 3 loaded .x7 .x6 .x6 second,
    execute_addi squareImage 2 squared .x5 .x0 1 third,
    execute_addi squareImage 1 flagged .x10 .x0 0 fourth,
    halted]
  simp only [pure_bind, Execution.charge]

theorem square_output (word : BitVec 64) :
    (squareFinal word).getReg .x7 = word * word := by rfl

/-- The sample kernel reads its shared input but never writes memory. -/
theorem square_preserves_input (word : BitVec 64) :
    (squareFinal word).mem = (inputState word).mem := by rfl

def squareKernel (word : BitVec 64) : Kernel where
  image := squareImage
  fuel := 5
  input := word
  cycles := 8
  imageBound := by decide
  noEmbeddedData := rfl
  fuelPositive := by decide
  fuelBound := by decide
  executionBound := by
    intro result reached
    rw [square_execute] at reached
    have equal : result = (⟨.success, squareFinal word, 8, 0⟩ : Execution) := by
      simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst result
    exact ⟨rfl, le_rfl⟩

/-- Same input, distinct private states and output registers: no branch output
is an input to its sibling. -/
def sequentialPair : Plan :=
  .serial haltKernel (.task (squareKernel 7)) (.task (squareKernel 7)) haltKernel

def parallelPair : Plan :=
  .forkJoin haltKernel (.task (squareKernel 7)) (.task (squareKernel 7)) haltKernel

theorem same_work : sequentialPair.work = parallelPair.work := rfl

theorem same_work_value : sequentialPair.work = 22 ∧ parallelPair.work = 22 := by
  exact ⟨rfl, rfl⟩

theorem lower_weighted_span : parallelPair.span = 14 ∧ sequentialPair.span = 22 := by
  exact ⟨rfl, rfl⟩

theorem strictly_lower_span : parallelPair.span < sequentialPair.span := by decide

theorem same_serialized_execution : parallelPair.serialRun = sequentialPair.serialRun := rfl

end DepthPrototype.WorkSpan
