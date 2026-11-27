import CommitGolfDepth.Span.Descriptors
import CommitGolfDepth.Span.Trace

/-! # Guarded RV64 fork/join machine

The canonical interpreter evaluates both children left then right to define their joint
oracle/coin distribution. The specified parallel machine shares immutable sampled public
primitives, private independent coins and disjoint writable RAM. Its span is the weighted
fork trace, not the canonical interpreter's runtime. No arbitrary-monad commutation or
finite-processor scheduling theorem is asserted.

Permission masking/restriction is an explicit machine primitive. All data accesses,
including syscall I/O and descriptor reads, are checked. A child's forbidden list includes
all ancestor exclusions and its sibling's owned words; nested join never removes it.
Each fuel prefix is restricted to the task's owned words before becoming observable.
Both launched children finish their bounded executions, even if one fails. Any exhausted
child takes precedence over failure, so a fault cannot hide a nonterminating sibling.
-/

namespace CommitGolfDepth.Span.SpanMachine
open CommitGolf RiscvZkvm.Rv64 OracleComp OracleSpec

inductive Mode where
  | legacy | forkJoin
  deriving DecidableEq

structure Result where
  exit : Riscv.Exit
  state : MachineState
  trace : Trace

def Result.work (r : Result) : Nat := r.trace.work
def Result.span (r : Result) : Nat := r.trace.span
def Result.oracleCalls (r : Result) : Nat := r.trace.queries

def Result.toExecution (r : Result) : Riscv.Execution :=
  ⟨r.exit, r.state, r.work, r.oracleCalls⟩

def Result.ofLegacy (r : Riscv.Execution) : Result :=
  ⟨r.exit, r.state, .step r.cycles r.oracleCalls .done⟩

@[simp] theorem Result.legacy_toExecution (r : Riscv.Execution) :
    (Result.ofLegacy r).toExecution = r := by cases r; rfl

@[simp] theorem Result.legacy_span (r : Riscv.Execution) : (Result.ofLegacy r).span = r.cycles := by
  simp [ofLegacy, span, Trace.span]

def Result.charge (r : Result) (cycles queries : Nat) : Result :=
  {r with trace := .step cycles queries r.trace}

def stop (exit : Riscv.Exit) (state : MachineState) (cycles : Nat := 0) : Result :=
  ⟨exit, state, .step cycles 0 .done⟩

def finish (p : Policy) (before : MachineState) (r : Result) : Result :=
  {r with state := protectWrites p before r.state}

/-- Internal evidence is erased by the public executor. Fuel bounds the total number
of guest instructions in the returned fork trace, without clipping work or outcomes. -/
abbrev BoundedResult (fuel : Nat) := {r : Result // r.trace.instructions ≤ fuel}

def boundedStop (fuel : Nat) (exit : Riscv.Exit) (state : MachineState) : BoundedResult fuel :=
  ⟨stop exit state, by simp [stop, Trace.instructions]⟩

def boundedExit (fuel : Nat) (exit : Riscv.Exit) (state : MachineState) : BoundedResult (fuel + 1) :=
  ⟨stop exit state 1, by simp [stop, Trace.instructions]⟩

def boundedCharge {fuel : Nat} (r : BoundedResult fuel) (cycles queries : Nat) :
    BoundedResult (fuel + 1) :=
  ⟨r.val.charge cycles queries, by
    have bound := r.property
    change (if cycles = 0 then 0 else 1) + r.val.trace.instructions ≤ fuel + 1
    split <;> omega⟩

def boundedFinish {fuel : Nat} (p : Policy) (before : MachineState)
    (r : BoundedResult fuel) : BoundedResult fuel :=
  ⟨finish p before r.val, r.property⟩

@[simp] theorem finish_frame (p : Policy) (before : MachineState) (r : Result)
    (a : BitVec 64) (h : p.owned.containsWord a = false) :
    (finish p before r).state.mem a = before.mem a := by
  exact protectWrites_frame p before r.state a h

def ordinaryAllowed (p : Policy) (state : MachineState) : Riscv.Instruction → Bool
  | .base instruction =>
    match memAccess state instruction with
    | none => true
    | some (address, bytes, write) =>
      if write then p.writeAccess address.toNat bytes
      else p.readAccess address.toNat bytes
  | _ => true

def oracleAllowed (p : Policy) (state : MachineState) : Bool :=
  let inputBytes := if state.getReg .x13 = 0 then (COMPRESSION_INPUT_LENGTH + 7) / 8
    else (PERMUTATION_WIDTH + 7) / 8
  let outputBytes := if state.getReg .x13 = 0 then (COMPRESSION_OUTPUT_LENGTH + 7) / 8
    else (PERMUTATION_WIDTH + 7) / 8
  p.readAccess (state.getReg .x10).toNat inputBytes &&
    p.writeAccess (state.getReg .x12).toNat outputBytes

def randomAllowed (p : Policy) (state : MachineState) : Bool :=
  Riscv.randomArgumentsValid state &&
    p.writeAccess (state.getReg .x10).toNat (state.getReg .x11).toNat

def childrenExit (left right : Riscv.Exit) : Riscv.Exit :=
  if left = .unfinished ∨ right = .unfinished then .unfinished
  else if left = .success ∧ right = .success then .success else .failure

@[simp] theorem childrenExit_unfinished_left (right : Riscv.Exit) :
    childrenExit .unfinished right = .unfinished := by simp [childrenExit]

@[simp] theorem childrenExit_unfinished_right (left : Riscv.Exit) :
    childrenExit left .unfinished = .unfinished := by simp [childrenExit]

abbrev ChildRunner := Policy → (fuel : Nat) → MachineState → OracleComp World (BoundedResult fuel)

/-- Structural recursion in local instruction fuel; recursive child execution is supplied
only by the strictly smaller fork-depth interpreter. The coin policy is captured by that
runner and is passed unchanged to every descendant. -/
def runBody (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (allowCoins : Bool) : (fuel : Nat) → MachineState → OracleComp World (BoundedResult fuel)
  | 0, state => pure (boundedStop 0 .unfinished state)
  | fuel + 1, state =>
    match Riscv.fetch image state with
    | none => pure (boundedStop (fuel + 1) .failure state)
    | some (.base .ECALL) =>
      if state.getReg .x5 = 0 then
        if oracleAllowed p state then
          match Riscv.oracleInput state with
          | none => pure (boundedExit fuel .failure state)
          | some query => do
            let answer ← World.query (.inr query)
            let next := protectWrites p state
              (Riscv.writeOracleAnswer state (state.getReg .x12) query answer)
            let result ← runBody children canFork image p allowCoins fuel next
            return boundedCharge result (Riscv.oracleCycles query) 1
        else pure (boundedExit fuel .failure state)
      else if state.getReg .x5 = 1 then
        pure (boundedExit fuel (if state.getReg .x10 = 0 then .success else .failure) state)
      else if state.getReg .x5 = 2 then
        if allowCoins && randomAllowed p state then do
          let bytes := (state.getReg .x11).toNat
          let answer ← liftM ($ᵗ BitVec (8 * bytes) : ProbComp (BitVec (8 * bytes)))
          let next := protectWrites p state (Riscv.writeBits state (state.getReg .x10) answer)
          let result ← runBody children canFork image p allowCoins fuel next
          return boundedCharge result (1 + (bytes + 7) / 8) 0
        else pure (boundedExit fuel .failure state)
      else if state.getReg .x5 = 3 then
        if canFork then
          match forkChildren p state with
          | none => pure (boundedExit fuel .failure state)
          | some (left, right) => if reserved : left.fuel + right.fuel ≤ fuel then do
            let l ← children (childPolicy p left.region right.region) left.fuel (childState state left)
            let r ← children (childPolicy p right.region left.region) right.fuel (childState state right)
            let exit := childrenExit l.val.exit r.val.exit
            let combined := protectWrites p state (merge state l.val.state r.val.state left.region right.region)
            let next := combined.setPC (state.pc + 4)
            let continuation ← if exit = .success then
                runBody children canFork image p allowCoins (fuel - left.fuel - right.fuel) next
              else pure (boundedStop (fuel - left.fuel - right.fuel) exit state)
            return ⟨{continuation.val with
              trace := .fork FORK_CYCLES JOIN_CYCLES l.val.trace r.val.trace continuation.val.trace}, by
                have hl := l.property
                have hr := r.property
                have hc := continuation.property
                change 1 + l.val.trace.instructions + r.val.trace.instructions +
                  continuation.val.trace.instructions ≤ fuel + 1
                omega⟩
            else pure (boundedExit fuel .failure state)
        else pure (boundedExit fuel .failure state)
      else pure (boundedExit fuel .failure state)
    | some instruction =>
      if ordinaryAllowed p state instruction then
        match Riscv.ordinaryStep state instruction with
        | none => pure (boundedExit fuel .failure state)
        | some next => do
          let result ← runBody children canFork image p allowCoins fuel (protectWrites p state next)
          return boundedCharge result (Riscv.instructionCycles instruction) 0
      else pure (boundedExit fuel .failure state)

/-- Outer recursion bounds nested fork ancestry, not a fixed-width literal task list.
The depth-zero machine still executes ordinary CPU work, but a further FORK faults. -/
def executeBudgeted (image : Riscv.Image) (allowCoins : Bool) :
    Nat → Policy → (fuel : Nat) → MachineState → OracleComp World (BoundedResult fuel)
  | 0, p, fuel, state =>
    boundedFinish p state <$> runBody (fun _ n s => pure (boundedStop n .failure s)) false image p allowCoins
      fuel (readView p state)
  | depth + 1, p, fuel, state =>
    boundedFinish p state <$> runBody (executeBudgeted image allowCoins depth) true image p allowCoins
      fuel (readView p state)

def executeAtDepth (image : Riscv.Image) (coins : Bool) (depth : Nat) (p : Policy)
    (fuel : Nat) (state : MachineState) : OracleComp World Result :=
  Subtype.val <$> executeBudgeted image coins depth p fuel state

def execute (image : Riscv.Image) (fuel : Nat) (state : MachineState) (allowCoins : Bool) :
    OracleComp World Result := executeAtDepth image allowCoins MAX_FORK_DEPTH rootPolicy fuel state

/-- Read-view equality implies equality of the actual guarded CPU body, with all oracle
queries, private coins, control flow and trace costs retained. No effect reordering occurs. -/
theorem runBody_congr (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (allowCoins : Bool) (fuel : Nat) (s t : MachineState)
    (h : readView p s = readView p t) :
    runBody children canFork image p allowCoins fuel (readView p s) =
      runBody children canFork image p allowCoins fuel (readView p t) := by rw [h]

theorem executeAtDepth_frame (image : Riscv.Image) (coins : Bool) (depth : Nat)
    (p : Policy) (fuel : Nat) (state : MachineState) (a : BitVec 64)
    (h : p.owned.containsWord a = false) :
    (fun r => r.state.mem a) <$> executeAtDepth image coins depth p fuel state =
      (fun _ => state.mem a) <$> executeAtDepth image coins depth p fuel state := by
  cases depth <;> simp only [executeAtDepth, executeBudgeted, Functor.map_map]
  all_goals
    congr 1
    funext r
    exact finish_frame p state r.val a h

def visibleResult (p : Policy) (r : Result) : Result :=
  {r with state := readView p r.state}

theorem visible_finish_congr (p : Policy) (s t : MachineState) (r : Result)
    (h : readView p s = readView p t) :
    visibleResult p (finish p s r) = visibleResult p (finish p t r) := by
  simp only [visibleResult, finish, readView_protectWrites, h]

/-- Noninterference of whole bounded executions. This is an equality of computations,
so the same private coins and fixed public oracle couple both sides, including failures,
queries and cost traces. It does not assert commutation in an arbitrary effect monad. -/
theorem executeAtDepth_read_congr (image : Riscv.Image) (coins : Bool) (depth : Nat)
    (p : Policy) (fuel : Nat) (s t : MachineState) (h : readView p s = readView p t) :
    visibleResult p <$> executeAtDepth image coins depth p fuel s =
      visibleResult p <$> executeAtDepth image coins depth p fuel t := by
  cases depth <;> simp only [executeAtDepth, executeBudgeted, Functor.map_map, h]
  all_goals
    congr 1
    funext r
    exact visible_finish_congr p s t r.val h

/-- Conserved fuel bounds the total guest-instruction prefix over the entire executed
fork tree, including both children and faults. Weighted work remains a separate measure.
The bound holds for every syntactic oracle/coin reply, before sampling an oracle. -/
theorem executeAtDepth_instructions_le (image : Riscv.Image) (coins : Bool) (depth : Nat)
    (p : Policy) (fuel : Nat) (state : MachineState) (result : Result)
    (reached : result ∈ support (executeAtDepth image coins depth p fuel state)) :
    result.trace.instructions ≤ fuel := by
  unfold executeAtDepth at reached
  rw [support_map] at reached
  obtain ⟨bounded, _, rfl⟩ := reached
  exact bounded.property

/-- A child can be run after its sibling's writes become visible, with exactly the same
permitted computation as from the original snapshot. Together with `merge_serial` and
`overlay_commute`, this is the shared-memory justification for constant logical join.
It holds for every bounded outcome, not only successful HALTs. -/
theorem executeAtDepth_sibling_independent (image : Riscv.Image) (coins : Bool) (depth : Nat)
    (parentPolicy : Policy) (own sibling : Region) (fuel : Nat)
    (state siblingResult : MachineState) :
    visibleResult (childPolicy parentPolicy own sibling) <$>
        executeAtDepth image coins depth (childPolicy parentPolicy own sibling) fuel
          (overlay state siblingResult sibling) =
      visibleResult (childPolicy parentPolicy own sibling) <$>
        executeAtDepth image coins depth (childPolicy parentPolicy own sibling) fuel state := by
  apply executeAtDepth_read_congr
  exact childPolicy_overlay_invisible parentPolicy own sibling state siblingResult

theorem Result.span_le_work (r : Result) : r.span ≤ r.work := r.trace.span_le_work

end CommitGolfDepth.Span.SpanMachine
