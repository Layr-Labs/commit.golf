import CommitGolfDepth.Span

/-! Solver-side rules for symbolic guarded RV64 executions.

The fork step rule opens one valid FORK in the real interpreter. Its two child computations
remain in canonical order and use their reserved fuel. The continuation is taken only
when both children succeed; exhaustion still dominates failure. Resource rules quantify
over syntactic support, hence over every possible oracle reply and private coin outcome.
Instantiate `children` with the real `executeBudgeted` runner for machine proofs.
The query coordinate below counts trace annotations, not the independent `Oracle.run`
counter for an arbitrary supplied runner. Honest query budgets remain separate obligations.
Ordinary-step rules retain permission checks, write protection and instruction prices,
including the zero-fuel and fault cases. ECALL rules retain public/private sampling,
argument guards, HALT status and their distinct resource prices. These are proof helpers,
not changes to the machine or extra certificate assumptions.
-/
namespace CommitGolfDepth.Span.Proofs
open CommitGolf RiscvZkvm.Rv64 OracleComp OracleSpec
open CommitGolfDepth.Span.SpanMachine

/-- Shared-memory join followed by the parent PC advance. -/
def joinedState (p : Policy) (state : MachineState) (left right : Child)
    (l r : Result) : MachineState :=
  (protectWrites p state (merge state l.state r.state left.region right.region)).setPC
    (state.pc + 4)

/-- Exact continuation, including unsuccessful children. Reserved fuel is never refunded. -/
def resume (children : ChildRunner) (image : Riscv.Image) (p : Policy) (coins : Bool)
    (fuel : Nat) (state : MachineState) (left right : Child) (l r : Result) :
    OracleComp World (BoundedResult (fuel - left.fuel - right.fuel)) :=
  if childrenExit l.exit r.exit = .success then
    runBody children true image p coins (fuel - left.fuel - right.fuel)
      (joinedState p state left right l r)
  else pure (boundedStop (fuel - left.fuel - right.fuel) (childrenExit l.exit r.exit) state)

/-- Attach the executed child traces without clipping any work or outcome. -/
def joinedResult (fuel : Nat) (left right : Child)
    (reserved : left.fuel + right.fuel ≤ fuel)
    (l : BoundedResult left.fuel) (r : BoundedResult right.fuel)
    (c : BoundedResult (fuel - left.fuel - right.fuel)) : BoundedResult (fuel + 1) :=
  ⟨{c.val with trace := .fork FORK_CYCLES JOIN_CYCLES l.val.trace r.val.trace c.val.trace}, by
    have hl := l.property
    have hr := r.property
    have hc := c.property
    change 1 + l.val.trace.instructions + r.val.trace.instructions +
      c.val.trace.instructions ≤ fuel + 1
    omega⟩

/-- One valid FORK, with arbitrary child programs, input state and remaining fuel.
The descriptor hypothesis certifies the real loader, not a solver-supplied task list. -/
theorem runBody_fork (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (reserved : left.fuel + right.fuel ≤ fuel) :
    runBody children true image p coins (fuel + 1) state = (do
      let l ← children (childPolicy p left.region right.region) left.fuel (childState state left)
      let r ← children (childPolicy p right.region left.region) right.fuel (childState state right)
      let c ← resume children image p coins fuel state left right l.val r.val
      return joinedResult fuel left right reserved l r c) := by
  rw [runBody, fetched]
  simp only [selector]
  simp only [show (3 : BitVec 64) ≠ 0 by decide, show (3 : BitVec 64) ≠ 1 by decide,
    show (3 : BitVec 64) ≠ 2 by decide, ite_false, ite_true, loaded, dite_eq_left reserved]
  apply bind_congr
  intro l
  apply bind_congr
  intro r
  dsimp only [resume, joinedResult, joinedState]
  split <;> rfl

/-- Projection of the exact step rule with a type using only contract definitions.
This is suitable for independent comparator checks of the symbolic rule itself. -/
theorem runBody_fork_val (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (reserved : left.fuel + right.fuel ≤ fuel) :
    Subtype.val <$> runBody children true image p coins (fuel + 1) state = (do
      let l ← children (childPolicy p left.region right.region) left.fuel (childState state left)
      let r ← children (childPolicy p right.region left.region) right.fuel (childState state right)
      let c ← if childrenExit l.val.exit r.val.exit = .success then
          runBody children true image p coins (fuel - left.fuel - right.fuel)
            ((protectWrites p state
              (merge state l.val.state r.val.state left.region right.region)).setPC (state.pc + 4))
        else pure (boundedStop (fuel - left.fuel - right.fuel)
          (childrenExit l.val.exit r.val.exit) state)
      return {c.val with trace := .fork FORK_CYCLES JOIN_CYCLES l.val.trace r.val.trace c.val.trace}) := by
  rw [runBody_fork children image p coins fuel state left right fetched selector loaded reserved]
  simp only [map_bind, map_pure]
  apply bind_congr
  intro l
  apply bind_congr
  intro r
  dsimp only [resume, joinedResult, joinedState]
  split <;> rfl

/-- Zero fuel is an exhausted execution, even when the next instruction is FORK. -/
theorem runBody_zero (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (state : MachineState) :
    runBody children canFork image p coins 0 state = pure (boundedStop 0 .unfinished state) := by rw [runBody]

/-- A disabled fork faults; no child computation is launched. -/
theorem runBody_fork_disabled (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3) :
    runBody children false image p coins (fuel + 1) state =
      pure (boundedExit fuel .failure state) := by
  rw [runBody, fetched]
  simp [selector]

/-- Malformed descriptors fault before either child runs. -/
theorem runBody_fork_invalid (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3) (invalid : forkChildren p state = none) :
    runBody children true image p coins (fuel + 1) state =
      pure (boundedExit fuel .failure state) := by
  rw [runBody, fetched]
  simp [selector, invalid]

/-- Child fuel must be reserved in aggregate before either child runs. -/
theorem runBody_fork_unreserved (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (unreserved : ¬ left.fuel + right.fuel ≤ fuel) :
    runBody children true image p coins (fuel + 1) state =
      pure (boundedExit fuel .failure state) := by
  rw [runBody, fetched]
  simp [selector, loaded, unreserved]

/-- Successful children permit the parent continuation, but do not imply its success. -/
theorem resume_success (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child) (l r : Result)
    (hl : l.exit = .success) (hr : r.exit = .success) :
    resume children image p coins fuel state left right l r =
      runBody children true image p coins (fuel - left.fuel - right.fuel)
        (joinedState p state left right l r) := by
  simp [resume, childrenExit, hl, hr]

/-- Unsuccessful children retain the exact combined exit and suppress continuation work. -/
theorem resume_unsuccessful (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child) (l r : Result)
    (h : childrenExit l.exit r.exit ≠ .success) :
    resume children image p coins fuel state left right l r =
      pure (boundedStop (fuel - left.fuel - right.fuel) (childrenExit l.exit r.exit) state) := by
  simp only [resume, h, ite_false]

/-- A failed sibling cannot conceal an exhausted child. -/
theorem resume_unfinished_left (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child) (l r : Result)
    (hl : l.exit = .unfinished) :
    resume children image p coins fuel state left right l r =
      pure (boundedStop (fuel - left.fuel - right.fuel) .unfinished state) := by
  simp [resume, hl]

/-- Componentwise trace-resource upper bounds; instruction fuel stays in `BoundedResult`.
`queries` is the trace coordinate, not a claim about an arbitrary runner's actual oracle calls. -/
def Bounds (result : Result) (work span queries : Nat) : Prop :=
  result.work ≤ work ∧ result.span ≤ span ∧ result.oracleCalls ≤ queries

/-- Resource composition at a join: work adds both children, span takes their maximum. -/
theorem joinedResult_bounds (fuel : Nat) (left right : Child)
    (reserved : left.fuel + right.fuel ≤ fuel)
    (l : BoundedResult left.fuel) (r : BoundedResult right.fuel)
    (c : BoundedResult (fuel - left.fuel - right.fuel))
    (lw ls lq rw rs rq cw cs cq : Nat)
    (hl : Bounds l.val lw ls lq) (hr : Bounds r.val rw rs rq)
    (hc : Bounds c.val cw cs cq) :
    Bounds (joinedResult fuel left right reserved l r c).val
      (FORK_CYCLES + lw + rw + JOIN_CYCLES + cw)
      (FORK_CYCLES + max ls rs + JOIN_CYCLES + cs) (lq + rq + cq) := by
  rcases hl with ⟨hlw, hls, hlq⟩
  rcases hr with ⟨hrw, hrs, hrq⟩
  rcases hc with ⟨hcw, hcs, hcq⟩
  simp only [Result.work, Result.span, Result.oracleCalls] at hlw hls hlq hrw hrs hrq hcw hcs hcq
  change _ ∧ _ ∧ _
  dsimp only [joinedResult, Result.work, Result.span, Result.oracleCalls,
    Trace.work, Trace.span, Trace.queries]
  constructor
  · omega
  constructor
  · have hm := max_le_max hls hrs
    omega
  · omega

/-- Peel a real successful descriptor/fuel check into its child and continuation runs.
No child-success assumption is made: `resume` retains failure and exhaustion behavior. -/
theorem runBody_fork_support (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (reserved : left.fuel + right.fuel ≤ fuel) (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children true image p coins (fuel + 1) state)) :
    ∃ l ∈ support (children (childPolicy p left.region right.region) left.fuel (childState state left)),
      ∃ r ∈ support (children (childPolicy p right.region left.region) right.fuel (childState state right)),
        ∃ c ∈ support (resume children image p coins fuel state left right l.val r.val),
          out = joinedResult fuel left right reserved l r c := by
  rw [runBody_fork children image p coins fuel state left right fetched selector loaded reserved] at reached
  obtain ⟨l, hl, rest⟩ := mem_support_bind_peel _ _ reached
  obtain ⟨r, hr, rest⟩ := mem_support_bind_peel _ _ rest
  obtain ⟨c, hc, last⟩ := mem_support_bind_peel _ _ rest
  have equal := eq_of_mem_support_pure _ last
  exact ⟨l, hl, r, hr, c, hc, equal⟩

/-- An induction-ready bound for the actual fork step, conditional only on bounds
for each possible child and the exact continuation reached by those child results. -/
theorem runBody_fork_bounds (children : ChildRunner) (image : Riscv.Image) (p : Policy)
    (coins : Bool) (fuel : Nat) (state : MachineState) (left right : Child)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (selector : state.getReg .x5 = 3)
    (loaded : forkChildren p state = some (left, right))
    (reserved : left.fuel + right.fuel ≤ fuel)
    (lw ls lq rw rs rq cw cs cq : Nat)
    (hl : ∀ l ∈ support (children (childPolicy p left.region right.region) left.fuel
      (childState state left)), Bounds l.val lw ls lq)
    (hr : ∀ r ∈ support (children (childPolicy p right.region left.region) right.fuel
      (childState state right)), Bounds r.val rw rs rq)
    (hc : ∀ l ∈ support (children (childPolicy p left.region right.region) left.fuel
      (childState state left)), ∀ r ∈ support (children (childPolicy p right.region left.region)
      right.fuel (childState state right)), ∀ c ∈ support
      (resume children image p coins fuel state left right l.val r.val), Bounds c.val cw cs cq)
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children true image p coins (fuel + 1) state)) :
    Bounds out.val (FORK_CYCLES + lw + rw + JOIN_CYCLES + cw)
      (FORK_CYCLES + max ls rs + JOIN_CYCLES + cs) (lq + rq + cq) := by
  obtain ⟨l, hleft, r, hright, c, hcont, rfl⟩ :=
    runBody_fork_support children image p coins fuel state left right fetched selector loaded reserved out reached
  exact joinedResult_bounds fuel left right reserved l r c lw ls lq rw rs rq cw cs cq
    (hl l hleft) (hr r hright) (hc l hleft r hright c hcont)

/-- Lift body bounds to the real recursive executor. Its child runner is fixed to
`executeBudgeted` at the smaller fork depth; the final ownership filter changes only state.
Apply `runBody_fork_bounds` to the premise for an actual machine induction step. -/
theorem executeBudgeted_succ_bounds (image : Riscv.Image) (coins : Bool) (depth : Nat)
    (p : Policy) (fuel : Nat) (state : MachineState) (work span queries : Nat)
    (h : ∀ result ∈ support (runBody (executeBudgeted image coins depth) true image p coins
      fuel (readView p state)), Bounds result.val work span queries)
    (out : BoundedResult fuel)
    (reached : out ∈ support (executeBudgeted image coins (depth + 1) p fuel state)) :
    Bounds out.val work span queries := by
  rw [executeBudgeted] at reached
  obtain ⟨result, member, rfl⟩ := mem_support_map_peel _ _ reached
  exact h result member

/-- Fetch/decode failure retains the machine's zero-cost fault marker. This is
separate from a permission or ordinary-step fault, which consumes one charged instruction. -/
theorem runBody_fetch_failure (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = none) :
    runBody children canFork image p coins (fuel + 1) state =
      pure (boundedStop (fuel + 1) .failure state) := by
  rw [runBody, fetched]

/-- All branches for a fetched non-ECALL instruction, with permission checks and
write protection retained. The classification premise prevents treating a syscall as CPU work. -/
theorem runBody_ordinary_cases (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) :
    runBody children canFork image p coins (fuel + 1) state =
      (if ordinaryAllowed p state instruction then
        match Riscv.ordinaryStep state instruction with
        | none => pure (boundedExit fuel .failure state)
        | some next => do
          let result ← runBody children canFork image p coins fuel (protectWrites p state next)
          return boundedCharge result (Riscv.instructionCycles instruction) 0
      else pure (boundedExit fuel .failure state)) := by
  rw [runBody, fetched]
  split <;> simp_all
  rfl

/-- A valid ordinary instruction consumes one unit of fuel, charges its actual price,
and resumes under the same policy, fork setting and coin setting. -/
theorem runBody_ordinary (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state next : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) (allowed : ordinaryAllowed p state instruction = true)
    (stepped : Riscv.ordinaryStep state instruction = some next) :
    runBody children canFork image p coins (fuel + 1) state = (do
      let result ← runBody children canFork image p coins fuel (protectWrites p state next)
      return boundedCharge result (Riscv.instructionCycles instruction) 0) := by
  rw [runBody_ordinary_cases children canFork image p coins fuel state instruction fetched ordinary]
  simp only [allowed, ite_true, stepped]

/-- Core-only projection of the valid ordinary step, suitable for comparator checks. -/
theorem runBody_ordinary_val (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state next : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) (allowed : ordinaryAllowed p state instruction = true)
    (stepped : Riscv.ordinaryStep state instruction = some next) :
    Subtype.val <$> runBody children canFork image p coins (fuel + 1) state = (do
      let result ← runBody children canFork image p coins fuel (protectWrites p state next)
      return result.val.charge (Riscv.instructionCycles instruction) 0) := by
  rw [runBody_ordinary children canFork image p coins fuel state next instruction
    fetched ordinary allowed stepped]
  simp only [map_bind, map_pure]
  rfl

/-- A denied ordinary memory access faults without running the continuation. -/
theorem runBody_ordinary_denied (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) (denied : ordinaryAllowed p state instruction = false) :
    runBody children canFork image p coins (fuel + 1) state =
      pure (boundedExit fuel .failure state) := by
  rw [runBody_ordinary_cases children canFork image p coins fuel state instruction fetched ordinary]
  simp only [denied, Bool.false_eq_true, ite_false]

/-- An admitted but unsupported/faulting ordinary step also stops before continuation. -/
theorem runBody_ordinary_invalid (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) (allowed : ordinaryAllowed p state instruction = true)
    (invalid : Riscv.ordinaryStep state instruction = none) :
    runBody children canFork image p coins (fuel + 1) state =
      pure (boundedExit fuel .failure state) := by
  rw [runBody_ordinary_cases children canFork image p coins fuel state instruction fetched ordinary]
  simp only [allowed, ite_true, invalid]

/-- Add one sequential trace vertex to a resource bound. Query annotations are explicit,
so this rule does not equate annotations with an arbitrary runner's actual oracle calls. -/
theorem boundedCharge_bounds {fuel : Nat} (result : BoundedResult fuel)
    (cost calls work span queries : Nat) (h : Bounds result.val work span queries) :
    Bounds (boundedCharge result cost calls).val (cost + work) (cost + span) (calls + queries) := by
  rcases h with ⟨hw, hs, hq⟩
  change cost + result.val.work ≤ cost + work ∧ cost + result.val.span ≤ cost + span ∧
    calls + result.val.oracleCalls ≤ calls + queries
  exact ⟨Nat.add_le_add_left hw _, Nat.add_le_add_left hs _, Nat.add_le_add_left hq _⟩

/-- Worst-case support bounds compose through a real ordinary instruction, retaining
faults and exhaustion in the continuation. Success requires a separate proof. -/
theorem runBody_ordinary_bounds (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state next : MachineState)
    (instruction : Riscv.Instruction) (fetched : Riscv.fetch image state = some instruction)
    (ordinary : instruction ≠ .base .ECALL) (allowed : ordinaryAllowed p state instruction = true)
    (stepped : Riscv.ordinaryStep state instruction = some next)
    (work span queries : Nat)
    (h : ∀ result ∈ support (runBody children canFork image p coins fuel
      (protectWrites p state next)), Bounds result.val work span queries)
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)) :
    Bounds out.val (Riscv.instructionCycles instruction + work)
      (Riscv.instructionCycles instruction + span) queries := by
  rw [runBody_ordinary children canFork image p coins fuel state next instruction
    fetched ordinary allowed stepped] at reached
  obtain ⟨result, member, last⟩ := mem_support_bind_peel _ _ reached
  have equal := eq_of_mem_support_pure _ last
  subst out
  simpa only [Nat.zero_add] using boundedCharge_bounds result
    (Riscv.instructionCycles instruction) 0 work span queries (h result member)

/-- Exact public-oracle dispatch, including permission and argument failures. No query
is issued before both guards pass; the actual sampled reply is written before continuation. -/
theorem runBody_oracle_cases (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0) :
    runBody children canFork image p coins (fuel + 1) state =
      (if oracleAllowed p state then
        match Riscv.oracleInput state with
        | none => pure (boundedExit fuel .failure state)
        | some query => do
          let answer ← World.query (.inr query)
          let result ← runBody children canFork image p coins fuel
            (protectWrites p state (Riscv.writeOracleAnswer state (state.getReg .x12) query answer))
          return boundedCharge result (Riscv.oracleCycles query) 1
      else pure (boundedExit fuel .failure state)) := by
  rw [runBody, fetched]
  simp only [selector, ite_true]
  rfl

/-- One admitted public call, with its real primitive, answer, output buffer and price. -/
theorem runBody_oracle (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState) (query : PublicSpec.Domain)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0)
    (allowed : oracleAllowed p state = true) (input : Riscv.oracleInput state = some query) :
    runBody children canFork image p coins (fuel + 1) state = (do
      let answer ← World.query (.inr query)
      let result ← runBody children canFork image p coins fuel
        (protectWrites p state (Riscv.writeOracleAnswer state (state.getReg .x12) query answer))
      return boundedCharge result (Riscv.oracleCycles query) 1) := by
  rw [runBody_oracle_cases children canFork image p coins fuel state fetched selector]
  simp only [allowed, ite_true, input]

/-- A denied public call faults without issuing the query or running continuation. -/
theorem runBody_oracle_denied (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0)
    (denied : oracleAllowed p state = false) :
    runBody children canFork image p coins (fuel + 1) state = pure (boundedExit fuel .failure state) := by
  rw [runBody_oracle_cases children canFork image p coins fuel state fetched selector]
  simp only [denied, Bool.false_eq_true, ite_false]

/-- Malformed primitive arguments fault before any public query, even when permissions pass. -/
theorem runBody_oracle_invalid (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0)
    (allowed : oracleAllowed p state = true) (invalid : Riscv.oracleInput state = none) :
    runBody children canFork image p coins (fuel + 1) state = pure (boundedExit fuel .failure state) := by
  rw [runBody_oracle_cases children canFork image p coins fuel state fetched selector]
  simp only [allowed, ite_true, invalid]

/-- Worst-case public-call bounds cover every possible reply and all continuation exits.
The added query is a trace annotation; actual whole-run query budgets remain separate. -/
theorem runBody_oracle_bounds (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState) (query : PublicSpec.Domain)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 0)
    (allowed : oracleAllowed p state = true) (input : Riscv.oracleInput state = some query)
    (work span queries : Nat)
    (h : ∀ answer : PublicSpec.Range query, ∀ result ∈ support
      (runBody children canFork image p coins fuel
        (protectWrites p state (Riscv.writeOracleAnswer state (state.getReg .x12) query answer))),
        Bounds result.val work span queries)
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)) :
    Bounds out.val (Riscv.oracleCycles query + work) (Riscv.oracleCycles query + span) (1 + queries) := by
  rw [runBody_oracle children canFork image p coins fuel state query fetched selector allowed input] at reached
  obtain ⟨answer, _, rest⟩ := mem_support_bind_peel _ _ reached
  obtain ⟨result, member, last⟩ := mem_support_bind_peel _ _ rest
  have equal := eq_of_mem_support_pure _ last
  subst out
  exact boundedCharge_bounds result (Riscv.oracleCycles query) 1 work span queries (h answer result member)

/-- HALT is terminal for either exit code. It charges one cycle, no query, and does not
invoke the child runner or continuation, independently of the coin/fork flags. -/
theorem runBody_halt (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 1) :
    runBody children canFork image p coins (fuel + 1) state =
      pure (boundedExit fuel (if state.getReg .x10 = 0 then .success else .failure) state) := by
  rw [runBody, fetched]
  simp [selector]

/-- The terminal resource bound does not assert successful HALT for nonzero status. -/
theorem runBody_halt_bounds (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 1)
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)) :
    Bounds out.val 1 1 0 := by
  rw [runBody_halt children canFork image p coins fuel state fetched selector] at reached
  have equal := eq_of_mem_support_pure _ reached
  subst out
  simp [Bounds, boundedExit, stop, Result.work, Result.span, Result.oracleCalls,
    Trace.work, Trace.span, Trace.queries]

/-- Exact RANDOM dispatch. Disabled coins or invalid/denied output arguments fault
before sampling; otherwise every sampled bit is passed to the protected write and continuation. -/
theorem runBody_random_cases (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2) :
    runBody children canFork image p coins (fuel + 1) state =
      (if coins && randomAllowed p state then do
        let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
          ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
        let result ← runBody children canFork image p coins fuel
          (protectWrites p state (Riscv.writeBits state (state.getReg .x10) answer))
        return boundedCharge result (1 + ((state.getReg .x11).toNat + 7) / 8) 0
      else pure (boundedExit fuel .failure state)) := by
  rw [runBody, fetched]
  simp [selector]

/-- One enabled, admitted private-coin call. The distribution and bit width are those
of the machine, not a deterministic observer or an abstract fresh-state assumption. -/
theorem runBody_random (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2)
    (allowed : (coins && randomAllowed p state) = true) :
    runBody children canFork image p coins (fuel + 1) state = (do
      let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
        ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
      let result ← runBody children canFork image p coins fuel
        (protectWrites p state (Riscv.writeBits state (state.getReg .x10) answer))
      return boundedCharge result (1 + ((state.getReg .x11).toNat + 7) / 8) 0) := by
  rw [runBody_random_cases children canFork image p coins fuel state fetched selector]
  simp only [allowed, ite_true]

/-- In particular the checker/coin-disabled execution never samples RANDOM. -/
theorem runBody_random_disabled (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2) :
    runBody children canFork image p false (fuel + 1) state = pure (boundedExit fuel .failure state) := by
  rw [runBody_random_cases children canFork image p false fuel state fetched selector]
  simp

/-- Invalid buffers or denied permissions also suppress the private sampling effect. -/
theorem runBody_random_denied (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2)
    (denied : randomAllowed p state = false) :
    runBody children canFork image p coins (fuel + 1) state = pure (boundedExit fuel .failure state) := by
  rw [runBody_random_cases children canFork image p coins fuel state fetched selector]
  simp only [denied, Bool.and_false, Bool.false_eq_true, ite_false]

/-- RANDOM bounds are worst-case over every bit string and every continuation outcome.
They neither condition on successful sampling nor replace the bound by an expectation. -/
theorem runBody_random_bounds (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL)) (selector : state.getReg .x5 = 2)
    (allowed : (coins && randomAllowed p state) = true) (work span queries : Nat)
    (h : ∀ answer : BitVec (8 * (state.getReg .x11).toNat), ∀ result ∈ support
      (runBody children canFork image p coins fuel
        (protectWrites p state (Riscv.writeBits state (state.getReg .x10) answer))),
        Bounds result.val work span queries)
    (out : BoundedResult (fuel + 1))
    (reached : out ∈ support (runBody children canFork image p coins (fuel + 1) state)) :
    Bounds out.val (1 + ((state.getReg .x11).toNat + 7) / 8 + work)
      (1 + ((state.getReg .x11).toNat + 7) / 8 + span) queries := by
  rw [runBody_random children canFork image p coins fuel state fetched selector allowed] at reached
  obtain ⟨answer, _, rest⟩ := mem_support_bind_peel _ _ reached
  obtain ⟨result, member, last⟩ := mem_support_bind_peel _ _ rest
  have equal := eq_of_mem_support_pure _ last
  subst out
  simpa only [Nat.zero_add] using boundedCharge_bounds result
    (1 + ((state.getReg .x11).toNat + 7) / 8) 0 work span queries (h answer result member)

/-- Unknown ECALL selectors fault without issuing an effect. -/
theorem runBody_ecall_unknown (children : ChildRunner) (canFork : Bool) (image : Riscv.Image)
    (p : Policy) (coins : Bool) (fuel : Nat) (state : MachineState)
    (fetched : Riscv.fetch image state = some (.base .ECALL))
    (notOracle : state.getReg .x5 ≠ 0) (notHalt : state.getReg .x5 ≠ 1)
    (notRandom : state.getReg .x5 ≠ 2) (notFork : state.getReg .x5 ≠ 3) :
    runBody children canFork image p coins (fuel + 1) state = pure (boundedExit fuel .failure state) := by
  rw [runBody, fetched]
  simp only [notOracle, notHalt, notRandom, notFork, ite_false]

end CommitGolfDepth.Span.Proofs
