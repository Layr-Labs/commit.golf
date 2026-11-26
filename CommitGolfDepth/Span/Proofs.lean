import CommitGolfDepth.Span

/-! Solver-side rules for symbolic fork/join executions.

The step rule opens one valid FORK in the real interpreter. Its two child computations
remain in canonical order and use their reserved fuel. The continuation is taken only
when both children succeed; exhaustion still dominates failure. Resource rules quantify
over syntactic support, hence over every possible oracle reply and private coin outcome.
Instantiate `children` with the real `executeBudgeted` runner for machine proofs.
The query coordinate below counts trace annotations, not the independent `Oracle.run`
counter for an arbitrary supplied runner. Honest query budgets remain separate obligations.
These are proof helpers, not changes to the machine or extra certificate assumptions.
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

end CommitGolfDepth.Span.Proofs
