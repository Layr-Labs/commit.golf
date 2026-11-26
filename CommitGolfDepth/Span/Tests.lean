import CommitGolfDepth.Span

/-! Kernel-checked small CPU fork tests. The deterministic interpreter observer is only
test instrumentation; the production machine and its certificate retain the full oracle
and private-coin computation. No native evaluation is a proof authority here. -/

namespace CommitGolfDepth.Span.Tests
open CommitGolf RiscvZkvm.Rv64 OracleComp OracleSpec SpanMachine

def cpuImage : Riscv.Image := ⟨[
  0x00000073, -- parent FORK
  0x00100293, -- parent t0 := HALT
  0x00000513, -- parent a0 := success
  0x00000073, -- parent HALT
  0x02b585b3, -- child MUL a1,a1,a1 (four cycles)
  0x00b53023, -- child SD a1,0(a0)
  0x00100293, -- child t0 := HALT
  0x00000513, -- child a0 := success
  0x00000073], []⟩

def descriptorWords : List (BitVec 64) :=
  [0x1010, 5, 512, 8, 512, 7, 0, 0,
   0x1010, 5, 520, 8, 520, 9, 0, 0]

def forkState : MachineState :=
  {Riscv.initialMachine with
    regs := fun r => if r = .x5 then 3 else if r = .x10 then 128 else 0
    mem := fun a => if 128 ≤ a.toNat ∧ a.toNat < 256 then
      descriptorWords[(a.toNat - 128) / 8]?.getD 0 else 0}

def observer : QueryImpl World Id
  | .inl n => ⟨0, Nat.zero_lt_succ n⟩
  | .inr (.inl _) => pure (0 : BitVec COMPRESSION_OUTPUT_LENGTH)
  | .inr (.inr (.inl _)) => pure (0 : BitVec PERMUTATION_WIDTH)
  | .inr (.inr (.inr _)) => pure (0 : BitVec PERMUTATION_WIDTH)

def observed (fuel : Nat := 14) (coins : Bool := true) : Result :=
  simulateQ observer (execute cpuImage fuel forkState coins)

def report (r : Result) : Riscv.Exit × Nat × Nat × Nat × BitVec 64 × BitVec 64 :=
  (r.exit, r.work, r.span, r.oracleCalls, r.state.mem 512, r.state.mem 520)

example : report observed = (.success, 101, 93, 0, 49, 81) := by decide +kernel
example : observed.trace.instructions = 14 := by decide +kernel

-- The checker coin prohibition is retained in both descendants; CPU-only children work.
example : report (observed 14 false) = (.success, 101, 93, 0, 49, 81) := by decide +kernel

-- Exhausting the parent remains unfinished rather than a successful partial execution.
example : (observed 0).exit = .unfinished := by decide +kernel

example : childrenExit .failure .unfinished = .unfinished := rfl
example : childrenExit .unfinished .failure = .unfinished := rfl

-- Shared-RAM reconciliation is order independent for the disjoint aligned output words.
example : (Region.mk 512 8).disjoint ⟨520, 8⟩ = true := by decide

example (parent left right : MachineState) :
    merge parent left right ⟨512, 8⟩ ⟨520, 8⟩ =
      overlay (overlay parent right ⟨520, 8⟩) left ⟨512, 8⟩ := by
  rw [merge_serial parent left right ⟨512, 8⟩ ⟨520, 8⟩ (by decide)]
  exact overlay_commute parent left right ⟨512, 8⟩ ⟨520, 8⟩ (by decide)

example (p : Policy) (parent worker : MachineState) :
    readView (childPolicy p ⟨512, 8⟩ ⟨520, 8⟩) (overlay parent worker ⟨520, 8⟩) =
      readView (childPolicy p ⟨512, 8⟩ ⟨520, 8⟩) parent :=
  childPolicy_overlay_invisible p _ _ parent worker

example (t : Trace) : t.span ≤ t.work := t.span_le_work

def restrictedPolicy : Policy := childPolicy rootPolicy ⟨1024, 256⟩ ⟨512, 256⟩

def restricted (image : Riscv.Image) (state : MachineState) (fuel : Nat := 1)
    (coins : Bool := true) : Result :=
  simulateQ observer (executeAtDepth image coins MAX_FORK_DEPTH restrictedPolicy fuel state)

def syscallState (selector input length output kind : BitVec 64) : MachineState :=
  {Riscv.initialMachine with regs := fun r =>
    if r = .x5 then selector else if r = .x10 then input else if r = .x11 then length
    else if r = .x12 then output else if r = .x13 then kind else 0}

-- Actual forbidden ordinary load/store executions fault before accessing sibling RAM.
example : (restricted ⟨[0x00053583], []⟩ (syscallState 0 512 0 0 0)).exit = .failure := by
  decide +kernel
example : (restricted ⟨[0x00b53023], []⟩ (syscallState 0 512 0 0 0)).exit = .failure := by
  decide +kernel

-- Full oracle input and output spans, and RANDOM output spans, receive permissions.
example : (restricted ⟨[0x73], []⟩ (syscallState 0 512 64 1024 0)).exit = .failure := by
  decide +kernel
example : (restricted ⟨[0x73], []⟩ (syscallState 0 1024 64 512 0)).exit = .failure := by
  decide +kernel
example : (restricted ⟨[0x73], []⟩ (syscallState 2 512 8 0 0)).exit = .failure := by
  decide +kernel

-- The inherited exclusion persists when a task creates another child policy.
example : (childPolicy restrictedPolicy ⟨1024, 8⟩ ⟨1032, 8⟩).canRead 512 8 = false := by
  decide +kernel

-- Fixed parser rejects overlapping, unaligned, wrapping and out-of-parent regions.
def testChild (region : Region) (fuel : Nat := 5) : Child := ⟨0x1010, fuel, region, 0, 0, 0, 0⟩
example : (testChild ⟨1025, 8⟩).valid restrictedPolicy = false := by decide +kernel
example : (testChild ⟨1024, 7⟩).valid restrictedPolicy = false := by decide +kernel
example : (testChild ⟨Riscv.MEMORY_BYTES - 8, 16⟩).valid rootPolicy = false := by decide +kernel
example : (testChild ⟨2048, 8⟩).valid restrictedPolicy = false := by decide +kernel
example : (testChild ⟨1024, 8⟩ 0).valid restrictedPolicy = false := by decide +kernel
example : (testChild ⟨1024, 8⟩ (STEP_LIMIT + 1)).valid restrictedPolicy = false := by decide +kernel
example : (forkChildren rootPolicy (forkState.setMem 208 512)).isNone = true := by decide +kernel

-- A descriptor table itself cannot be read through a parent's inherited exclusion.
example : (forkChildren (childPolicy rootPolicy ⟨1024, 8⟩ ⟨128, 128⟩) forkState).isNone = true := by
  decide +kernel

-- At the ancestry bound FORK faults, while ordinary CPU execution remains available.
example : (simulateQ observer (executeAtDepth cpuImage true 0 rootPolicy 14 forkState)).exit =
    .failure := by decide +kernel

-- Both children run: the left consumes a four-cycle MUL then exhausts fuel; the right
-- faults on fetch. Unfinished dominates the fault and all executed work is retained.
def unfinishedAndFault : MachineState := (forkState.setMem 136 1).setMem 192 0x2000
example : let r := simulateQ observer (execute cpuImage 14 unfinishedAndFault true);
    (r.exit, r.work, r.span) = (.unfinished, 86, 86) := by decide +kernel

def nestedImage : Riscv.Image := ⟨[0x00300293, 0x73, 0x00100293, 0x00000513, 0x73,
  0x02b585b3, 0x00b53023, 0x00100293, 0x00000513, 0x73], []⟩
def nestedWords : List (BitVec 64) :=
  [0x1000, 15, 512, 16, 256, 0, 0, 0, 0x1014, 5, 528, 8, 528, 11, 0, 0,
   0x1014, 5, 512, 8, 512, 7, 0, 0, 0x1014, 5, 520, 8, 520, 9, 0, 0]
def nestedState : MachineState :=
  {Riscv.initialMachine with
    regs := fun r => if r = .x10 then 128 else 0
    mem := fun a => if 128 ≤ a.toNat ∧ a.toNat < 384 then
      nestedWords[(a.toNat - 128) / 8]?.getD 0 else 0}

-- Successful data-dependent nesting uses the same submitted image at both fork levels.
example : let r := simulateQ observer (execute nestedImage 25 nestedState true);
    (r.exit, r.work, r.span, r.state.mem 512, r.state.mem 520, r.state.mem 528) =
      (.success, 196, 180, 49, 81, 121) := by decide +kernel
example : (simulateQ observer (execute nestedImage 25 nestedState true)).trace.instructions = 25 := by
  decide +kernel

-- The left child owns and overwrites the right descriptor's entry word. The right
-- child still uses the descriptor snapshotted before either child ran.
def descriptorOverwrite : MachineState :=
  let s := ((forkState.setMem 144 192).setMem 152 64).setMem 160 192
  let s := s.setMem 168 0
  let s := (s.setMem 208 512).setMem 224 512
  s
example : let r := simulateQ observer (execute cpuImage 14 descriptorOverwrite true);
    (r.exit, r.work, r.span, r.state.mem 192, r.state.mem 512) =
      (.success, 101, 93, 0, 81) := by decide +kernel

def randomChildImage : Riscv.Image := ⟨[0x73, 0x00100293, 0x00000513, 0x73,
  0x00200293, 0x73, 0x00100293, 0x00000513, 0x73], []⟩
def randomChildState : MachineState := (forkState.setMem 168 8).setMem 232 8

-- An actual checker-mode child requests RANDOM. Both children reject it, with both
-- bounded prefixes charged; allowCoins=false is inherited rather than defaulted.
example : let r := simulateQ observer (execute randomChildImage 14 randomChildState false);
    (r.exit, r.work, r.span, r.oracleCalls) = (.failure, 86, 84, 0) := by decide +kernel

def oracleChildImage : Riscv.Image := ⟨[0x73, 0x00100293, 0x00000513, 0x73,
  0x00000293, 0x73, 0x00100293, 0x73], []⟩
def oracleChildState : MachineState :=
  let s := ((forkState.setMem 136 2).setMem 152 32).setMem 160 1024
  let s := ((s.setMem 168 64).setMem 176 512).setMem 184 0
  let s := ((s.setMem 200 4).setMem 208 544).setMem 216 32
  ((s.setMem 224 1024).setMem 232 64).setMem 240 544

-- Both child oracle queries occur. The left then exhausts fuel, the right fails HALT;
-- unfinished wins, and the complete charged work and two query events are retained.
example : let r := simulateQ observer (execute oracleChildImage 14 oracleChildState true);
    (r.exit, r.work, r.span, r.oracleCalls) = (.unfinished, 102, 93, 2) := by decide +kernel

-- Fork reservations are checked before launching; no child query can run without fuel.
example : let r := simulateQ observer (execute oracleChildImage 6 oracleChildState true);
    (r.exit, r.work, r.oracleCalls) = (.failure, 1, 0) := by decide +kernel

-- Exact child reservations leave no instruction for the parent's continuation.
example : (observed 11).exit = .unfinished := by decide +kernel

-- Unused child reservations are not refunded: both children halt immediately, but their
-- five-step reservations leave no parent fuel after an eleven-step root allocation.
def earlyHaltState : MachineState :=
  let s := (forkState.setMem 128 0x1018).setMem 192 0x1018
  (s.setMem 160 0).setMem 224 0
example : (simulateQ observer (execute cpuImage 11 earlyHaltState true)).exit = .unfinished := by
  decide +kernel

end CommitGolfDepth.Span.Tests
