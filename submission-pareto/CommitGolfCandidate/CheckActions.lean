import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationLeafAccess
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationMemoryBridge
import CommitGolfCandidate.TwoPermutationCheckerLowerRun
import CommitGolfCandidate.CheckEvaluation

/-! A straight-line action kernel for any image (a generalization of `PentaGrouped.Action`, with
`lui` and arbitrary register results): exact `execute` equations, and the deterministic
fixed-oracle semantics with recorded public rows that the checker observation uses. -/
namespace TwoPermutationPrototype.CheckActions
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

inductive Action where
  | lui (dest : Reg) (imm : BitVec 20) (result : Word)
  | offset (dest base : Reg) (imm : BitVec 12) (result : Word)
  | load (dest base : Reg) (imm : BitVec 12) (addr : Nat)
  | store (base value : Reg) (imm : BitVec 12) (addr : Nat)
  | perm (src dst : Nat)
  /-- Any ordinary register instruction whose step writes `result` to `dest`. -/
  | alu (op : Instr) (dest : Reg) (result : Word)

def Action.op : Action → Instr
  | .lui dest imm _ => .LUI dest imm
  | .offset dest base imm _ => .ADDI dest base imm
  | .load dest base imm _ => .LD dest base imm
  | .store base value imm _ => .SD base value imm
  | .perm .. => .ECALL
  | .alu op _ _ => op

def Action.calls : Action → Nat | .perm .. => 1 | _ => 0

def Action.cycles : Action → Nat
  | .perm .. => 8
  | .alu op _ _ => instructionCycles (.base op)
  | _ => 1

def Action.valid (a : Action) (s : MachineState) : Prop :=
  match a with
  | .lui _ imm result => (imm.zeroExtend 32 <<< 12).signExtend 64 = result
  | .offset _ base imm result => s.getReg base + signExtend12 imm = result
  | .load _ base imm addr | .store base _ imm addr =>
      s.getReg base + signExtend12 imm = wordAddress addr ∧ addr + 1 ≤ 2^33
  | .perm src dst => s.getReg .x10 = wordAddress src ∧ s.getReg .x12 = wordAddress dst ∧
      s.getReg .x5 = 0 ∧ s.getReg .x11 = 200 ∧ s.getReg .x13 = 1 ∧ src + 25 ≤ 2^33 ∧ dst + 25 ≤ 2^33
  | .alu op dest result => ordinaryStep s (.base op) = some ((s.setReg dest result).setPC (s.pc + 4))

def putReg (s : MachineState) (rd : Reg) (v : Word) := (s.setReg rd v).setPC (s.pc + 4)
def putWord (s : MachineState) (a : Nat) (v : Word) := (s.setMem (wordAddress a) v).setPC (s.pc + 4)

def Action.run (a : Action) (s : MachineState) : OracleComp World MachineState :=
  match a with
  | .lui dest _ result | .offset dest _ _ result => pure (putReg s dest result)
  | .load dest _ _ addr => pure (putReg s dest (memoryView s addr))
  | .store _ value _ addr => pure (putWord s addr (s.getReg value))
  | .perm src dst => do
      let reply ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) src)))))
      return writeBits s (wordAddress dst) reply
  | .alu _ dest result => pure (putReg s dest result)

def runOps : List Action → MachineState → OracleComp World MachineState
  | [], s => pure s
  | a :: rest, s => a.run s >>= runOps rest

def opCalls (ops : List Action) := (ops.map Action.calls).sum
def opCycles (ops : List Action) := (ops.map Action.cycles).sum

private theorem ordinary_charge (img : Image) (s t : MachineState) (op : Instr) (fuel : Nat) (coins : Bool)
    (cell : fetch img s = some (.base op)) (step : ordinaryStep s (.base op) = some t)
    (price : instructionCycles (.base op) = 1) :
    execute img (1 + fuel) s coins = (do let r ← execute img fuel t coins; return r.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, execute_ordinary_step img (.base op) s t fuel coins cell step, price]

theorem action_run (img : Image) (a : Action) (s : MachineState) (fuel : Nat) (coins : Bool)
    (cell : fetch img s = some (.base a.op)) (ok : a.valid s) :
    execute img (1 + fuel) s coins = (do
      let t ← a.run s
      let r ← execute img fuel t coins
      return r.charge a.cycles a.calls) := by
  cases a with
  | alu op rd result =>
    simp only [Action.run, pure_bind, Action.calls, Action.cycles]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step img (.base op) s _ fuel coins cell ok]
    rfl
  | lui rd imm result =>
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge img s _ _ _ _ cell _ rfl
    change some ((s.setReg rd ((imm.zeroExtend 32 <<< 12).signExtend 64)).setPC (s.pc + 4)) = _
    rw [show (imm.zeroExtend 32 <<< 12).signExtend 64 = result from ok]; rfl
  | offset rd base imm result =>
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge img s _ _ _ _ cell _ rfl
    change some ((s.setReg rd (s.getReg base + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [show s.getReg base + signExtend12 imm = result from ok]; rfl
  | load rd base imm addr =>
    obtain ⟨atAddr, room⟩ := ok
    have access : accessValid (wordAddress addr) 8 = true := by simpa using leaf_word_access addr 0 (by omega)
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge img s _ _ _ _ cell _ rfl
    simp only [ordinaryStep, Action.op, memoryArgumentsValid, memAccess, atAddr, access, ite_true, execInstrBr,
      putReg, memoryView]
  | store base value imm addr =>
    obtain ⟨atAddr, room⟩ := ok
    have access : accessValid (wordAddress addr) 8 = true := by simpa using leaf_word_access addr 0 (by omega)
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge img s _ _ _ _ cell _ rfl
    simp only [ordinaryStep, Action.op, memoryArgumentsValid, memAccess, atAddr, access, ite_true, execInstrBr, putWord]
  | perm src dst =>
    obtain ⟨input, output, sel, size, pr, rs, rd⟩ := ok
    rw [Nat.add_comm 1 fuel, execute_permutation_call img fuel s coins src dst rs rd input output sel size pr cell]
    simp only [Action.run, bind_assoc, pure_bind, Action.calls, Action.cycles]

theorem action_pc (a : Action) (s t : MachineState) (hit : t ∈ support (a.run s)) : t.pc = s.pc + 4 := by
  cases a <;> simp only [Action.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  all_goals first | subst t; rfl | obtain ⟨_, _, rfl⟩ := hit; exact written_pc ..

/-! ### Fixed-oracle semantics -/

def fixedStep (o : Oracle) (s : MachineState) : Action → MachineState
  | .lui rd _ result | .offset rd _ _ result => putReg s rd result
  | .load rd _ _ a => putReg s rd (memoryView s a)
  | .store _ r _ a => putWord s a (s.getReg r)
  | .perm src dst => writeBits s (wordAddress dst) (o.permutation (packBuffer (window (memoryView s) src)))
  | .alu _ rd result => putReg s rd result

def fixedOps (o : Oracle) (ops : List Action) (s : MachineState) : MachineState := ops.foldl (fixedStep o) s

/-- The public rows an action records under a fixed oracle. -/
def stepRows (o : Oracle) (s : MachineState) : Action → List PublicRow
  | .perm src _ => [PublicRow.permutation (packBuffer (window (memoryView s) src))
      (o.permutation (packBuffer (window (memoryView s) src)))]
  | _ => []

def opsRows (o : Oracle) : List Action → MachineState → List PublicRow
  | [], _ => []
  | a :: rest, s => stepRows o s a ++ opsRows o rest (fixedStep o s a)

theorem check_step (o : Oracle) (s : MachineState) (a : Action) :
    checkEvaluation o (recordRows (a.run s)) = ((fixedStep o s a, stepRows o s a), a.calls) := by
  cases a <;> simp only [Action.run, fixedStep, stepRows, Action.calls, record_rows_pure, check_evaluation_pure]
  simp only [record_rows_query, check_evaluation_public_bind, check_evaluation_map, record_rows_pure,
    check_evaluation_pure]
  rfl

theorem check_ops (o : Oracle) (ops : List Action) (s : MachineState) :
    checkEvaluation o (recordRows (runOps ops s)) = ((fixedOps o ops s, opsRows o ops s), opCalls ops) := by
  induction ops generalizing s with
  | nil => simp [runOps, fixedOps, opsRows, opCalls, record_rows_pure, check_evaluation_pure]
  | cons a rest ih =>
    rw [show runOps (a :: rest) s = a.run s >>= runOps rest from rfl, check_recorded_bind, check_step]
    dsimp only
    rw [ih]
    simp only [fixedOps, opsRows, opCalls, List.foldl_cons, List.map_cons, List.sum_cons]

/-- Validity along the fixed-oracle trajectory. -/
def validFixed (o : Oracle) : List Action → MachineState → Prop
  | [], _ => True
  | a :: rest, s => a.valid s ∧ validFixed o rest (fixedStep o s a)

def fetchOps (img : Image) (index : Nat) (ops : List Action) :=
  ∀ (i : Fin ops.length) (s : MachineState), s.pc = BitVec.ofNat 64 (4096 + 4 * (index + i.val)) →
    fetch img s = some (.base ops[i].op)

theorem fixed_pc (o : Oracle) (s : MachineState) (a : Action) : (fixedStep o s a).pc = s.pc + 4 := by
  cases a <;> first | rfl | exact written_pc ..

/-- The observed run of a straight-line block under a fixed oracle. -/
theorem observe_ops (o : Oracle) (img : Image) (ops : List Action) (index fuel : Nat) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096 + 4 * index)) (cells : fetchOps img index ops) (ok : validFixed o ops s) :
    checkEvaluation o (recordRows (execute img (ops.length + fuel) s false)) =
      let tail := checkEvaluation o (recordRows (execute img fuel (fixedOps o ops s) false))
      ((tail.1.1.charge (opCycles ops) (opCalls ops), opsRows o ops s ++ tail.1.2),
        opCalls ops + tail.2) := by
  induction ops generalizing index s with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, fixedOps, List.foldl_nil, opCalls, opCycles, List.map_nil, List.sum_nil,
      Nat.mul_zero, opsRows, List.nil_append]
    cases checkEvaluation o (recordRows (execute img fuel s false)) with
    | mk p n => cases p with | mk r rows => cases r; simp [Execution.charge]
  | cons a rest ih =>
    have cell := cells ⟨0, by simp⟩ s (by simpa using pc)
    rw [show (a :: rest).length + fuel = 1 + (rest.length + fuel) by simp; omega,
      action_run img a s _ false cell ok.1, check_recorded_bind, check_step]
    dsimp only
    have tpc : (fixedStep o s a).pc = BitVec.ofNat 64 (4096 + 4 * (index + 1)) := by
      rw [fixed_pc, pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      congr 1
    have tail : fetchOps img (index + 1) rest := by
      intro i st hp
      exact cells ⟨i.val + 1, by simp⟩ st (by simpa only [Nat.add_assoc, Nat.add_comm 1 i.val] using hp)
    simp only [bind_pure_comp]
    rw [check_recorded_map, ih (index + 1) _ tpc tail ok.2]
    simp only [fixedOps, List.foldl_cons]
    generalize checkEvaluation o (recordRows (execute img fuel (List.foldl (fixedStep o) (fixedStep o s a) rest) false)) = tl
    obtain ⟨⟨⟨e, st, c, q⟩, rows⟩, n⟩ := tl
    simp only [opsRows, opCalls, opCycles, List.map_cons, List.sum_cons, List.append_assoc, List.length_cons,
      Execution.charge, Prod.mk.injEq, Execution.mk.injEq, true_and, and_true]
    refine ⟨⟨by omega, by omega⟩, by omega⟩

end TwoPermutationPrototype.CheckActions
