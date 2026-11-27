import CommitGolfCandidate.Machine
import CommitGolfCandidate.PentaGroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted
import CommitGolfCandidate.CounterSaltWindows

/-! Deterministic fixed-oracle view and machine-state correspondence for `PentaGrouped.Action`. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

structure View where
  regs : Reg → Word
  mem : Memory

def View.reg (v : View) (r : Reg) (w : Word) : View :=
  ⟨fun k => if r = k ∧ k ≠ .x0 then w else v.regs k, v.mem⟩
def View.store (v : View) (addr : Nat) (w : Word) : View := ⟨v.regs, writeWord v.mem addr w⟩
def View.reply (v : View) (addr : Nat) (y : BitVec 1600) : View := ⟨v.regs, writeWindow v.mem addr (replyWords y)⟩

def viewStep (o : Oracle) (v : View) : Action → View
  | .offset rd _ _ a | .add rd _ _ a => v.reg rd (wordAddress a)
  | .load rd _ _ a => v.reg rd (v.mem a)
  | .store _ r _ a => v.store a (v.regs r)
  | .perm src dst => v.reply dst (o.permutation (packBuffer (window v.mem src)))

def Matches (s : MachineState) (v : View) :=
  (∀ r, s.getReg r = v.regs r) ∧ ∀ w < 2^33, memoryView s w = v.mem w

theorem matches_initial (s : MachineState) : Matches s ⟨s.getReg, memoryView s⟩ :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem register_put (s : MachineState) (r t : Reg) (w : Word) :
    (putReg s r w).getReg t = (if r = t ∧ t ≠ .x0 then w else s.getReg t) := by
  cases r <;> cases t <;> rfl

theorem matches_reg (s : MachineState) (v : View) (h : Matches s v) (r : Reg) (w : Word) :
    Matches (putReg s r w) (v.reg r w) := by
  refine ⟨fun t => ?_, fun j hj => ?_⟩
  · rw [register_put]; simp only [View.reg, h.1]
  · simpa only [putReg, memoryView, MachineState.getMem_setPC, MachineState.getMem_setReg, View.reg] using h.2 j hj

theorem matches_store (s : MachineState) (v : View) (h : Matches s v) (a : Nat) (ha : a < 2^33) (w : Word) :
    Matches (putWord s a w) (v.store a w) := by
  refine ⟨fun r => ?_, fun j hj => ?_⟩
  · exact (show (putWord s a w).getReg r = s.getReg r by cases r <;> rfl).trans (h.1 r)
  · change memoryView (s.setMem (wordAddress a) w) j = writeWord v.mem a w j
    rw [memory_at_store (by omega) (by omega)]
    simp only [writeWord, h.2 j hj]

theorem matches_reply (s : MachineState) (v : View) (h : Matches s v) (a : Nat) (ha : a + 25 ≤ 2^33)
    (y : BitVec 1600) : Matches (writeBits s (wordAddress a) y) (v.reply a y) := by
  refine ⟨fun r => (writeBits_register ..).trans (h.1 r), fun j hj => ?_⟩
  change memoryView (writeBits s (wordAddress a) y) j = writeWindow v.mem a (replyWords y) j
  rw [permutation_write_memory s a j y ha hj]
  simp only [writeWindow, h.2 j hj]

def fixedStep (o : Oracle) (s : MachineState) : Action → MachineState
  | .offset rd _ _ a | .add rd _ _ a => putReg s rd (wordAddress a)
  | .load rd _ _ a => putReg s rd (memoryView s a)
  | .store _ r _ a => putWord s a (s.getReg r)
  | .perm src dst => writeBits s (wordAddress dst) (o.permutation (packBuffer (window (memoryView s) src)))

theorem fixed_step (o : Oracle) (s : MachineState) (a : Action) :
    o.run (a.run s) = pure (fixedStep o s a, a.calls) := by
  cases a <;> simp only [Action.run, fixedStep, Action.calls, oracle_run_public_bind, oracle_run_pure, pure_bind] <;> rfl

theorem matches_step (o : Oracle) (s : MachineState) (v : View) (a : Action) (h : Matches s v)
    (ok : a.valid s) : Matches (fixedStep o s a) (viewStep o v a) := by
  cases a with
  | offset | add => exact matches_reg s v h _ _
  | load rd base imm addr =>
    have ha : addr + 1 ≤ 2^33 := ok.2
    simp only [fixedStep, viewStep, h.2 addr (by omega)]
    exact matches_reg s v h _ _
  | store base val imm addr =>
    have ha : addr + 1 ≤ 2^33 := ok.2
    simp only [fixedStep, viewStep, h.1 val]
    exact matches_store s v h addr (by omega) _
  | perm src dst =>
    obtain ⟨_, _, _, _, _, hs, hd⟩ := ok
    have windowEq : (window (memoryView s) src : Words 25) = window v.mem src := by
      funext j; apply h.2; have := j.isLt; omega
    simp only [fixedStep, viewStep, windowEq]; exact matches_reply s v h dst hd _

theorem fixed_ops (o : Oracle) (s : MachineState) (ops : List Action) :
    o.run (runOps ops s) = pure (ops.foldl (fixedStep o) s, opCalls ops) := by
  induction ops generalizing s with
  | nil => exact oracle_run_pure ..
  | cons a rest ih =>
    rw [runOps, oracle_run_bind, fixed_step, pure_bind]
    simp only [ih, pure_bind, List.foldl_cons, opCalls, List.map_cons, List.sum_cons]

theorem fixed_in_support (o : Oracle) (s : MachineState) (a : Action) :
    fixedStep o s a ∈ support (a.run s) := by
  apply writer_support (o.world.withAddCost Oracle.callCost) _ (fixedStep o s a, a.calls)
  change (_, _) ∈ support (o.run (a.run s))
  rw [fixed_step]; simp

theorem matches_ops (o : Oracle) (s : MachineState) (v : View) (ops : List Action)
    (ok : validOps ops s) (h : Matches s v) :
    Matches (ops.foldl (fixedStep o) s) (ops.foldl (viewStep o) v) := by
  induction ops generalizing s v with
  | nil => exact h
  | cons a rest ih =>
    exact ih _ _ (ok.2 _ (fixed_in_support o s a)) (matches_step o s v a h ok.1)

end TwoPermutationPrototype.PentaGrouped
