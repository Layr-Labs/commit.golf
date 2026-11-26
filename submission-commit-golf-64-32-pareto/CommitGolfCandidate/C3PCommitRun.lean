import CommitGolfCandidate.C3PCommitBlock
import CommitGolfCandidate.TwoPermutationHybridPhase
import CommitGolfCandidate.TwoPermutationCommitSetup

/-! # The whole paired commit run

Setup (words 0..19) and `jal zero,<18517>`, 8,192 blocks each followed by the latch
(`beq s4,s5,<45172>`, then `jal zero,<18517>` except after the last block), the exit
(45172..45177) into the leader's parent levels (paired loop 1) and the root:
276,964,482 steps, 1,266,820,219 cycles, 83,886,079 calls. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (address_up address_down addi_mem addi_pc word_access)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000
attribute [local irreducible] execute packedWideCommitImage blockTrace hybridParentPhase

/-! ### Setup and the first jump -/

def firstState (s : MachineState) : MachineState := (runOpsC s setupOps).setPC (cpc blockStart)

theorem setup_run (s : MachineState) (entry : CommitEntry s) (fuel : Nat) :
    execute packedWideCommitImage (21 + fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (firstState s) true; return r.charge 21 0) := by
  have spc : s.pc = cpc 0 := entry.pc
  have runS : ∀ X, execute packedWideCommitImage (20 + X) s true =
      (do let r ← execute packedWideCommitImage X (runOpsC s setupOps) true; return r.charge 20 0) := fun X =>
    alu_run_c s 0 setupOps X spc
      (fun j h u hu => by rw [← op_at_eq setupOps j h]; exact fetch_setup j h u (by simpa using hu))
      (by intro j h t; have hj : j < 19 := (by change j + 1 < 20 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 20 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 20 at h; interval_cases j <;> rfl)
  have spc20 : (runOpsC s setupOps).pc = cpc 20 := by
    rw [show (runOpsC s setupOps).pc = s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
      + 4 + 4 from rfl, spc]; decide
  have jump : ordinaryStep (runOpsC s setupOps) (.base (.JAL .x0 73988)) = some (firstState s) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, spc20, firstState]
    simp only [↓reduceIte, Option.some.injEq]
    have : cpc 20 + signExtend21 73988 = cpc blockStart := by decide
    rw [this]
    rfl
  rw [show 21 + fuel = 20 + (1 + fuel) by omega, runS,
    ordinary_c _ (firstState s) _ _ (fetch_first_jump _ spc20) jump rfl]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

theorem first_regs (s : MachineState) (entry : CommitEntry s) :
    BlockRegsP (firstState s) 0 ∧ (firstState s).getReg .x21 = wordAddress (D0 8192 - 25) ∧
    (firstState s).getReg .x8 = 4294971392 ∧ (firstState s).getReg .x9 = 4294971424 ∧
    (firstState s).getReg .x19 = 536870912 := by
  have regs (g : Reg) : (firstState s).getReg g = (runOpsC s setupOps).getReg g := by
    simp only [firstState, MachineState.getReg_setPC]
  refine ⟨⟨rfl, ?_, ?_, by decide⟩, ?_, ?_, ?_, ?_⟩ <;> rw [regs] <;>
    simp only [runOpsC, setupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      and_self, reg_zero_c]
  · rw [entry.message]; decide
  · rw [entry.heap]; decide
  · rw [entry.heap]; decide
  · rw [entry.commitment]; decide
  · rw [entry.heap]; decide
  · decide

/-! ### The latch and the block loop -/

def latchPC (g : Nat) : Word := if g + 1 = 8192 then cpc 45172 else cpc blockStart
def latchCost (g : Nat) : Nat := if g + 1 = 8192 then 1 else 2

theorem latch_run (t : MachineState) (g : Nat) (hg : g < 8192) (pc : t.pc = cpc 45156)
    (x20 : t.getReg .x20 = wordAddress (D0 (g + 1) - 25)) (x21 : t.getReg .x21 = wordAddress (D0 8192 - 25))
    (fuel : Nat) :
    execute packedWideCommitImage (latchCost g + fuel) t true =
      (do let r ← execute packedWideCommitImage fuel (t.setPC (latchPC g)) true; return r.charge (latchCost g) 0) := by
  have db := d0_bounds g hg
  have equal : t.getReg .x20 = t.getReg .x21 ↔ g + 1 = 8192 := by
    rw [x20, x21]
    constructor
    · intro same
      have index := wordAddress_injective_of_bound (by unfold D0 replyW at *; omega)
        (by unfold D0 replyW; omega) same
      unfold D0 at index; omega
    · intro h; rw [h]
  by_cases last : g + 1 = 8192
  · have step : ordinaryStep t (.base (.BEQ .x20 .x21 64)) = some (t.setPC (cpc 45172)) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, equal.mpr last]
      exact congrArg t.setPC (by decide)
    rw [latchCost, if_pos last, latchPC, if_pos last, Nat.add_comm 1 fuel,
      CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_latch t pc) step]
    rfl
  · let mid := t.setPC (cpc 45157)
    have diff : t.getReg .x20 ≠ t.getReg .x21 := fun h => last (equal.mp h)
    have step : ordinaryStep t (.base (.BEQ .x20 .x21 64)) = some mid := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, diff, mid]
      exact congrArg t.setPC (by decide)
    have jump : ordinaryStep mid (.base (.JAL .x0 1990592)) = some (t.setPC (cpc blockStart)) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, mid, MachineState.setReg, MachineState.setPC]
      decide
    rw [latchCost, if_neg last, latchPC, if_neg last, show 2 + fuel = 1 + (1 + fuel) by omega,
      ordinary_c t mid _ _ (fetch_latch t pc) step rfl,
      ordinary_c mid _ _ _ (fetch_loop_jump mid rfl) jump rfl]
    simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

def leafPhaseP : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n + 1, g, s => do let t ← blockTrace g s; leafPhaseP n (g + 1) (t.setPC (latchPC g))

def blocksSteps (n : Nat) : Nat := 26639 * n + (2 * n - 1)
def blocksCycles (n : Nat) : Nat := 133135 * n + (2 * n - 1)

structure LoopRegs (s : MachineState) (g : Nat) (x8 x9 x19 : Word) : Prop where
  regs : BlockRegsP s g
  stop : s.getReg .x21 = wordAddress (D0 8192 - 25)
  out : s.getReg .x8 = x8
  heap : s.getReg .x9 = x9
  stride : s.getReg .x19 = x19

theorem blocks_run (x8 x9 x19 : Word) : ∀ n g (s : MachineState), g + n = 8192 → LoopRegs s g x8 x9 x19 → ∀ fuel,
    execute packedWideCommitImage (blocksSteps n + fuel) s true =
      (do let t ← leafPhaseP n g s
          let res ← execute packedWideCommitImage fuel t true
          return res.charge (blocksCycles n) (8192 * n)) := by
  intro n
  induction n with
  | zero =>
    intro g s _ _ fuel
    have h : ∀ res : Execution, res.charge 0 0 = res := fun res => by simp [Execution.charge]
    simp only [leafPhaseP, blocksSteps, blocksCycles, Nat.mul_zero, Nat.zero_add, Nat.zero_sub, pure_bind, h, bind_pure]
  | succ n ih =>
    intro g s total inv fuel
    have hg : g < 8192 := by omega
    rw [show blocksSteps (n + 1) + fuel = 26639 + (latchCost g + (blocksSteps n + fuel)) by
        unfold blocksSteps latchCost; split <;> omega,
      block_run s g inv.regs]
    simp only [leafPhaseP, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro t reached
    obtain ⟨tpc, t10, t20, _, tk⟩ := block_post s g inv.regs t reached
    have t21 : t.getReg .x21 = wordAddress (D0 8192 - 25) :=
      (tk .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.stop
    rw [latch_run t g hg tpc t20 t21]
    simp only [bind_assoc, pure_bind]
    by_cases last : n = 0
    · subst last
      have hl : latchCost g = 1 := by unfold latchCost; rw [if_pos (by omega)]
      rw [hl]
      simp only [leafPhaseP, blocksCycles, pure_bind, charge_charge, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
        Nat.zero_add, Nat.mul_one, show blocksSteps 0 = 0 from rfl]
    · have next : LoopRegs (t.setPC (latchPC g)) (g + 1) x8 x9 x19 := by
        have np : latchPC g = cpc blockStart := by unfold latchPC; rw [if_neg (by omega)]
        refine ⟨⟨by rw [np]; rfl, by simpa using t10, by simpa using t20, by omega⟩, by simpa using t21, ?_, ?_, ?_⟩
        · simp only [MachineState.getReg_setPC]
          exact (tk .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.out
        · simp only [MachineState.getReg_setPC]
          exact (tk .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.heap
        · simp only [MachineState.getReg_setPC]
          exact (tk .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            inv.stride
      rw [ih (g + 1) _ (by omega) next]
      simp only [bind_assoc, pure_bind, charge_charge]
      have hl : latchCost g = 2 := by unfold latchCost; rw [if_neg (by omega)]
      rw [hl, show 133135 + 2 + blocksCycles n = blocksCycles (n + 1) by unfold blocksCycles; omega,
        show 8192 + 0 + 8192 * n = 8192 * (n + 1) by ring]

theorem blocks_post (x8 x9 x19 : Word) : ∀ n g (s : MachineState), g + n = 8192 → 0 < n → LoopRegs s g x8 x9 x19 →
    ∀ t ∈ support (leafPhaseP n g s), t.pc = cpc 45172 ∧ t.getReg .x5 = 0 ∧
      t.getReg .x21 = wordAddress (D0 8192 - 25) ∧ t.getReg .x8 = x8 ∧ t.getReg .x9 = x9 ∧ t.getReg .x19 = x19 := by
  intro n
  induction n with
  | zero => intro g s _ h; omega
  | succ n ih =>
    intro g s total _ inv t reached
    have hg : g < 8192 := by omega
    simp only [leafPhaseP, mem_support_bind_iff] at reached
    obtain ⟨u, hu, rest⟩ := reached
    obtain ⟨upc, u10, u20, u5, uk⟩ := block_post s g inv.regs u hu
    have k (reg : Reg) (a : reg ≠ .x5) (b : reg ≠ .x10) (c : reg ≠ .x11) (d : reg ≠ .x12) (e : reg ≠ .x13)
        (f : reg ≠ .x18) (h : reg ≠ .x20) : (u.setPC (latchPC g)).getReg reg = s.getReg reg := by
      simp only [MachineState.getReg_setPC]; exact uk reg a b c d e f h
    by_cases last : n = 0
    · subst last
      simp only [leafPhaseP, support_pure, Set.mem_singleton_iff] at rest
      subst rest
      have np : latchPC g = cpc 45172 := by unfold latchPC; rw [if_pos (by omega)]
      refine ⟨by rw [np]; rfl, by simpa using u5, ?_, ?_, ?_, ?_⟩
      · exact (k .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.stop
      · exact (k .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.out
      · exact (k .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.heap
      · exact (k .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          inv.stride
    · have np : latchPC g = cpc blockStart := by unfold latchPC; rw [if_neg (by omega)]
      have next : LoopRegs (u.setPC (latchPC g)) (g + 1) x8 x9 x19 :=
        ⟨⟨by rw [np]; rfl, by simpa using u10, by simpa using u20, by omega⟩,
          (k .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.stop,
          (k .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.out,
          (k .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.heap,
          (k .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.stride⟩
      exact ih (g + 1) _ (by omega) (by omega) next t rest

/-! ### Exit, parents, root -/

def exitState (t : MachineState) : MachineState := (runOpsC t exitOps).setPC 217572

theorem exit_run (t : MachineState) (pc : t.pc = cpc 45172) (fuel : Nat) :
    execute packedWideCommitImage (6 + fuel) t true =
      (do let r ← execute packedWideCommitImage fuel (exitState t) true; return r.charge 6 0) := by
  have runX : ∀ X, execute packedWideCommitImage (5 + X) t true =
      (do let r ← execute packedWideCommitImage X (runOpsC t exitOps) true; return r.charge 5 0) := fun X =>
    alu_run_c t 45172 exitOps X pc
      (fun j h u hu => by rw [← op_at_eq exitOps j h]; exact fetch_exit j h u hu)
      (by intro j h t; have hj : j < 4 := (by change j + 1 < 5 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 5 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 5 at h; interval_cases j <;> rfl)
  have xpc : (runOpsC t exitOps).pc = cpc 45177 := by
    rw [show (runOpsC t exitOps).pc = t.pc + 4 + 4 + 4 + 4 + 4 from rfl, pc]; decide
  have jump : ordinaryStep (runOpsC t exitOps) (.base (.JAL .x0 32768)) = some (exitState t) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, xpc, exitState]
    simp only [↓reduceIte, Option.some.injEq]
    have : cpc 45177 + signExtend21 32768 = 217572 := by decide
    rw [this]
    rfl
  rw [show 6 + fuel = 5 + (1 + fuel) by omega, runX,
    ordinary_c _ (exitState t) _ _ (fetch_exit_jump _ xpc) jump rfl]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

theorem exit_regs (t : MachineState) (x5 : t.getReg .x5 = 0) (x21 : t.getReg .x21 = wordAddress (D0 8192 - 25))
    (x9 : t.getReg .x9 = 4294971424) (x19 : t.getReg .x19 = 536870912) :
    ParentRegsP (exitState t) (2 ^ 24 - 1) ∧ (exitState t).pc = 217572 ∧
      (exitState t).getReg .x8 = t.getReg .x8 := by
  have regs (g : Reg) : (exitState t).getReg g = (runOpsC t exitOps).getReg g := by
    simp only [exitState, MachineState.getReg_setPC]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩ <;> rw [regs] <;>
    simp only [runOpsC, exitOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      and_self, reg_zero_c]
  · rw [x21]; decide
  · rw [x9, x19]; decide
  · exact x5
  · decide
  · decide
  · rw [x9]; decide

/-- The paired commit as an oracle computation with private coins. -/
def commitTraceP (initial : MachineState) : OracleComp World Execution := do
  let leaves ← leafPhaseP 8192 0 (firstState initial)
  let parents ← hybridParentPhase (exitState leaves)
  return ⟨.success, rootPrefix parents 10, 1266820219, 83886079⟩

theorem paired_commit_execution (initial : MachineState) (entry : CommitEntry initial) (fuel : Nat) :
    execute packedWideCommitImage (276964482 + fuel) initial true = commitTraceP initial := by
  obtain ⟨regs0, x21, x8, x9, x19⟩ := first_regs initial entry
  have inv0 : LoopRegs (firstState initial) 0 4294971392 4294971424 536870912 := ⟨regs0, x21, x8, x9, x19⟩
  rw [show 276964482 + fuel = 21 + (blocksSteps 8192 + (6 + (58721373 + (11 + fuel)))) by
      unfold blocksSteps; omega,
    setup_run initial entry, blocks_run _ _ _ 8192 0 _ (by omega) inv0]
  simp only [commitTraceP, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  obtain ⟨lpc, l5, l21, l8, l9, l19⟩ := blocks_post _ _ _ 8192 0 _ (by omega) (by omega) inv0 leaves reached
  obtain ⟨pregs, ppc, p8⟩ := exit_regs leaves l5 l21 l9 l19
  rw [exit_run leaves lpc, hybrid_parent_phase (exitState leaves) _ pregs ppc (p8.trans l8)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro parents hit
  obtain ⟨_, rpc, r8⟩ := hybrid_parent_phase_post (exitState leaves) pregs ppc (p8.trans l8) hit
  have r9 : parents.getReg .x9 = 4294971424 := by
    have h := (hybrid_parent_phase_post (exitState leaves) pregs ppc (p8.trans l8) hit).1.heap
    rw [h]; rfl
  rw [execute_packed_root parents rpc r9 (r8.trans (p8.trans l8))]
  simp only [pure_bind, charge_charge, Execution.charge]
  unfold blocksCycles
  norm_num

end TwoPermutationPrototype.RV64.C3P
