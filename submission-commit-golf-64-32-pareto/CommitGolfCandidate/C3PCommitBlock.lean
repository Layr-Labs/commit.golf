import CommitGolfCandidate.C3PCommitPass23

/-! # One block of the paired commit loop (2,048 leaves, 1,024 pairs)

`blockTrace g` is the prologue, pass 1 over the block's pairs, the pass-2 setup, pass 2, the pass-3
setup, pass 3 and the epilogue: 26,639 steps, 133,135 cycles, 8,192 calls. Block `g` starts with
`a0` at its first message word `E0 g = 512 + 65536 g` and `s4` at `D0 g - 25`, where `D0 g` is the
reply word of its first leaf; it ends with both advanced by one block and the pc at the latch. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (address_up address_down addi_mem addi_pc word_access)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000
attribute [local irreducible] execute packedWideCommitImage

/-- Message word of leaf `2048 g` and reply word of leaf `2048 g`. -/
def E0 (g : Nat) : Nat := 512 + 65536 * g
def replyW : Nat := 516 + 32 * 2 ^ 24 + 2 ^ 26 + 21
def D0 (g : Nat) : Nat := replyW + 51200 * g

/-! ### Pair loops -/

def pass1Loop (E : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n + 1, p, s => do let t ← p1PairTrace s (E + 64 * p); pass1Loop E n (p + 1) t

def pass2Loop (E : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n + 1, p, s => do
    let w ← liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    pass2Loop E n (p + 1) (p2After s (E + 64 * p) w)

def pass3Loop (E D : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n + 1, p, s => do let t ← p3PairTrace s (E + 64 * p) (D + 50 * p); pass3Loop E D n (p + 1) t

structure Loop1 (s : MachineState) (E p : Nat) : Prop where
  pc : s.pc = cpc (p1Index p)
  source : s.getReg .x10 = wordAddress (E + 64 * p - 32)
  low : 32 ≤ E
  bound : E + 65536 ≤ 2 ^ 33
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0

theorem pass1_run (E : Nat) : ∀ n p (s : MachineState), p + n ≤ 1024 → Loop1 s E p → ∀ fuel,
    execute packedWideCommitImage (16 * n + fuel) s true =
      (do let t ← pass1Loop E n p s
          let res ← execute packedWideCommitImage fuel t true
          return res.charge (58 * n) (6 * n)) := by
  intro n
  induction n with
  | zero =>
    intro p s _ _ fuel
    have h : ∀ res : Execution, res.charge 0 0 = res := fun res => by simp [Execution.charge]
    simp only [pass1Loop, Nat.mul_zero, Nat.zero_add, pure_bind, h, bind_pure]
  | succ n ih =>
    intro p s total inv fuel
    have ready : P1PairReady s p (E + 64 * p) :=
      ⟨inv.pc, inv.source, by have := inv.low; omega, by have := inv.bound; omega, inv.selector, inv.size,
        inv.primitive, by omega⟩
    rw [show 16 * (n + 1) + fuel = 16 + (16 * n + fuel) by ring, execute_p1_pair s p _ ready]
    simp only [pass1Loop, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro t reached
    -- the pair's end state, for its answers
    simp only [p1PairTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨a1, _, a2, _, a3, _, a4, _, a5, _, a6, _, rfl⟩ := reached
    have R := p1_pair_regs s p (E + 64 * p) ready a1 a2 a3 a4 a5 a6
    have next : Loop1 (p1w6 s (E + 64 * p) a1 a2 a3 a4 a5 a6) E (p + 1) := by
      refine ⟨R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_, inv.low, inv.bound, ?_, ?_, ?_⟩
      · rw [R.2.2.2.2.2.2.2.2.2.2.2.2.1]; congr 1 <;> omega
      · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x5 (by decide) (by decide)).2.2.2.2.2.2).trans inv.selector
      · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x11 (by decide) (by decide)).2.2.2.2.2.2).trans inv.size
      · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x13 (by decide) (by decide)).2.2.2.2.2.2).trans inv.primitive
    rw [ih (p + 1) _ (by omega) next]
    simp only [bind_assoc, pure_bind, charge_charge]
    rw [show 58 + 58 * n = 58 * (n + 1) by ring, show 6 + 6 * n = 6 * (n + 1) by ring]

theorem pass1_post (E : Nat) : ∀ n p (s : MachineState), p + n ≤ 1024 → Loop1 s E p →
    ∀ t ∈ support (pass1Loop E n p s), Loop1 t E (p + n) ∧ (∀ g, g ≠ .x10 → g ≠ .x12 → t.getReg g = s.getReg g) := by
  intro n
  induction n with
  | zero =>
    intro p s _ inv t reached
    simp only [pass1Loop, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨inv, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro p s total inv t reached
    have ready : P1PairReady s p (E + 64 * p) :=
      ⟨inv.pc, inv.source, by have := inv.low; omega, by have := inv.bound; omega, inv.selector, inv.size,
        inv.primitive, by omega⟩
    simp only [pass1Loop, mem_support_bind_iff] at reached
    obtain ⟨u, hu, rest⟩ := reached
    simp only [p1PairTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hu
    obtain ⟨a1, _, a2, _, a3, _, a4, _, a5, _, a6, _, rfl⟩ := hu
    have R := p1_pair_regs s p (E + 64 * p) ready a1 a2 a3 a4 a5 a6
    have next : Loop1 (p1w6 s (E + 64 * p) a1 a2 a3 a4 a5 a6) E (p + 1) := by
      refine ⟨R.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_, inv.low, inv.bound, ?_, ?_, ?_⟩
      · rw [R.2.2.2.2.2.2.2.2.2.2.2.2.1]; congr 1 <;> omega
      · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x5 (by decide) (by decide)).2.2.2.2.2.2).trans inv.selector
      · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x11 (by decide) (by decide)).2.2.2.2.2.2).trans inv.size
      · exact ((R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 .x13 (by decide) (by decide)).2.2.2.2.2.2).trans inv.primitive
    obtain ⟨tail, keep⟩ := ih (p + 1) _ (by omega) next t rest
    refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using tail, fun g h10 h12 => ?_⟩
    rw [keep g h10 h12]
    exact (R.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g h10 h12).2.2.2.2.2.2

structure Loop2 (s : MachineState) (E p : Nat) : Prop where
  pc : s.pc = cpc (p2Index p)
  source : s.getReg .x10 = wordAddress (E + 64 * p - 34)
  low : 34 ≤ E
  bound : E + 65536 ≤ 2 ^ 33
  selector : s.getReg .x5 = 2
  size : s.getReg .x11 = 32

theorem loop2_next (s : MachineState) (E p : Nat) (inv : Loop2 s E p) (hp : p < 1024) (w : BitVec 256) :
    Loop2 (p2After s (E + 64 * p) w) E (p + 1) ∧ (∀ g, g ≠ .x10 → (p2After s (E + 64 * p) w).getReg g = s.getReg g) := by
  have ready : P2PairReady s p (E + 64 * p) :=
    ⟨inv.pc, inv.source, by have := inv.low; omega, by have := inv.bound; omega, inv.selector, inv.size, hp⟩
  obtain ⟨_, _, a10, apc, keep⟩ := p2_after_facts s p (E + 64 * p) ready w
  refine ⟨⟨apc, ?_, inv.low, inv.bound, (keep .x5 (by decide)).1.trans inv.selector,
    (keep .x11 (by decide)).1.trans inv.size⟩, fun g h => (keep g h).1⟩
  rw [a10]; congr 1 <;> omega

theorem pass2_run (E : Nat) : ∀ n p (s : MachineState), p + n ≤ 1024 → Loop2 s E p → ∀ fuel,
    execute packedWideCommitImage (2 * n + fuel) s true =
      (do let t ← pass2Loop E n p s
          let res ← execute packedWideCommitImage fuel t true
          return res.charge (6 * n) 0) := by
  intro n
  induction n with
  | zero =>
    intro p s _ _ fuel
    have h : ∀ res : Execution, res.charge 0 0 = res := fun res => by simp [Execution.charge]
    simp only [pass2Loop, Nat.mul_zero, Nat.zero_add, pure_bind, h, bind_pure]
  | succ n ih =>
    intro p s total inv fuel
    have ready : P2PairReady s p (E + 64 * p) :=
      ⟨inv.pc, inv.source, by have := inv.low; omega, by have := inv.bound; omega, inv.selector, inv.size, by omega⟩
    rw [show 2 * (n + 1) + fuel = 2 + (2 * n + fuel) by ring, execute_p2_pair s p _ ready]
    simp only [pass2Loop, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro w _
    rw [ih (p + 1) _ (by omega) (loop2_next s E p inv (by omega) w).1]
    simp only [bind_assoc, pure_bind, charge_charge]
    rw [show 6 + 6 * n = 6 * (n + 1) by ring]

theorem pass2_post (E : Nat) : ∀ n p (s : MachineState), p + n ≤ 1024 → Loop2 s E p →
    ∀ t ∈ support (pass2Loop E n p s), Loop2 t E (p + n) ∧ (∀ g, g ≠ .x10 → t.getReg g = s.getReg g) := by
  intro n
  induction n with
  | zero =>
    intro p s _ inv t reached
    simp only [pass2Loop, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨inv, fun _ _ => rfl⟩
  | succ n ih =>
    intro p s total inv t reached
    simp only [pass2Loop, mem_support_bind_iff] at reached
    obtain ⟨w, _, rest⟩ := reached
    have step := loop2_next s E p inv (by omega) w
    obtain ⟨tail, keep⟩ := ih (p + 1) _ (by omega) step.1 t rest
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using tail, fun g h => (keep g h).trans (step.2 g h)⟩

structure Loop3 (s : MachineState) (E D p : Nat) : Prop where
  pc : s.pc = cpc (p3Index p)
  source : s.getReg .x10 = wordAddress (E + 64 * p - 32)
  target : s.getReg .x12 = wordAddress (D + 50 * p - 25)
  low : 32 ≤ E
  lowD : 25 ≤ D
  bound : E + 65536 ≤ 2 ^ 33
  boundD : D + 51200 ≤ 2 ^ 33
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1

theorem loop3_next (s : MachineState) (E D p : Nat) (inv : Loop3 s E D p) (hp : p < 1024) (y1 y2 : Sampling.Block) :
    Loop3 (p3w2 s (D + 50 * p) y1 y2) E D (p + 1) ∧
      (∀ g, g ≠ .x10 → g ≠ .x12 → (p3w2 s (D + 50 * p) y1 y2).getReg g = s.getReg g) := by
  have ready : P3PairReady s p (E + 64 * p) (D + 50 * p) :=
    ⟨inv.pc, inv.source, inv.target, by have := inv.low; omega, by have := inv.lowD; omega,
      by have := inv.bound; omega, by have := inv.boundD; omega, inv.selector, inv.size, inv.primitive, hp⟩
  have P := p3_facts s p (E + 64 * p) (D + 50 * p) ready y1 y2
  refine ⟨⟨P.2.2.2.2.2.2.2.2.1, ?_, ?_, inv.low, inv.lowD, inv.bound, inv.boundD,
    ((P.2.2.2.2.2.2.2.2.2.1 .x5 (by decide) (by decide)).2.2).trans inv.selector,
    ((P.2.2.2.2.2.2.2.2.2.1 .x11 (by decide) (by decide)).2.2).trans inv.size,
    ((P.2.2.2.2.2.2.2.2.2.1 .x13 (by decide) (by decide)).2.2).trans inv.primitive⟩,
    fun g a b => (P.2.2.2.2.2.2.2.2.2.1 g a b).2.2⟩
  · rw [P.2.2.2.2.2.2.1]; congr 1 <;> omega
  · rw [P.2.2.2.2.2.2.2.1]; congr 1 <;> omega

theorem pass3_run (E D : Nat) : ∀ n p (s : MachineState), p + n ≤ 1024 → Loop3 s E D p → ∀ fuel,
    execute packedWideCommitImage (8 * n + fuel) s true =
      (do let t ← pass3Loop E D n p s
          let res ← execute packedWideCommitImage fuel t true
          return res.charge (66 * n) (2 * n)) := by
  intro n
  induction n with
  | zero =>
    intro p s _ _ fuel
    have h : ∀ res : Execution, res.charge 0 0 = res := fun res => by simp [Execution.charge]
    simp only [pass3Loop, Nat.mul_zero, Nat.zero_add, pure_bind, h, bind_pure]
  | succ n ih =>
    intro p s total inv fuel
    have ready : P3PairReady s p (E + 64 * p) (D + 50 * p) :=
      ⟨inv.pc, inv.source, inv.target, by have := inv.low; omega, by have := inv.lowD; omega,
        by have := inv.bound; omega, by have := inv.boundD; omega, inv.selector, inv.size, inv.primitive, by omega⟩
    rw [show 8 * (n + 1) + fuel = 8 + (8 * n + fuel) by ring, execute_p3_pair s p _ _ ready]
    simp only [pass3Loop, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro t reached
    simp only [p3PairTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨y1, _, y2, _, rfl⟩ := reached
    rw [ih (p + 1) _ (by omega) (loop3_next s E D p inv (by omega) y1 y2).1]
    simp only [bind_assoc, pure_bind, charge_charge]
    rw [show 66 + 66 * n = 66 * (n + 1) by ring, show 2 + 2 * n = 2 * (n + 1) by ring]

theorem pass3_post (E D : Nat) : ∀ n p (s : MachineState), p + n ≤ 1024 → Loop3 s E D p →
    ∀ t ∈ support (pass3Loop E D n p s), Loop3 t E D (p + n) ∧
      (∀ g, g ≠ .x10 → g ≠ .x12 → t.getReg g = s.getReg g) := by
  intro n
  induction n with
  | zero =>
    intro p s _ inv t reached
    simp only [pass3Loop, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨inv, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro p s total inv t reached
    simp only [pass3Loop, mem_support_bind_iff] at reached
    obtain ⟨u, hu, rest⟩ := reached
    simp only [p3PairTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hu
    obtain ⟨y1, _, y2, _, rfl⟩ := hu
    have step := loop3_next s E D p inv (by omega) y1 y2
    obtain ⟨tail, keep⟩ := ih (p + 1) _ (by omega) step.1 t rest
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using tail,
      fun g a b => (keep g a b).trans (step.2 g a b)⟩

/-! ### Straight-line ALU words -/

def runOpsC (s : MachineState) (ops : List Instr) : MachineState := ops.foldl execInstrBr s

theorem run_ops_c_append (s : MachineState) (a b : List Instr) : runOpsC s (a ++ b) = runOpsC (runOpsC s a) b := by
  simp [runOpsC, List.foldl_append]

theorem alu_run_c (s : MachineState) (start : Nat) (ops : List Instr) (fuel : Nat)
    (pc : s.pc = cpc start)
    (code : ∀ j (h : j < ops.length) (u : MachineState), u.pc = cpc (start + j) →
      fetch packedWideCommitImage u = some (.base ops[j]))
    (plain : ∀ j (h : j + 1 < ops.length) (t : MachineState), (execInstrBr t ops[j]).pc = t.pc + 4)
    (alu : ∀ j (h : j < ops.length) (t : MachineState), ordinaryStep t (.base ops[j]) = some (execInstrBr t ops[j]))
    (unit : ∀ j (h : j < ops.length), instructionCycles (.base ops[j]) = 1) :
    execute packedWideCommitImage (ops.length + fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (runOpsC s ops) true; return r.charge ops.length 0) := by
  have pcs : ∀ j, j < ops.length → (runOpsC s (ops.take j)).pc = cpc (start + j) := by
    intro j
    induction j with
    | zero => intro _; simpa [runOpsC] using pc
    | succ j ih =>
      intro h
      rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some, run_ops_c_append]
      change (execInstrBr (runOpsC s (ops.take j)) ops[j]).pc = _
      rw [plain j h, ih (by omega), cpc_next, Nat.add_assoc]
  have final : runOpsC s ops = runOpsC s (ops.take ops.length) := by rw [List.take_length]
  rw [final]
  apply CommitGolfCandidate.execute_unit_steps (states := fun j => runOpsC s (ops.take j))
  intro j h
  refine ⟨.base ops[j], code j h _ (pcs j h), ?_, unit j h⟩
  rw [List.take_succ, List.getElem?_eq_getElem h, Option.toList_some, run_ops_c_append]
  exact alu j h _

/-! ### The block -/

def blockTrace (g : Nat) (s : MachineState) : OracleComp World MachineState := do
  let t1 ← pass1Loop (E0 g) 1024 0 (runOpsC s prologueOps)
  let t2 ← pass2Loop (E0 g) 1024 0 (runOpsC t1 p2SetupOps)
  let t3 ← pass3Loop (E0 g) (D0 g) 1024 0 (runOpsC t2 p3SetupOps)
  pure (runOpsC t3 epilogueOps)

structure BlockRegsP (s : MachineState) (g : Nat) : Prop where
  pc : s.pc = cpc blockStart
  source : s.getReg .x10 = wordAddress (E0 g)
  reply : s.getReg .x20 = wordAddress (D0 g - 25)
  block : g < 8192

private theorem immm256 : signExtend12 (3840 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 32) := by decide
private theorem immm272 : signExtend12 (3824 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 8 * 34) := by decide
private theorem imm256 : signExtend12 (256 : BitVec 12) = BitVec.ofNat 64 (8 * 32) := by decide

theorem op_at_eq (ops : List Instr) (j : Nat) (h : j < ops.length) : opAt ops j = ops[j] := by
  simp [opAt, List.getElem?_eq_getElem h]

theorem reg_zero_c (s : MachineState) : s.getReg .x0 = 0 := rfl

theorem prologue_facts (s : MachineState) :
    (runOpsC s prologueOps).getReg .x18 = s.getReg .x10 + signExtend12 0 ∧
    (runOpsC s prologueOps).getReg .x5 = 0 ∧ (runOpsC s prologueOps).getReg .x11 = 64 ∧
    (runOpsC s prologueOps).getReg .x13 = 0 ∧
    (runOpsC s prologueOps).getReg .x10 = s.getReg .x10 + signExtend12 3840 ∧
    (runOpsC s prologueOps).pc = s.pc + 4 + 4 + 4 + 4 + 4 ∧
    ∀ g, g ≠ .x18 → g ≠ .x5 → g ≠ .x11 → g ≠ .x13 → g ≠ .x10 → (runOpsC s prologueOps).getReg g = s.getReg g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [runOpsC, prologueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · simp only [runOpsC, prologueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, prologueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, prologueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, prologueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · intro g a b c d e
    simp [runOpsC, prologueOps, execInstrBr, Opening.getReg_setReg, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d,
      Ne.symm e]

theorem p2_setup_facts (t : MachineState) :
    (runOpsC t p2SetupOps).getReg .x5 = 2 ∧ (runOpsC t p2SetupOps).getReg .x11 = 32 ∧
    (runOpsC t p2SetupOps).getReg .x10 = t.getReg .x18 + signExtend12 3824 ∧
    (runOpsC t p2SetupOps).pc = t.pc + 4 + 4 + 4 ∧
    ∀ g, g ≠ .x5 → g ≠ .x11 → g ≠ .x10 → (runOpsC t p2SetupOps).getReg g = t.getReg g := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp only [runOpsC, p2SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, p2SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, p2SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · intro g a b c
    simp [runOpsC, p2SetupOps, execInstrBr, Opening.getReg_setReg, Ne.symm a, Ne.symm b, Ne.symm c]

theorem p3_setup_facts (t : MachineState) :
    (runOpsC t p3SetupOps).getReg .x5 = 0 ∧ (runOpsC t p3SetupOps).getReg .x11 = 200 ∧
    (runOpsC t p3SetupOps).getReg .x13 = 1 ∧
    (runOpsC t p3SetupOps).getReg .x10 = t.getReg .x18 + signExtend12 3840 ∧
    (runOpsC t p3SetupOps).getReg .x12 = t.getReg .x20 + signExtend12 0 ∧
    (runOpsC t p3SetupOps).pc = t.pc + 4 + 4 + 4 + 4 + 4 ∧
    ∀ g, g ≠ .x5 → g ≠ .x11 → g ≠ .x13 → g ≠ .x10 → g ≠ .x12 → (runOpsC t p3SetupOps).getReg g = t.getReg g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [runOpsC, p3SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, p3SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, p3SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]; rw [reg_zero_c]; decide
  · simp only [runOpsC, p3SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · simp only [runOpsC, p3SetupOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · intro g a b c d e
    simp [runOpsC, p3SetupOps, execInstrBr, Opening.getReg_setReg, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d,
      Ne.symm e]

theorem epilogue_facts (t : MachineState) :
    (runOpsC t epilogueOps).getReg .x20 = t.getReg .x12 + signExtend12 0 ∧
    (runOpsC t epilogueOps).getReg .x10 = t.getReg .x10 + signExtend12 256 ∧
    (runOpsC t epilogueOps).pc = t.pc + 4 + 4 ∧
    ∀ g, g ≠ .x20 → g ≠ .x10 → (runOpsC t epilogueOps).getReg g = t.getReg g := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp only [runOpsC, epilogueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · simp only [runOpsC, epilogueOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte, and_self]
  · intro g a b
    simp [runOpsC, epilogueOps, execInstrBr, Opening.getReg_setReg, Ne.symm a, Ne.symm b]

theorem e0_bounds (g : Nat) (hg : g < 8192) : 34 ≤ E0 g ∧ E0 g + 65536 ≤ 2 ^ 33 ∧ E0 (g + 1) = E0 g + 65536 := by
  unfold E0; omega

theorem d0_bounds (g : Nat) (hg : g < 8192) : 25 ≤ D0 g ∧ D0 g + 51200 ≤ 2 ^ 33 ∧ D0 (g + 1) = D0 g + 51200 := by
  unfold D0 replyW; omega

theorem block_steps (s : MachineState) (g : Nat) (r : BlockRegsP s g) :
    let P0 := runOpsC s prologueOps
    P0.pc = cpc (p1Index 0) ∧ Loop1 P0 (E0 g) 0 ∧ P0.getReg .x18 = wordAddress (E0 g) ∧
      (∀ reg, reg ≠ .x18 → reg ≠ .x5 → reg ≠ .x11 → reg ≠ .x13 → reg ≠ .x10 → P0.getReg reg = s.getReg reg) := by
  intro P0
  obtain ⟨h18, h5, h11, h13, h10, hpc, hk⟩ := prologue_facts s
  have eb := e0_bounds g r.block
  have pc0 : P0.pc = cpc (p1Index 0) := by
    rw [hpc, r.pc, cpc_next, cpc_next, cpc_next, cpc_next, cpc_next]; rfl
  refine ⟨pc0, ⟨pc0, ?_, by omega, by omega, h5, h11, h13⟩, ?_, hk⟩
  · rw [h10, r.source, address_down _ 32 3840 immm256 (by omega) (by norm_num)]; congr 1 <;> omega
  · rw [h18, r.source, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]

theorem block_post (s : MachineState) (g : Nat) (r : BlockRegsP s g) (t : MachineState)
    (reached : t ∈ support (blockTrace g s)) :
    t.pc = cpc 45156 ∧ t.getReg .x10 = wordAddress (E0 (g + 1)) ∧ t.getReg .x20 = wordAddress (D0 (g + 1) - 25) ∧
      t.getReg .x5 = 0 ∧ ∀ reg, reg ≠ .x5 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x12 → reg ≠ .x13 → reg ≠ .x18 → reg ≠ .x20 →
        t.getReg reg = s.getReg reg := by
  have eb := e0_bounds g r.block
  have db := d0_bounds g r.block
  obtain ⟨_, inv0, x18, keep0⟩ := block_steps s g r
  simp only [blockTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨t1, h1, t2, h2, t3, h3, rfl⟩ := reached
  obtain ⟨inv1, keep1⟩ := pass1_post (E0 g) 1024 0 _ (by omega) inv0 t1 h1
  obtain ⟨q5, q11, q10, qpc, qk⟩ := p2_setup_facts t1
  have t1x18 : t1.getReg .x18 = wordAddress (E0 g) := (keep1 .x18 (by decide) (by decide)).trans x18
  have inv2 : Loop2 (runOpsC t1 p2SetupOps) (E0 g) 0 := by
    refine ⟨?_, ?_, by omega, by omega, q5, q11⟩
    · rw [qpc, inv1.pc, cpc_next, cpc_next, cpc_next]; rfl
    · rw [q10, t1x18, address_down _ 34 3824 immm272 (by omega) (by norm_num)]; congr 1 <;> omega
  obtain ⟨inv2', keep2⟩ := pass2_post (E0 g) 1024 0 _ (by omega) inv2 t2 h2
  obtain ⟨u5, u11, u13, u10, u12, upc, uk⟩ := p3_setup_facts t2
  have t2x18 : t2.getReg .x18 = wordAddress (E0 g) :=
    (keep2 .x18 (by decide)).trans ((qk .x18 (by decide) (by decide) (by decide)).trans t1x18)
  have t2x20 : t2.getReg .x20 = wordAddress (D0 g - 25) :=
    (keep2 .x20 (by decide)).trans ((qk .x20 (by decide) (by decide) (by decide)).trans
      ((keep1 .x20 (by decide) (by decide)).trans ((keep0 .x20 (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r.reply)))
  have inv3 : Loop3 (runOpsC t2 p3SetupOps) (E0 g) (D0 g) 0 := by
    refine ⟨?_, ?_, ?_, by omega, by omega, by omega, by omega, u5, u11, u13⟩
    · rw [upc, inv2'.pc, cpc_next, cpc_next, cpc_next, cpc_next, cpc_next]; rfl
    · rw [u10, t2x18, address_down _ 32 3840 immm256 (by omega) (by norm_num)]; congr 1 <;> omega
    · rw [u12, t2x20, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]; congr 1 <;> omega
  obtain ⟨inv3', keep3⟩ := pass3_post (E0 g) (D0 g) 1024 0 _ (by omega) inv3 t3 h3
  obtain ⟨e20, e10, epc, ek⟩ := epilogue_facts t3
  refine ⟨?_, ?_, ?_, by rw [ek .x5 (by decide) (by decide)]; exact inv3'.selector, ?_⟩
  · rw [epc, inv3'.pc, cpc_next, cpc_next]; rfl
  · rw [e10, inv3'.source, imm256, address_up, eb.2.2]; congr 1 <;> omega
  · rw [e20, inv3'.target, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero, db.2.2]
    all_goals (congr 1 <;> omega)
  · intro reg h5 h10 h11 h12 h13 h18 h20
    rw [ek reg h20 h10, keep3 reg h10 h12, uk reg h5 h11 h13 h10 h12, keep2 reg h10, qk reg h5 h11 h10,
      keep1 reg h10 h12, keep0 reg h18 h5 h11 h13 h10]

theorem block_run (s : MachineState) (g : Nat) (r : BlockRegsP s g) (fuel : Nat) :
    execute packedWideCommitImage (26639 + fuel) s true =
      (do let t ← blockTrace g s
          let res ← execute packedWideCommitImage fuel t true
          return res.charge 133135 8192) := by
  have eb := e0_bounds g r.block
  have db := d0_bounds g r.block
  obtain ⟨pc0, inv0, x18, keep0⟩ := block_steps s g r
  rw [show 26639 + fuel = 5 + (16 * 1024 + (3 + (2 * 1024 + (5 + (8 * 1024 + (2 + fuel)))))) by omega]
  have runP : ∀ X, execute packedWideCommitImage (5 + X) s true =
      (do let r ← execute packedWideCommitImage X (runOpsC s prologueOps) true; return r.charge 5 0) := fun X =>
    alu_run_c s blockStart prologueOps X r.pc
      (fun j h u hu => by rw [← op_at_eq prologueOps j h]; exact fetch_prologue j h u hu)
      (by intro j h t; have hj : j < 4 := (by change j + 1 < 5 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 5 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 5 at h; interval_cases j <;> rfl)
  rw [runP, pass1_run (E0 g) 1024 0 _ (by omega) inv0]
  simp only [blockTrace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t1 h1
  obtain ⟨inv1, keep1⟩ := pass1_post (E0 g) 1024 0 _ (by omega) inv0 t1 h1
  obtain ⟨q5, q11, q10, qpc, qk⟩ := p2_setup_facts t1
  have t1x18 : t1.getReg .x18 = wordAddress (E0 g) := (keep1 .x18 (by decide) (by decide)).trans x18
  have inv2 : Loop2 (runOpsC t1 p2SetupOps) (E0 g) 0 := by
    refine ⟨?_, ?_, by omega, by omega, q5, q11⟩
    · rw [qpc, inv1.pc, cpc_next, cpc_next, cpc_next]; rfl
    · rw [q10, t1x18, address_down _ 34 3824 immm272 (by omega) (by norm_num)]; congr 1 <;> omega
  have runQ : ∀ X, execute packedWideCommitImage (3 + X) t1 true =
      (do let r ← execute packedWideCommitImage X (runOpsC t1 p2SetupOps) true; return r.charge 3 0) := fun X =>
    alu_run_c t1 p2Setup p2SetupOps X (by rw [inv1.pc]; rfl)
      (fun j h u hu => by rw [← op_at_eq p2SetupOps j h]; exact fetch_p2_setup j h u hu)
      (by intro j h t; have hj : j < 2 := (by change j + 1 < 3 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 3 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 3 at h; interval_cases j <;> rfl)
  rw [runQ, pass2_run (E0 g) 1024 0 _ (by omega) inv2]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t2 h2
  obtain ⟨inv2', keep2⟩ := pass2_post (E0 g) 1024 0 _ (by omega) inv2 t2 h2
  obtain ⟨u5, u11, u13, u10, u12, upc, uk⟩ := p3_setup_facts t2
  have t2x18 : t2.getReg .x18 = wordAddress (E0 g) :=
    (keep2 .x18 (by decide)).trans ((qk .x18 (by decide) (by decide) (by decide)).trans t1x18)
  have t2x20 : t2.getReg .x20 = wordAddress (D0 g - 25) :=
    (keep2 .x20 (by decide)).trans ((qk .x20 (by decide) (by decide) (by decide)).trans
      ((keep1 .x20 (by decide) (by decide)).trans ((keep0 .x20 (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r.reply)))
  have inv3 : Loop3 (runOpsC t2 p3SetupOps) (E0 g) (D0 g) 0 := by
    refine ⟨?_, ?_, ?_, by omega, by omega, by omega, by omega, u5, u11, u13⟩
    · rw [upc, inv2'.pc, cpc_next, cpc_next, cpc_next, cpc_next, cpc_next]; rfl
    · rw [u10, t2x18, address_down _ 32 3840 immm256 (by omega) (by norm_num)]; congr 1 <;> omega
    · rw [u12, t2x20, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]; congr 1 <;> omega
  have runR : ∀ X, execute packedWideCommitImage (5 + X) t2 true =
      (do let r ← execute packedWideCommitImage X (runOpsC t2 p3SetupOps) true; return r.charge 5 0) := fun X =>
    alu_run_c t2 p3Setup p3SetupOps X (by rw [inv2'.pc]; rfl)
      (fun j h u hu => by rw [← op_at_eq p3SetupOps j h]; exact fetch_p3_setup j h u hu)
      (by intro j h t; have hj : j < 4 := (by change j + 1 < 5 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 5 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 5 at h; interval_cases j <;> rfl)
  rw [runR, pass3_run (E0 g) (D0 g) 1024 0 _ (by omega) inv3]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t3 h3
  obtain ⟨inv3', _⟩ := pass3_post (E0 g) (D0 g) 1024 0 _ (by omega) inv3 t3 h3
  have runE : ∀ X, execute packedWideCommitImage (2 + X) t3 true =
      (do let r ← execute packedWideCommitImage X (runOpsC t3 epilogueOps) true; return r.charge 2 0) := fun X =>
    alu_run_c t3 epilogue epilogueOps X (by rw [inv3'.pc]; rfl)
      (fun j h u hu => by rw [← op_at_eq epilogueOps j h]; exact fetch_epilogue j h u hu)
      (by intro j h t; have hj : j < 1 := (by change j + 1 < 2 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 2 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 2 at h; interval_cases j <;> rfl)
  rw [runE]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd, Nat.reduceMul]

end TwoPermutationPrototype.RV64.C3P
