import CommitGolfCandidate.PentaGroupedPacketRun
import CommitGolfCandidate.TwoPermutationCounted

/-! Full 16,777,215-leaf loop scan (`4097 * 4095`) plus the trailing leaf (`i = 16777215`),
reaching word 45,201 (`leafZeroWords`) with exact step, cycle, and oracle-call counts. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Quad.Commit
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

abbrev N_loop : Nat := 16777215

def startPC (i : Nat) : Word := if i = N_loop then wordPC 45190 else wordPC (firstWord (i % 4095))
def edgeCost (i : Nat) : Nat := if i % 4095 = 4094 then if i + 1 = N_loop then 1 else 2 else 0
def S (i : Nat) : Nat := 11 * i + cacheCredit i + (91 * (i / 4095) + rb (i % 4095)) + 2 * (i / 4095) - (if i = N_loop then 1 else 0)
def Q (i : Nat) : Nat := 2 * i + heads i
def C (i : Nat) : Nat := S i + 29 * Q i

theorem calls_plan (i : Nat) : opCalls (plan i) = 2 + (if rank i = 0 then 1 else 0) := by
  unfold plan; dsimp only; rw [within_rank, within_period]; split_ifs <;> rfl

theorem length_plan (i : Nat) : (plan i).length = bodyLen i + (if rebase (i % 4095) then 1 else 0) := by
  have h := congrArg List.length (plan_words i)
  rw [List.length_map, packet_length] at h
  simpa [bodyLen, within_rank, within_period] using h

theorem cumul (i : Nat) (hi : i < N_loop) :
    S (i + 1) = S i + (plan i).length + edgeCost i ∧ Q (i + 1) = Q i + opCalls (plan i) := by
  have rs := rebases_succ i
  rw [calls_plan, length_plan]; unfold S Q edgeCost
  rw [heads_succ, if_neg (Nat.ne_of_lt hi)]
  have hc := credit_succ i
  change i < 16777215 at hi
  dsimp only [N_loop]
  split_ifs at rs ⊢ <;> constructor <;> omega

def stepTrace (s : MachineState) (i : Nat) : OracleComp World MachineState := do
  let t ← runOps (plan i) s
  return t.setPC (startPC (i + 1))

structure Live (s : MachineState) (i : Nat) extends PacketRegs s i where
  pc : s.pc = startPC i
  stop : s.getReg .x28 = wordAddress (msgWord N_loop)
  out : s.getReg .x8 = 4294971392
  heapBase : s.getReg .x9 = 4294971424

theorem step_live (s : MachineState) (i : Nat) (hi : i < N_loop) (r : Live s i)
    (u : MachineState) (reach : u ∈ support (stepTrace s i)) : Live u (i + 1) := by
  simp only [stepTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reach
  obtain ⟨t, hit, rfl⟩ := reach
  have post := (walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)).2 t hit
  obtain ⟨src, hp, ct, sel, sz, pr, out, hbase, stop⟩ := post
  exact ⟨⟨src, hp, ct, sel, sz, pr⟩, rfl, stop.trans r.stop, out.trans r.out, hbase.trans r.heapBase⟩

theorem edge_run (s : MachineState) (i fuel : Nat) (hi : i < N_loop)
    (start : s.pc = wordPC (firstWord (i % 4095) + (plan i).length))
    (msg : s.getReg .x10 = wordAddress (msgWord (i + 1)))
    (stop : s.getReg .x28 = wordAddress (msgWord N_loop)) :
    execute image (edgeCost i + fuel) s true = (do
      let z ← execute image fuel (s.setPC (startPC (i + 1))) true
      return z.charge (edgeCost i) 0) := by
  have len : (plan i).length = (packet (i % 4095)).length := by
    have h := congrArg List.length (plan_words i); simpa using h
  rw [len, ← packet_next] at start
  by_cases edge : i % 4095 = 4094
  · have pc : s.pc = wordPC 45153 := by rw [start, edge]; exact congrArg wordPC first_word_4095
    have fetchB : fetch image s = some (.base (.BEQ .x10 .x28 148)) :=
      fetch_decoded s 45153 (by decide) pc _ (by decide +kernel)
    have same : s.getReg .x10 = s.getReg .x28 ↔ i + 1 = N_loop := by
      rw [msg, stop]
      constructor
      · intro h
        have w := wordAddress_injective_of_bound (by unfold msgWord; dsimp [N_loop] at hi; omega)
          (by unfold msgWord; decide) h
        unfold msgWord at w; dsimp [N_loop] at w ⊢; omega
      · intro h; rw [h]
    by_cases last : i + 1 = N_loop
    · have op : ordinaryStep s (.base (.BEQ .x10 .x28 148)) = some (s.setPC (wordPC 45190)) := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, same.mpr last, wordPC, signExtend13]
      rw [edgeCost, if_pos edge, if_pos last, startPC, if_pos last, Nat.add_comm 1 fuel,
        execute_ordinary_step _ _ _ _ _ _ fetchB op]; rfl
    · let mid := s.setPC (wordPC 45154)
      have next : (i + 1) % 4095 = 0 := by omega
      have op : ordinaryStep s (.base (.BEQ .x10 .x28 148)) = some mid := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, mid, mt same.mp last]; rfl
      have fj : fetch image mid = some (.base (.JAL .x0 1916604)) :=
        fetch_decoded mid 45154 (by decide) rfl _ (by decide +kernel)
      have jump : ordinaryStep mid (.base (.JAL .x0 1916604)) = some (s.setPC (wordPC 17)) := by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, mid, MachineState.setPC, MachineState.setReg]; rfl
      rw [edgeCost, if_pos edge, if_neg last, startPC, if_neg last, next, first_word_0,
        show 2 + fuel = (fuel + 1) + 1 by omega, execute_ordinary_step _ _ _ _ _ _ fetchB op,
        execute_ordinary_step _ _ _ _ _ _ fj jump]
      simp [Execution.charge, instructionCycles, ← Nat.add_assoc]
  · have more : i + 1 ≠ N_loop := by dsimp [N_loop] at *; omega
    have next : (i + 1) % 4095 = i % 4095 + 1 := by omega
    rw [edgeCost, if_neg edge, Nat.zero_add, startPC, if_neg more, next, ← start]
    cases s; simp [MachineState.setPC, Execution.charge]

theorem packet_execute (s : MachineState) (i fuel : Nat) (hi : i < N_loop) (r : Live s i) :
    execute image ((plan i).length + edgeCost i + fuel) s true =
      (do let t ← stepTrace s i; let z ← execute image fuel t true
          return z.charge ((plan i).length + edgeCost i + 29 * opCalls (plan i)) (opCalls (plan i))) := by
  have walkOK := walk_post _ _ _ (packet_walk s i hi r.toPacketRegs)
  have pc : s.pc = wordPC (firstWord (i % 4095)) := by simpa [startPC, Nat.ne_of_lt hi] using r.pc
  rw [Nat.add_assoc, run_ops (plan i) _ _ s true pc (plan_fetch i) walkOK.1]
  simp only [stepTrace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support; intro t hit
  have p := walkOK.2 t hit
  have pct : t.pc = wordPC (firstWord (i % 4095) + (plan i).length) := by
    rw [ops_pc _ s t hit, pc]; unfold wordPC; rw [← BitVec.ofNat_add]; congr 1 <;> omega
  rw [edge_run t i fuel hi pct p.1 (p.2.2.2.2.2.2.2.2.trans r.stop)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro z; apply congrArg pure
  cases z; simp [Execution.charge, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def scan : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n + 1, i, s => do let t ← stepTrace s i; scan n (i + 1) t

theorem scan_post (n i : Nat) (s t : MachineState) (bound : i + n ≤ N_loop) (r : Live s i)
    (reach : t ∈ support (scan n i s)) : Live t (i + n) := by
  induction n generalizing i s with
  | zero => simp only [scan, support_pure, Set.mem_singleton_iff] at reach; subst t; exact r
  | succ n ih =>
    rw [scan, mem_support_bind_iff] at reach
    obtain ⟨u, h, rest⟩ := reach
    simpa only [show i + (n + 1) = (i + 1) + n by omega] using
      ih (i + 1) u (by omega) (step_live s i (by omega) r u h) rest

theorem monotone_counts (i n : Nat) (bound : i + n ≤ N_loop) :
    S i ≤ S (i + n) ∧ Q i ≤ Q (i + n) ∧ C i ≤ C (i + n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h := ih (by omega)
    have g := cumul (i + k) (by omega)
    rw [show i + (k + 1) = i + k + 1 by omega]
    unfold C at *; omega

attribute [local irreducible] stepTrace S Q C edgeCost opCalls plan

theorem run_scan (n i : Nat) (s : MachineState) (bound : i + n ≤ N_loop) (r : Live s i) (fuel : Nat) :
    execute image (S (i + n) - S i + fuel) s true = (do
      let t ← scan n i s; let z ← execute image fuel t true
      return z.charge (C (i + n) - C i) (Q (i + n) - Q i)) := by
  induction n generalizing i s with
  | zero => simp [scan, Execution.charge]
  | succ n ih =>
    have h := cumul i (by omega)
    have m := monotone_counts (i + 1) n (by omega)
    have next : i + (n + 1) = (i + 1) + n := by omega
    have price : C (i + 1) = C i + ((plan i).length + edgeCost i + 29 * opCalls (plan i)) := by
      unfold C; rw [h.1, h.2]; omega
    rw [next, show S ((i + 1) + n) - S i + fuel = (plan i).length + edgeCost i + (S ((i + 1) + n) - S (i + 1) + fuel) by omega,
      packet_execute s i _ (by omega) r]
    simp only [scan, bind_assoc]
    apply bind_congr_of_forall_mem_support; intro u reach
    rw [ih (i + 1) u (by omega) (step_live s i (by omega) r u reach)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro last; apply bind_congr; intro out; apply congrArg pure
    cases out; simp only [Execution.charge, Execution.mk.injEq, true_and]; constructor <;> omega

attribute [local semireducible] S Q C opCalls

theorem scan_counts : S N_loop = 184930385 ∧ Q N_loop = 35082611 ∧ C N_loop = 1202326104 ∧
    S 0 = 0 ∧ Q 0 = 0 ∧ C 0 = 0 := by
  decide

theorem trailing_execute (s : MachineState) (r : Live s N_loop) (fuel : Nat) :
    execute image (11 + fuel) s true = (do
      let t ← runOps trailingPlan s
      let z ← execute image fuel t true
      return z.charge 98 3) := by
  have walkOK := walk_post _ _ _ (trailing_walk s r.toPacketRegs)
  have pc : s.pc = wordPC 45190 := by simpa [startPC] using r.pc
  have h := run_ops trailingPlan 45190 fuel s true pc trailing_plan_fetch walkOK.1
  have len : trailingPlan.length = 11 := rfl
  have calls : opCalls trailingPlan = 3 := rfl
  simpa only [len, calls] using h

theorem trailing_post (s t : MachineState) (r : Live s N_loop) (hit : t ∈ support (runOps trailingPlan s)) :
    t.pc = wordPC 45201 ∧ t.getReg .x12 = wordAddress (leafWord 16777215) ∧
    t.getReg .x5 = 0 ∧ t.getReg .x11 = 200 ∧ t.getReg .x13 = 1 ∧
    t.getReg .x8 = 4294971392 ∧ t.getReg .x9 = 4294971424 := by
  have walkOK := walk_post _ _ _ (trailing_walk s r.toPacketRegs)
  obtain ⟨x12, x5, x11, x13, x8, x9⟩ := walkOK.2 t hit
  have pc : s.pc = wordPC 45190 := by simpa [startPC] using r.pc
  have pct : t.pc = wordPC 45201 := by
    rw [ops_pc _ s t hit, pc, show trailingPlan.length = 11 from rfl]; rfl
  exact ⟨pct, x12, x5, x11, x13, x8.trans r.out, x9.trans r.heapBase⟩

end TwoPermutationPrototype.PentaGrouped
