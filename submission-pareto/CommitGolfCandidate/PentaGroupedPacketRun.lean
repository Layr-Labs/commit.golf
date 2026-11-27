import CommitGolfCandidate.PentaGroupedPacket

/-! Straight-line validity (`walk`) for every loop-body packet (`i < 16777215`) and the
trailing packet (`i = 16777215`). -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Quad.Commit
set_option maxRecDepth 24000
set_option maxHeartbeats 3000000

def walk (post : MachineState → Prop) : List Action → MachineState → Prop
  | [], s => post s
  | a :: rest, s => a.valid s ∧
      match a with
      | .offset rd _ _ target | .add rd _ _ target => walk post rest (putReg s rd (wordAddress target))
      | .load rd _ _ addr => walk post rest (putReg s rd (memoryView s addr))
      | .store _ value _ addr => walk post rest (putWord s addr (s.getReg value))
      | .perm _ dst => ∀ y : BitVec 1600, walk post rest (writeBits s (wordAddress dst) y)

theorem walk_post (post : MachineState → Prop) (ops : List Action) (s : MachineState)
    (h : walk post ops s) : validOps ops s ∧ ∀ t ∈ support (runOps ops s), post t := by
  induction ops generalizing s with
  | nil =>
    refine ⟨trivial, ?_⟩
    simpa only [runOps, support_pure, Set.mem_singleton_iff, forall_eq] using (show post s from h)
  | cons a rest ih =>
    have restOk : ∀ t ∈ support (a.run s), walk post rest t := by
      cases a <;> simp only [Action.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, forall_eq]
      all_goals first | exact h.2 | intro t hit; obtain ⟨y, _, rfl⟩ := hit; exact h.2 y
    exact ⟨⟨h.1, fun t hit => (ih t (restOk t hit)).1⟩, fun t hit => by
      rw [runOps, mem_support_bind_iff] at hit
      obtain ⟨st, prior, tail⟩ := hit
      exact (ih st (restOk st prior)).2 t tail⟩

theorem ops_pc (ops : List Action) (s t : MachineState) (hit : t ∈ support (runOps ops s)) :
    t.pc = s.pc + BitVec.ofNat 64 (4 * ops.length) := by
  induction ops generalizing s with
  | nil => simp only [runOps, support_pure, Set.mem_singleton_iff] at hit; subst t; simp
  | cons a rest ih =>
    rw [runOps, mem_support_bind_iff] at hit
    obtain ⟨st, one, tail⟩ := hit
    rw [ih st tail, action_pc a s st one, List.length_cons, Nat.mul_add]
    rw [BitVec.ofNat_add, show BitVec.ofNat 64 (4 * 1) = 4#64 from rfl,
      BitVec.add_comm (BitVec.ofNat 64 (4 * rest.length)), BitVec.add_assoc]; rfl

theorem buffer_next (i : Nat) (more : rank (i + 1) ≠ 0) : groupBuffer (i + 1) = groupBuffer i := by
  have hEdge : i % 4095 ≠ 4094 := by
    intro h; apply more
    unfold rank; rw [show (i + 1) % 4095 = 0 by omega]
  have rel : (i + 1) % 4095 = i % 4095 + 1 := by omega
  unfold rank at more
  rw [rel] at more
  have rk : (i % 4095 + 1) % 11 = i % 4095 % 11 + 1 := by omega
  unfold groupBuffer rank; rw [rel, rk]; simp

def finish (s t : MachineState) (i : Nat) : Prop :=
  t.getReg .x10 = wordAddress (msgWord (i + 1)) ∧ t.getReg .x20 = wordAddress (cursor (i + 1)) ∧
  t.getReg .x24 = wordAddress keyWord ∧
  t.getReg .x5 = 0 ∧ t.getReg .x11 = 200 ∧ t.getReg .x13 = 1 ∧
  t.getReg .x8 = s.getReg .x8 ∧ t.getReg .x9 = s.getReg .x9 ∧ t.getReg .x28 = s.getReg .x28

def trailingFinish (s t : MachineState) : Prop :=
  t.getReg .x12 = wordAddress (leafWord 16777215) ∧
  t.getReg .x5 = 0 ∧ t.getReg .x11 = 200 ∧ t.getReg .x13 = 1 ∧
  t.getReg .x8 = s.getReg .x8 ∧ t.getReg .x9 = s.getReg .x9

private theorem word_getReg (s : MachineState) (addr : Nat) (v : Word) (reg : Reg) :
    (putWord s addr v).getReg reg = s.getReg reg := by cases reg <;> rfl

private theorem offset_getReg (s : MachineState) (rd : Reg) (value : Word) (reg : Reg) :
    (putReg s rd value).getReg reg = if rd = reg ∧ reg ≠ .x0 then value else s.getReg reg := by
  simp only [putReg, MachineState.getReg_setPC]
  cases rd <;> cases reg <;> rfl

attribute [local irreducible] wordAddress msgWord cursor groupBuffer sourceWord keyWord leafWord writeBits

theorem packet_walk (s : MachineState) (i : Nat) (limit : i < 16777215) (r : PacketRegs s i) :
    walk (fun t => finish s t i) (plan i) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := packet_addrs i
  have h0 := heap_address i
  have boundM : msgWord i + 32 ≤ 2^33 := by unfold msgWord; omega
  have boundQ : leafWord i + 25 ≤ 2^33 := by unfold leafWord groupWord; omega
  have boundSource : sourceWord i + 2 ≤ 2^33 := by unfold sourceWord groupBuffer msgWord rank; omega
  have ctrRoom : keyWord + 25 ≤ 2^33 := by unfold keyWord saltWord; decide
  have z : signExtend12 0#12 = 0#64 := rfl
  change wordAddress (msgWord i) + signExtend12 4064#12 = _ at a0
  change wordAddress (msgWord i) + signExtend12 3976#12 = _ at a1
  change wordAddress (msgWord i) + signExtend12 56#12 = _ at a2
  change wordAddress (msgWord i - 15) + signExtend12 176#12 = _ at a3
  change wordAddress (msgWord i + 7) + signExtend12 8#12 = _ at a4
  change wordAddress (msgWord i + 7) + signExtend12 16#12 = _ at a5
  change wordAddress (msgWord i + 7) + signExtend12 200#12 = _ at a6
  have directLoads (j : Fin 4) :
      wordAddress (msgWord i - 15) + signExtend12 (BitVec.ofNat 12 (128 + 8 * j.val)) =
        wordAddress (msgWord i - 15 + (16 + j.val)) := by
    have u := wordAddress_add (msgWord i - 15) (16 + j.val)
    have v : signExtend12 (BitVec.ofNat 12 (128 + 8 * j.val)) = wordAddress (16 + j.val) := by
      unfold wordAddress; fin_cases j <;> rfl
    rw [v]; exact u.symm
  have l0 := directLoads 0; have l1 := directLoads 1; have l2 := directLoads 2; have l3 := directLoads 3
  change wordAddress (msgWord i - 15) + signExtend12 128#12 = wordAddress (msgWord i - 15 + 16) at l0
  change wordAddress (msgWord i - 15) + signExtend12 136#12 = wordAddress (msgWord i - 15 + 17) at l1
  change wordAddress (msgWord i - 15) + signExtend12 144#12 = wordAddress (msgWord i - 15 + 18) at l2
  change wordAddress (msgWord i - 15) + signExtend12 152#12 = wordAddress (msgWord i - 15 + 19) at l3
  have lastRank : rank 4092 = 0 := by decide
  have lastHeap (last : i % 4095 = 4092) :
      wordAddress (cursor i) + signExtend12 (slotImmediate 4092) = wordAddress (leafWord i) := by
    simpa only [last] using h0
  have rbc (shift : rebase (i % 4095)) :
      wordAddress (leafWord i) + signExtend12 1776#12 = wordAddress (cursor (i + 1)) := rebase_cursor i shift
  by_cases direct : rank i = 0
  · by_cases short : i % 4095 = 4092 <;> by_cases shift : rebase (i % 4095)
    all_goals try (exfalso; exact (show ¬rebase 4092 by decide) (short ▸ shift))
    all_goals simp [plan, within_rank, within_period, direct, short, (show ¬rebase 4092 by decide), lastRank,
      lastHeap, shift, walk, finish, Action.valid, offset_getReg, word_getReg, writeBits_register,
      r.msg, r.heap, r.counter, r.selector, r.size, r.primitive, h0, no_rebase_cursor]
    all_goals simp only [a0, a1, a2, a3, a4, a5, a6, l0, l1, l2, l3, z, true_and, and_true]
    all_goals try rw [rbc shift]
    all_goals try rw [no_rebase_cursor i shift]
    all_goals repeat' apply And.intro
    all_goals first | omega | rfl
  · by_cases near : rank i ≤ 8
    · have src0 : wordAddress (msgWord i - 4) + signExtend12 (sourceImm (i % 4095)) = wordAddress (sourceWord i) := by
        simpa using src_address i 0 (by omega) near
      have src1 : wordAddress (msgWord i - 4) + signExtend12 (sourceImm (i % 4095) + 8#12) = wordAddress (sourceWord i + 1) :=
        src_address i 1 (by omega) near
      by_cases shift : rebase (i % 4095)
      all_goals simp [plan, within_rank, direct, near, shift, walk, finish, Action.valid, offset_getReg, word_getReg,
        writeBits_register, r.msg, r.heap, r.counter, r.selector, r.size, r.primitive, h0]
      all_goals simp only [a0, a1, a2, a3, a4, a5, a6, src0, src1, z, true_and, and_true]
      all_goals try rw [rbc shift]
      all_goals try rw [no_rebase_cursor i shift]
      all_goals repeat' apply And.intro
      all_goals first | omega | rfl
    · by_cases ninth : rank i = 9 <;> by_cases shift : rebase (i % 4095)
      all_goals simp [plan, within_rank, direct, near, ninth, shift, walk, finish, Action.valid, offset_getReg, word_getReg,
        writeBits_register, r.msg, r.heap, r.counter, r.selector, r.size, r.primitive, h0]
      all_goals simp only [a0, a1, a2, a3, a4, a5, a6, z, true_and, and_true]
      all_goals try rw [rbc shift]
      all_goals try rw [no_rebase_cursor i shift]
      all_goals repeat' apply And.intro
      all_goals first | omega | rfl

theorem trailing_walk (s : MachineState) (r : PacketRegs s 16777215) :
    walk (fun t => trailingFinish s t) trailingPlan s := by
  obtain ⟨a0, a1, _, a3, _, _, a6⟩ := packet_addrs 16777215
  have h0 : wordAddress (cursor 16777215) + signExtend12 (slotImmediate 0) = wordAddress (leafWord 16777215) := by
    simpa [show (16777215 : Nat) % 4095 = 0 by decide] using heap_address 16777215
  have boundM : msgWord 16777215 + 32 ≤ 2^33 := by unfold msgWord; decide
  have boundQ : leafWord 16777215 + 25 ≤ 2^33 := by unfold leafWord groupWord; decide
  have ctrRoom : keyWord + 25 ≤ 2^33 := by unfold keyWord saltWord; decide
  have z : signExtend12 0#12 = 0#64 := rfl
  change wordAddress (msgWord 16777215) + signExtend12 4064#12 = _ at a0
  change wordAddress (msgWord 16777215) + signExtend12 3976#12 = _ at a1
  change wordAddress (msgWord 16777215 - 15) + signExtend12 176#12 = _ at a3
  change wordAddress (msgWord 16777215 + 7) + signExtend12 200#12 = _ at a6
  simp [trailingPlan, walk, trailingFinish, Action.valid, offset_getReg, word_getReg, writeBits_register,
    r.msg, r.heap, r.counter, r.selector, r.size, r.primitive, h0, a0, a1, a3, a6, z]
  repeat' apply And.intro
  all_goals first | omega | rfl

end TwoPermutationPrototype.PentaGrouped
