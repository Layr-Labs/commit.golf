import CommitGolfCandidate.C3PCommitPass1
import CommitGolfCandidate.TwoPermutationSyscall

/-! # Passes 2 and 3 of the paired commit

Pass 2, per pair (even leaf at message word `E`, entered with `a0 = E - 34`): `addi a0,a0,512 ; ecall`
with `t0 = 2, a1 = 32`: one RANDOM(32) at words `E + 30 .. E + 33` (even salt, odd salt). 2 steps,
6 cycles, no calls.

Pass 3, per pair (entered with `a0 = E - 32`, `a2 = Rw + 25 e - 25` for the even leaf `e`):
`addi a0,a0,312 ; sd a0,168(a0) ; addi a2,a2,200 ; ecall` (the even window at `E + 7`, its tag at
`E + 28`, the reply at `Rw + 25 e`), `addi a0,a0,200 ; sd a0,16(a0) ; addi a2,a2,200 ; ecall` (the odd
window at `O = E + 32`, its tag at `O + 2`, the reply at `Rw + 25 (e + 1)`). 8 steps, 66 cycles, 2 calls. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (address_up address_down addi_mem addi_pc word_access)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000
attribute [local irreducible] execute packedWideCommitImage

/-! ### The RANDOM step -/

theorem execute_random_c (st : MachineState) (dst fuel : Nat) (bound : dst + 4 ≤ 2 ^ 33)
    (sel : st.getReg .x5 = 2) (target : st.getReg .x10 = wordAddress dst) (size : st.getReg .x11 = 32)
    (fetched : fetch packedWideCommitImage st = some (.base .ECALL)) :
    execute packedWideCommitImage (fuel + 1) st true =
      (do let w ← liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          let r ← execute packedWideCommitImage fuel (writeBits st (wordAddress dst) w) true
          return r.charge 5 0) := by
  have addr := word_address_value (word := dst) (by omega)
  have valid : randomArgumentsValid st = true := by
    rw [randomArgumentsValid, target, size]
    simp only [addr, decide_eq_true_eq, Bool.and_eq_true]
    refine ⟨by omega, ?_⟩
    simp [rangeValid, addr, MEMORY_BYTES]; omega
  have n32 : (st.getReg .x11).toNat = 32 := by rw [size]; rfl
  have resize (bits : Nat) (eq : bits = 256) :
      (do let w ← (liftM ($ᵗ BitVec bits : ProbComp (BitVec bits)) : OracleComp World _)
          let r ← execute packedWideCommitImage fuel (writeBits st (wordAddress dst) w) true
          return r.charge 5 0) =
      (do let w ← liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          let r ← execute packedWideCommitImage fuel (writeBits st (wordAddress dst) w) true
          return r.charge 5 0) := by subst bits; rfl
  simp only [execute, fetched, sel, show (2 : Word) ≠ 0 by decide, show (2 : Word) ≠ 1 by decide, ↓reduceIte,
    valid, decide_true, Bool.and_self, target, n32]
  exact resize _ (by rw [n32])

/-! ### Pass 2, one pair -/

def p2Draw (s : MachineState) : MachineState := seg1 s 512

def p2After (s : MachineState) (E : Nat) (w : BitVec 256) : MachineState := writeBits (p2Draw s) (wordAddress (E + 30)) w

structure P2PairReady (s : MachineState) (p E : Nat) : Prop where
  pc : s.pc = cpc (p2Index p)
  source : s.getReg .x10 = wordAddress (E - 34)
  low : 34 ≤ E
  bound : E + 64 ≤ 2 ^ 33
  selector : s.getReg .x5 = 2
  size : s.getReg .x11 = 32
  pair : p < 1024

private theorem imm512 : signExtend12 (512 : BitVec 12) = BitVec.ofNat 64 (8 * 64) := by decide

theorem p2_after_facts (s : MachineState) (p E : Nat) (r : P2PairReady s p E) (w : BitVec 256) :
    (p2Draw s).getReg .x10 = wordAddress (E + 30) ∧ (p2Draw s).pc = cpc (p2Index p + 1) ∧
    (p2After s E w).getReg .x10 = wordAddress (E + 30) ∧ (p2After s E w).pc = cpc (p2Index (p + 1)) ∧
    (∀ g, g ≠ .x10 → (p2After s E w).getReg g = s.getReg g ∧ (p2Draw s).getReg g = s.getReg g) := by
  have low := r.low
  obtain ⟨x10, _, pc, keep⟩ := seg1_facts s 512
  have d10 : (p2Draw s).getReg .x10 = wordAddress (E + 30) := by
    rw [p2Draw, x10, r.source, imm512, address_up]; congr 1 <;> omega
  have dpc : (p2Draw s).pc = cpc (p2Index p + 1) := by rw [p2Draw, pc, r.pc, cpc_next]
  have wr (t : MachineState) (d : Word) (a : BitVec 256) (g : Reg) : (writeBits t d a).getReg g = t.getReg g :=
    CommitGolfCandidate.writeBits_register _ _ _ _
  refine ⟨d10, dpc, by rw [p2After, wr, d10], ?_, fun g h => ⟨by rw [p2After, wr, p2Draw, keep g h], by
    rw [p2Draw, keep g h]⟩⟩
  rw [p2After, show ∀ (t : MachineState) (d : Word) (a : BitVec 256), (writeBits t d a).pc = t.pc + 4 from
    fun t d a => by simp only [writeBits, MachineState.setPC], dpc, cpc_next]
  congr 1 <;> (unfold p2Index; omega)

theorem execute_p2_pair (s : MachineState) (p E : Nat) (r : P2PairReady s p E) (fuel : Nat) :
    execute packedWideCommitImage (2 + fuel) s true =
      (do let w ← liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          let res ← execute packedWideCommitImage fuel (p2After s E w) true
          return res.charge 6 0) := by
  have hp := r.pair
  have bd := r.bound
  obtain ⟨d10, dpc, _, _, keep⟩ := p2_after_facts s p E r 0
  rw [show 2 + fuel = 1 + (fuel + 1) by omega,
    run_seg1 s (p2Index p) 512 _ r.pc (fun u h => fetch_p2 p hp 0 (by decide) u (by simpa using h)),
    show seg1 s 512 = p2Draw s from rfl,
    execute_random_c (p2Draw s) (E + 30) fuel (by omega) ((keep .x5 (by decide)).2.trans r.selector) d10
      ((keep .x11 (by decide)).2.trans r.size) (fetch_p2 p hp 1 (by decide) _ dpc)]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]
  rfl

/-! ### Pass 3, one pair -/

def p3a (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (seg1 s 312) (.SD .x10 .x10 168)) (.ADDI .x12 .x12 200)

def p3w1 (s : MachineState) (D : Nat) (y1 : Sampling.Block) : MachineState :=
  writeBits (p3a s) (wordAddress D) y1

def p3b (s : MachineState) (D : Nat) (y1 : Sampling.Block) : MachineState :=
  execInstrBr (execInstrBr (seg1 (p3w1 s D y1) 200) (.SD .x10 .x10 16)) (.ADDI .x12 .x12 200)

def p3w2 (s : MachineState) (D : Nat) (y1 y2 : Sampling.Block) : MachineState :=
  writeBits (p3b s D y1) (wordAddress (D + 25)) y2

def p3PairTrace (s : MachineState) (E D : Nat) : OracleComp World MachineState := do
  let y1 ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (p3a s)) (E + 7))))))
  let y2 ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (p3b s D y1)) (E + 32))))))
  return p3w2 s D y1 y2

structure P3PairReady (s : MachineState) (p E D : Nat) : Prop where
  pc : s.pc = cpc (p3Index p)
  source : s.getReg .x10 = wordAddress (E - 32)
  target : s.getReg .x12 = wordAddress (D - 25)
  low : 32 ≤ E
  lowD : 25 ≤ D
  bound : E + 64 ≤ 2 ^ 33
  boundD : D + 50 ≤ 2 ^ 33
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1
  pair : p < 1024

private theorem imm312 : signExtend12 (312 : BitVec 12) = BitVec.ofNat 64 (8 * 39) := by decide
private theorem imm200 : signExtend12 (200 : BitVec 12) = BitVec.ofNat 64 (8 * 25) := by decide
private theorem imm168 : signExtend12 (168 : BitVec 12) = BitVec.ofNat 64 (8 * 21) := by decide
private theorem imm16 : signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 (8 * 2) := by decide

/-- One tag store `sd a0,o(a0)` followed by `addi a2,a2,200`, on an abstract state. -/
theorem tag_facts (t : MachineState) (o : BitVec 12) :
    let u := execInstrBr (execInstrBr t (.SD .x10 .x10 o)) (.ADDI .x12 .x12 200)
    u.getReg .x10 = t.getReg .x10 ∧ u.getReg .x12 = t.getReg .x12 + signExtend12 200 ∧
    u.pc = t.pc + 4 + 4 ∧ (∀ g, g ≠ .x12 → u.getReg g = t.getReg g) ∧
    u.mem = (t.setMem (t.getReg .x10 + signExtend12 o) (t.getReg .x10)).mem := by
  intro u
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · simp only [u, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC, Opening.getReg_setMem,
      reduceCtorEq, false_and, ↓reduceIte]
  · simp only [u, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC, Opening.getReg_setMem,
      reduceCtorEq, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
  · intro g h
    simp [u, execInstrBr, Opening.getReg_setReg, Opening.getReg_setMem, Ne.symm h]
  · rfl

/-- `addi a0,a0,i ; sd a0,o(a0) ; addi a2,a2,200` at words `k .. k+2`. -/
theorem run_tag3 (t : MachineState) (k : Nat) (i o : BitVec 12) (X : Nat) (pc : t.pc = cpc k)
    (f0 : ∀ u : MachineState, u.pc = cpc k → fetch packedWideCommitImage u = some (.base (.ADDI .x10 .x10 i)))
    (f1 : ∀ u : MachineState, u.pc = cpc (k + 1) → fetch packedWideCommitImage u = some (.base (.SD .x10 .x10 o)))
    (f2 : ∀ u : MachineState, u.pc = cpc (k + 2) →
      fetch packedWideCommitImage u = some (.base (.ADDI .x12 .x12 200)))
    (valid : accessValid ((seg1 t i).getReg .x10 + signExtend12 o) 8 = true) :
    execute packedWideCommitImage (3 + X) t true =
      (do let r ← execute packedWideCommitImage X
            (execInstrBr (execInstrBr (seg1 t i) (.SD .x10 .x10 o)) (.ADDI .x12 .x12 200)) true
          return r.charge 3 0) := by
  let a := seg1 t i
  let b := execInstrBr a (.SD .x10 .x10 o)
  have apc : a.pc = cpc (k + 1) := by rw [show a.pc = t.pc + 4 from rfl, pc, cpc_next]
  have bpc : b.pc = cpc (k + 2) := by rw [show b.pc = a.pc + 4 from rfl, apc, cpc_next]
  have sdStep : ordinaryStep a (.base (.SD .x10 .x10 o)) = some b := by
    change (if memoryArgumentsValid a (.SD .x10 .x10 o) = true then some (execInstrBr a (.SD .x10 .x10 o)) else none) = _
    rw [show memoryArgumentsValid a (.SD .x10 .x10 o) = accessValid (a.getReg .x10 + signExtend12 o) 8 from rfl, valid]
    rfl
  rw [show 3 + X = 1 + (1 + (1 + X)) by omega, run_seg1 t k i _ pc f0,
    ordinary_c a b _ _ (f1 a apc) sdStep rfl, ordinary_c b _ _ _ (f2 b bpc) rfl rfl]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]
  rfl

theorem p3_facts (s : MachineState) (p E D : Nat) (r : P3PairReady s p E D) (y1 y2 : Sampling.Block) :
    (p3a s).getReg .x10 = wordAddress (E + 7) ∧ (p3a s).getReg .x12 = wordAddress D ∧
    (p3a s).pc = cpc (p3Index p + 3) ∧
    (p3b s D y1).getReg .x10 = wordAddress (E + 32) ∧ (p3b s D y1).getReg .x12 = wordAddress (D + 25) ∧
    (p3b s D y1).pc = cpc (p3Index p + 7) ∧
    (p3w2 s D y1 y2).getReg .x10 = wordAddress (E + 32) ∧ (p3w2 s D y1 y2).getReg .x12 = wordAddress (D + 25) ∧
    (p3w2 s D y1 y2).pc = cpc (p3Index (p + 1)) ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → (p3a s).getReg g = s.getReg g ∧ (p3b s D y1).getReg g = s.getReg g ∧
      (p3w2 s D y1 y2).getReg g = s.getReg g) ∧
    (seg1 s 312).getReg .x10 = wordAddress (E + 7) ∧ (seg1 (p3w1 s D y1) 200).getReg .x10 = wordAddress (E + 32) := by
  have low := r.low
  have lowD := r.lowD
  have wr (t : MachineState) (d : Word) (a : Sampling.Block) (g : Reg) : (writeBits t d a).getReg g = t.getReg g :=
    CommitGolfCandidate.writeBits_register _ _ _ _
  have wpc (t : MachineState) (d : Word) (a : Sampling.Block) : (writeBits t d a).pc = t.pc + 4 :=
    by simp only [writeBits, MachineState.setPC]
  obtain ⟨a10, _, apc, akeep⟩ := seg1_facts s 312
  have s10 : (seg1 s 312).getReg .x10 = wordAddress (E + 7) := by
    rw [a10, r.source, imm312, address_up]; congr 1 <;> omega
  obtain ⟨t10, t12, tpc, tkeep, _⟩ := tag_facts (seg1 s 312) 168
  have a12 : (p3a s).getReg .x12 = wordAddress D := by
    change (execInstrBr (execInstrBr (seg1 s 312) (.SD .x10 .x10 168)) (.ADDI .x12 .x12 200)).getReg .x12 = _
    rw [t12, akeep .x12 (by decide), r.target, imm200, address_up]; congr 1 <;> omega
  have pa : (p3a s).pc = cpc (p3Index p + 3) := by
    change (execInstrBr (execInstrBr (seg1 s 312) (.SD .x10 .x10 168)) (.ADDI .x12 .x12 200)).pc = _
    rw [tpc, apc, r.pc, cpc_next, cpc_next, cpc_next]
  have pa10 : (p3a s).getReg .x10 = wordAddress (E + 7) := by
    change (execInstrBr (execInstrBr (seg1 s 312) (.SD .x10 .x10 168)) (.ADDI .x12 .x12 200)).getReg .x10 = _
    rw [t10, s10]
  obtain ⟨b10, _, bpc0, bkeep⟩ := seg1_facts (p3w1 s D y1) 200
  have u10 : (seg1 (p3w1 s D y1) 200).getReg .x10 = wordAddress (E + 32) := by
    rw [b10, p3w1, wr, pa10, imm200, address_up]
  obtain ⟨c10, c12, cpc', ckeep, _⟩ := tag_facts (seg1 (p3w1 s D y1) 200) 16
  have pb10 : (p3b s D y1).getReg .x10 = wordAddress (E + 32) := by
    change (execInstrBr (execInstrBr (seg1 (p3w1 s D y1) 200) (.SD .x10 .x10 16)) (.ADDI .x12 .x12 200)).getReg .x10 = _
    rw [c10, u10]
  have pb12 : (p3b s D y1).getReg .x12 = wordAddress (D + 25) := by
    change (execInstrBr (execInstrBr (seg1 (p3w1 s D y1) 200) (.SD .x10 .x10 16)) (.ADDI .x12 .x12 200)).getReg .x12 = _
    rw [c12, bkeep .x12 (by decide), p3w1, wr, a12, imm200, address_up]
  have pbpc : (p3b s D y1).pc = cpc (p3Index p + 7) := by
    change (execInstrBr (execInstrBr (seg1 (p3w1 s D y1) 200) (.SD .x10 .x10 16)) (.ADDI .x12 .x12 200)).pc = _
    rw [cpc', bpc0, p3w1, wpc, pa, cpc_next, cpc_next, cpc_next, cpc_next]
  refine ⟨pa10, a12, pa, pb10, pb12, pbpc, by rw [p3w2, wr, pb10], by rw [p3w2, wr, pb12], ?_, ?_, s10, u10⟩
  · rw [p3w2, wpc, pbpc, cpc_next]; congr 1 <;> (unfold p3Index; omega)
  · intro g h10 h12
    have ka : (p3a s).getReg g = s.getReg g := by
      change (execInstrBr (execInstrBr (seg1 s 312) (.SD .x10 .x10 168)) (.ADDI .x12 .x12 200)).getReg g = _
      rw [tkeep g h12, akeep g h10]
    have kb : (p3b s D y1).getReg g = s.getReg g := by
      change (execInstrBr (execInstrBr (seg1 (p3w1 s D y1) 200) (.SD .x10 .x10 16)) (.ADDI .x12 .x12 200)).getReg g = _
      rw [ckeep g h12, bkeep g h10, p3w1, wr, ka]
    exact ⟨ka, kb, by rw [p3w2, wr, kb]⟩

theorem p3w1_eq (s : MachineState) (D : Nat) (y1 : Sampling.Block) :
    writeBits (p3a s) (wordAddress D) y1 = p3w1 s D y1 := rfl
theorem p3w2_eq (s : MachineState) (D : Nat) (y1 y2 : Sampling.Block) :
    writeBits (p3b s D y1) (wordAddress (D + 25)) y2 = p3w2 s D y1 y2 := rfl
theorem p3w1_pc (s : MachineState) (p E D : Nat) (r : P3PairReady s p E D) (y1 : Sampling.Block) :
    (p3w1 s D y1).pc = cpc (p3Index p + 4) := by
  rw [p3w1, show ∀ (t : MachineState) (d : Word) (a : Sampling.Block), (writeBits t d a).pc = t.pc + 4 from
    fun t d a => by simp only [writeBits, MachineState.setPC], (p3_facts s p E D r y1 y1).2.2.1, cpc_next]

attribute [local irreducible] p3w1 p3w2

theorem execute_p3_pair (s : MachineState) (p E D : Nat) (r : P3PairReady s p E D) (fuel : Nat) :
    execute packedWideCommitImage (8 + fuel) s true =
      (do let t ← p3PairTrace s E D
          let res ← execute packedWideCommitImage fuel t true
          return res.charge 66 2) := by
  have hp := r.pair
  have bd := r.bound
  have bdD := r.boundD
  have F (k : Nat) (hk : k < 8) (u : MachineState) (h : u.pc = cpc (p3Index p + k)) :
      fetch packedWideCommitImage u = some (.base (opAt p3Ops k)) := fetch_p3 p hp k hk u h
  have P := p3_facts s p E D r
  rw [show 8 + fuel = 3 + ((3 + (fuel + 1)) + 1) by omega,
    run_tag3 s (p3Index p) 312 168 _ r.pc (fun u h => F 0 (by decide) u (by simpa using h))
      (F 1 (by decide)) (F 2 (by decide))
      (by rw [(P 0 0).2.2.2.2.2.2.2.2.2.2.1, imm168]; exact word_access (E + 7) 21 (by omega)),
    show execInstrBr (execInstrBr (seg1 s 312) (.SD .x10 .x10 168)) (.ADDI .x12 .x12 200) = p3a s from rfl,
    execute_permutation_call _ (3 + (fuel + 1)) (p3a s) true (E + 7) D (by omega) (by omega)
      (P 0 0).1 (P 0 0).2.1
      (((P 0 0).2.2.2.2.2.2.2.2.2.1 .x5 (by decide) (by decide)).1.trans r.selector)
      (((P 0 0).2.2.2.2.2.2.2.2.2.1 .x11 (by decide) (by decide)).1.trans r.size)
      (((P 0 0).2.2.2.2.2.2.2.2.2.1 .x13 (by decide) (by decide)).1.trans r.primitive)
      (F 3 (by decide) _ (P 0 0).2.2.1)]
  simp only [p3PairTrace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro y1 _
  rw [p3w1_eq,
    run_tag3 (p3w1 s D y1) (p3Index p + 4) 200 16 _ (p3w1_pc s p E D r y1) (F 4 (by decide))
      (fun u h => F 5 (by decide) u (by rw [h])) (fun u h => F 6 (by decide) u (by rw [h]))
      (by rw [(P y1 0).2.2.2.2.2.2.2.2.2.2.2, imm16]; exact word_access (E + 32) 2 (by omega)),
    show execInstrBr (execInstrBr (seg1 (p3w1 s D y1) 200) (.SD .x10 .x10 16)) (.ADDI .x12 .x12 200) = p3b s D y1
      from rfl,
    execute_permutation_call _ fuel (p3b s D y1) true (E + 32) (D + 25) (by omega) (by omega)
      (P y1 0).2.2.2.1 (P y1 0).2.2.2.2.1
      (((P y1 0).2.2.2.2.2.2.2.2.2.1 .x5 (by decide) (by decide)).2.1.trans r.selector)
      (((P y1 0).2.2.2.2.2.2.2.2.2.1 .x11 (by decide) (by decide)).2.1.trans r.size)
      (((P y1 0).2.2.2.2.2.2.2.2.2.1 .x13 (by decide) (by decide)).2.1.trans r.primitive)
      (F 7 (by decide) _ (P y1 0).2.2.2.2.2.1)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro y2 _
  rw [p3w2_eq]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

end TwoPermutationPrototype.RV64.C3P
