import CommitGolfCandidate.TwoPermutationPackedCapRoot
import CommitGolfCandidate.TwoPermutationCheckerRootRun

/-! One-byte search image: a root mismatch goes to the search block at word 1163 instead of the reject. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt word_offset aligned_access)

structure RootScanReady (state : MachineState) (claim left : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*(345+3*(4-left)))
  roots : state.getReg .x25 = wordAddress 2048
  commitment : state.getReg .x9 = wordAddress claim
  claimBound : claim+4 ≤ 2^33

theorem root_word_unchanged (before after : MachineState)
    (mem : after.mem = before.mem) (r25 : after.getReg .x25 = before.getReg .x25)
    (r9 : after.getReg .x9 = before.getReg .x9) (i : Fin 4) :
    rootWordMatches after i ↔ rootWordMatches before i := by
  simp [rootWordMatches, MachineState.getMem, mem, r25, r9]

private theorem root_scan_addresses {state : MachineState} {claim left : Nat}
    (ready : RootScanReady state claim left) (i : Fin 4) :
    accessValid (state.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true ∧
      accessValid (state.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true := by
  rw [ready.roots, ready.commitment, show 32+8*i.val = 8*(4+i.val) by omega, word_offset, word_offset]
  exact ⟨aligned_access _ (by omega), aligned_access _ (by have := ready.claimBound; omega)⟩

attribute [local irreducible] execute

theorem root_charge_charge (z : Execution) (a b : Nat) : (z.charge a 0).charge b 0 = z.charge (a+b) 0 := by
  cases z
  simp only [Execution.charge, Execution.mk.injEq, true_and, Nat.add_zero, and_true]
  omega

/-- One-byte search: the root scan either accepts, or reaches the search block (word 1163, `0x222c`) at the first
mismatching root word, with memory and every register but `x29`/`x30` unchanged. -/
theorem execute_root_scan {state : MachineState} {claim left : Nat}
    (ready : RootScanReady state claim left) (bounded : left ≤ 4) :
    ((∀ i : Fin 4, 4-left ≤ i.val → rootWordMatches state i) ∧
      ∃ result : Execution, result.exit = .success ∧ result.oracleCalls = 0 ∧
        ∀ fuel, execute packedImage (3*left+3+fuel) state false = pure result) ∨
    (¬ (∀ i : Fin 4, 4-left ≤ i.val → rootWordMatches state i) ∧
      ∃ (t : MachineState) (c : Nat), c ≤ 3*left ∧ t.pc = 0x222c ∧ t.mem = state.mem ∧
        (∀ r : Reg, r ≠ .x29 → r ≠ .x30 → t.getReg r = state.getReg r) ∧
        ∀ fuel, execute packedImage (c+fuel) state false =
          (do let z ← execute packedImage fuel t false; return z.charge c 0)) := by
  induction left generalizing state with
  | zero =>
    have pc : state.pc = 0x1594 := ready.pc
    refine Or.inl ⟨fun i impossible => by have := i.isLt; omega, ⟨.success, acceptState state, 3, 0⟩, rfl, rfl,
      fun fuel => ?_⟩
    simpa using execute_accept state pc fuel
  | succ left ih =>
    let i : Fin 4 := ⟨4-(left+1), by omega⟩
    let next := rootCompare state i
    have pc : state.pc = BitVec.ofNat 64 (4096+4*(345+3*i.val)) := ready.pc
    obtain ⟨cap, claimAccess⟩ := root_scan_addresses ready i
    obtain ⟨nextPC, mem, regs⟩ := root_compare_post state i pc
    have executed (fuel : Nat) := execute_root_compare state i fuel pc cap claimAccess
    have stable := root_word_unchanged state next mem (regs .x25 (by decide) (by decide))
      (regs .x9 (by decide) (by decide))
    by_cases same : rootWordMatches state i
    · have nextReady : RootScanReady next claim left := by
        refine ⟨?_, (regs .x25 (by decide) (by decide)).trans ready.roots,
          (regs .x9 (by decide) (by decide)).trans ready.commitment, ready.claimBound⟩
        change next.pc = _ at nextPC
        rw [nextPC, ite_eq_left same]
        congr 1
        have : i.val = 4-(left+1) := rfl
        omega
      have extend : (∀ j : Fin 4, 4-left ≤ j.val → rootWordMatches next j) ↔
          (∀ j : Fin 4, 4-(left+1) ≤ j.val → rootWordMatches state j) := by
        constructor
        · intro tail j valid
          by_cases first : j = i
          · rwa [first]
          · have jAfter : 4-left ≤ j.val := by
              have : j.val ≠ i.val := fun eq => first (Fin.ext eq)
              have : i.val = 4-(left+1) := rfl
              omega
            exact (stable j).mp (tail j jAfter)
        · intro all j valid
          exact (stable j).mpr (all j (by omega))
      rcases ih nextReady (by omega) with ⟨all, result, accepted, calls, run⟩ | ⟨differs, t, c, cb, tpc, tmem, tregs, run⟩
      · refine Or.inl ⟨extend.mp all, result.charge 3 0, accepted, by simpa [Execution.charge] using calls, ?_⟩
        intro fuel
        rw [show 3*(left+1)+3+fuel = 3+(3*left+3+fuel) by omega, executed, run]
        simp
      · refine Or.inr ⟨fun all => differs (extend.mpr all), t, c+3, by omega, tpc, tmem.trans mem, ?_, ?_⟩
        · intro r a b
          exact (tregs r a b).trans (regs r a b)
        · intro fuel
          rw [show c+3+fuel = 3+(c+fuel) by omega, executed, run]
          simp only [bind_assoc, pure_bind, root_charge_charge]
    · have miss : next.pc = 0x222c := by
        change next.pc = _ at nextPC
        rw [nextPC, ite_eq_right same]
      refine Or.inr ⟨fun all => same (all i (by rfl)), next, 3, by omega, miss, mem, regs, ?_⟩
      intro fuel
      exact executed fuel

theorem root_words_iff (state : MachineState) (claim : Nat)
    (roots : state.getReg .x25 = wordAddress 2048)
    (claimReg : state.getReg .x9 = wordAddress claim) :
    (∀ i : Fin 4, rootWordMatches state i) ↔ capRootAt state 1 = readBuffer state (8*claim) 32 := by
  unfold capRootAt
  rw [read_digest_eq_iff _ _ _ _ (by omega) (by omega)]
  constructor
  · intro words j bounded
    have same := words ⟨j,bounded⟩
    unfold rootWordMatches at same
    rw [roots, claimReg, show 32+8*j = 8*(4+j) by omega, word_offset, word_offset] at same
    simpa only [← Nat.mul_add, wordAddress, Nat.add_assoc] using same
  · intro digest i
    unfold rootWordMatches
    rw [roots, claimReg, show 32+8*i.val = 8*(4+i.val) by omega, word_offset, word_offset]
    simpa only [← Nat.mul_add, wordAddress, Nat.add_assoc] using digest i.val i.isLt

/-- One-byte search: the root check (length, then the four words) rejects when the length differs, accepts when the
root equals the claim, and otherwise reaches the search block (`0x222c`) with memory and every register but
`x29`/`x30` unchanged, after at most 13 steps. -/
theorem execute_root_check (state : MachineState) (claim : Nat) (pc : state.pc = 0x1560)
    (roots : state.getReg .x25 = wordAddress 2048) (claimReg : state.getReg .x9 = wordAddress claim)
    (claimBound : claim+4 ≤ 2^33) :
    (state.getReg .x21 ≠ state.getReg .x22 ∧
      ∀ fuel, execute packedImage (4+fuel) state false = pure ⟨.failure, rejectState (rootLength state), 4, 0⟩) ∨
    (state.getReg .x21 = state.getReg .x22 ∧ capRootAt state 1 = readBuffer state (8*claim) 32 ∧
      ∃ result : Execution, result.exit = .success ∧ result.oracleCalls = 0 ∧
        ∀ fuel, execute packedImage (16+fuel) state false = pure result) ∨
    (state.getReg .x21 = state.getReg .x22 ∧ capRootAt state 1 ≠ readBuffer state (8*claim) 32 ∧
      ∃ (t : MachineState) (c : Nat), c ≤ 13 ∧ t.pc = 0x222c ∧ t.mem = state.mem ∧
        (∀ r : Reg, r ≠ .x29 → r ≠ .x30 → t.getReg r = state.getReg r) ∧
        ∀ fuel, execute packedImage (c+fuel) state false =
          (do let z ← execute packedImage fuel t false; return z.charge c 0)) := by
  obtain ⟨target, mem, stable⟩ := root_length_post state pc
  let next := rootLength state
  have entry : next.getReg .x9 = wordAddress claim := (stable _).trans claimReg
  have endRoots : next.getReg .x25 = wordAddress 2048 := (stable _).trans roots
  have paired (i : Fin 4) := root_word_unchanged state next mem (stable .x25) (stable .x9) i
  have first (fuel : Nat) := execute_root_length state pc fuel
  by_cases length : state.getReg .x21 = state.getReg .x22
  · have entered : RootScanReady next claim 4 := by
      refine ⟨?_, endRoots, entry, claimBound⟩
      change next.pc = _
      rw [target, ite_eq_left length]
      rfl
    have words : (∀ i : Fin 4, 4-4 ≤ i.val → rootWordMatches next i) ↔ capRootAt state 1 = readBuffer state (8*claim) 32 := by
      rw [← root_words_iff state claim roots claimReg]
      simp only [Nat.sub_self, Nat.zero_le, forall_const]
      exact ⟨fun matched i => (paired i).mp (matched i), fun matched i => (paired i).mpr (matched i)⟩
    rcases execute_root_scan entered (by decide) with ⟨all, result, accepted, calls, run⟩ | ⟨differs, t, c, cb, tpc, tmem, tregs, run⟩
    · refine Or.inr (Or.inl ⟨length, words.mp all, result.charge 1 0, accepted, by simpa [Execution.charge] using calls, ?_⟩)
      intro fuel
      rw [show 16+fuel = 1+(3*4+3+fuel) by omega, first, run]
      simp
    · refine Or.inr (Or.inr ⟨length, fun same => differs (words.mpr same), t, c+1, by omega, tpc, tmem.trans mem, ?_, ?_⟩)
      · intro r a b
        exact (tregs r a b).trans (stable r)
      · intro fuel
        rw [show c+1+fuel = 1+(c+fuel) by omega, first, run]
        simp only [bind_assoc, pure_bind, root_charge_charge]
  · have fail : next.pc = 0x15b0 := by rw [target, ite_eq_right length]
    refine Or.inl ⟨length, fun fuel => ?_⟩
    rw [show 4+fuel = 1+(3+fuel) by omega, first, execute_reject next fail fuel]
    simp [Execution.charge]
    rfl

end TwoPermutationPrototype.Packed.Checker
