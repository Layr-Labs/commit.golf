import CommitGolfCandidate.QuadNonceCommitLoop

/-! Execution of the paired permutation expansion for every possible reply. -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 14000
set_option maxHeartbeats 650000
attribute [local irreducible] execute chainAdvance writeBits chainPermReply image

/-- Exact one-call execution: even calls do ECALL + one ADDI, odd calls do ECALL + two ADDIs;
the group latch is fetched after the last odd call of a 64-call group. -/
theorem nonce_chain_step (s : MachineState) (j : Nat) (hj : j < nonceChainCount)
    (h : NonceChainFrame s j) (fuel : Nat) :
    execute image ((2 + j%2 + (if j%64=63 then 1 else 0))+fuel) s true =
      (do let y ← World.query (.inr (.inr (.inl (chainPermInput s))))
          let r ← execute image fuel (chainAdvance s j y) true
          return r.charge (9 + j%2 + (if j%64=63 then 1 else 0)) 1) := by
  let tail := if j%64=63 then 1 else 0
  have pc : s.pc = BitVec.ofNat 64 (nonceChainPC j) := h.pc
  have packetIdx : copyOf j < 32 := Nat.mod_lt _ (by decide)
  have slot : j%2 = 0 ∨ j%2 = 1 := by omega
  -- fetch the ECALL at the right word of the packet
  have fetchCall : fetch image s = some (.base .ECALL) := by
    rcases slot with even | odd
    · exact nonce_chain_packet (copyOf j) 0 packetIdx (by decide) s (by
        rw [pc]; unfold nonceChainPC; simp only [if_neg (Nat.ne_of_lt hj), even]
        congr 1; omega)
    · exact nonce_chain_packet (copyOf j) 2 packetIdx (by decide) s (by
        rw [pc]; unfold nonceChainPC; simp only [if_neg (Nat.ne_of_lt hj), odd]
        congr 1; omega)
  have source : (s.getReg .x10).toNat = nonceChainSource j := by
    rw [h.input, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold nonceChainSource nonceChainBase; dsimp [nonceChainCount] at hj; omega)]
  have dest : (s.getReg .x12).toNat = nonceChainDest j := by
    rw [h.output, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold nonceChainDest nonceChainBase; dsimp [nonceChainCount] at hj; omega)]
  have call := chain_perm_call _ s (1+j%2+(tail+fuel)) true fetchCall h.ready
    (by rw [source]; unfold nonceChainSource nonceChainBase; omega)
    (by rw [dest]; unfold nonceChainDest nonceChainBase; omega)
    (by rw [source]; unfold nonceChainSource nonceChainBase MEMORY_BYTES; dsimp [nonceChainCount] at hj; omega)
    (by rw [dest]; unfold nonceChainDest nonceChainBase MEMORY_BYTES; dsimp [nonceChainCount] at hj; omega)
  have hstep : (2+j%2+tail)+fuel = 1+(1+j%2+(tail+fuel)) := by omega
  rw [hstep, call]
  apply bind_congr
  intro y
  set w := chainPermReply s y with _hw
  -- execute the increment instructions after the ECALL
  rcases slot with even | odd
  · -- even call: one ADDI (x12 += 176)
    have wpc : w.pc = BitVec.ofNat 64 (nonceChainPC j + 4) := by
      rw [show w.pc = s.pc + 4 from nonce_reply_pc s y, pc]
      simp only [BitVec.ofNat_add]
      rfl
    have wpc2 : w.pc = BitVec.ofNat 64 (995720 + 20 * copyOf j + 4) := by
      rw [wpc]
      unfold nonceChainPC
      simp only [if_neg (Nat.ne_of_lt hj), even]
      congr 1
      omega
    simp only [even, Nat.add_zero]
    rw [nonce_increments_execute (copyOf j) packetIdx w wpc2]
    simp only [bind_assoc, pure_bind]
    have h2dvd : (2:ℕ) ∣ 64 := by norm_num
    have notEdge : j%64 ≠ 63 := by
      intro h63
      have hmod : (j % 64) % 2 = j % 2 := Nat.mod_mod_of_dvd j h2dvd
      rw [h63] at hmod
      norm_num at hmod
      omega
    have hj1 : j+1 ≠ nonceChainCount := by dsimp [nonceChainCount] at hj ⊢; omega
    have tail0 : tail = 0 := by
      show (if j % 64 = 63 then 1 else 0) = 0
      have hne : ¬(j%64=63) := notEdge
      simp [hne]
    have hdiv : (j+1)/2 = j/2 := by omega
    have nextPc : (nonceIncrementsEven w).pc = BitVec.ofNat 64 (nonceChainPC (j+1)) := by
      show (execInstrBr w (.ADDI .x12 .x12 176)).pc = _
      simp only [execInstrBr, MachineState.getReg_setPC, MachineState.setPC]
      rw [wpc2]
      simp only [BitVec.ofNat_add]
      unfold nonceChainPC nonceChainCount copyOf
      simp only [if_neg hj1, even]
      congr 1
      simp only [hdiv]
      have h2 : (j+1) % 2 = 1 := by omega
      simp only [h2]
      congr 1
      simp only [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      congr 1
      omega
    have setPcId : (nonceIncrementsEven w).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) = nonceIncrementsEven w := by
      simp only [MachineState.setPC]
      congr 1
      rw [←nextPc]
      rfl
    have eq : chainAdvance s j y = nonceIncrementsEven w := by
      rw [chain_advance_eq, nonceIncrements]
      split
      · simp only [nonceIncrementsEven]
        exact setPcId
      · next h => exact absurd h (by omega)
    rw [tail0, eq]
    simp only [Nat.zero_add]
    apply bind_congr
    intro r
    simp [Execution.charge, Nat.add_assoc] <;> omega
  · -- odd call: two ADDIs (x10 += 352, x12 += 176)
    have wpc : w.pc = BitVec.ofNat 64 (nonceChainPC j + 4) := by
      rw [show w.pc = s.pc + 4 from nonce_reply_pc s y, pc]
      simp only [BitVec.ofNat_add]
      rfl
    have wpc2 : w.pc = BitVec.ofNat 64 (995720 + 20 * copyOf j + 12) := by
      rw [wpc]
      unfold nonceChainPC
      simp only [if_neg (Nat.ne_of_lt hj), odd]
      congr 1
      omega
    simp only [odd, Nat.add_one, Nat.add_assoc]
    rw [nonce_increments_execute_odd (copyOf j) packetIdx w wpc2]
    simp only [bind_assoc, pure_bind]
    let advance := nonceIncrementsOdd w
    by_cases edge : j%64=63
    · -- odd edge call: latch follows
      have apc : advance.pc = BitVec.ofNat 64 996360 := by
        show (nonceIncrementsOdd w).pc = _
        unfold nonceIncrementsOdd
        simp only [execInstrBr, MachineState.getReg_setPC, MachineState.setPC]
        rw [wpc2]
        congr 1
        have hc : copyOf j = 31 := by
          unfold copyOf
          omega
        rw [hc]
        decide
      have output := (chain_advance_frame s j y h).output
      have limit := (chain_advance_frame s j y h).limit
      have key : chainAdvance s j y = advance.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := by
        show chainAdvance s j y = (nonceIncrementsOdd w).setPC (BitVec.ofNat 64 (nonceChainPC (j+1)))
        rw [chain_advance_eq]
        show (nonceIncrements (chainPermReply s y) j).setPC _ = (nonceIncrementsOdd (chainPermReply s y)).setPC _
        rw [nonceIncrements, odd, ←_hw]
        rfl
      rw [key, MachineState.getReg_setPC] at output limit
      have latch := nonce_latch_pc advance j edge hj (by rw [apc]; rfl) output limit
      have br := execute_ordinary_step image (.base (.BLTU .x12 .x7 7552))
        advance (chainAdvance s j y) fuel true (nonce_chain_latch _ (by rw [apc]; rfl)) (by
          change some (execInstrBr advance (.BLTU .x12 .x7 7552)) = _
          rw [latch, key])
      simp only [tail, edge, ite_true, Nat.add_comm 1 fuel]
      rw [br]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro r
      simp [Execution.charge, instructionCycles, Nat.add_assoc] <;> omega
    · -- odd non-edge: increments end at next packet's ECALL
      have hj1 : j+1 ≠ nonceChainCount := by dsimp [nonceChainCount] at hj ⊢; omega
      have nextPc : advance.pc = BitVec.ofNat 64 (nonceChainPC (j+1)) := by
        show (nonceIncrementsOdd w).pc = _
        unfold nonceIncrementsOdd
        simp only [execInstrBr, MachineState.getReg_setPC, MachineState.setPC]
        rw [wpc2]
        unfold nonceChainPC nonceChainCount copyOf
        simp only [if_neg hj1, odd]
        congr 1
        have hdiv : (j+1)/2 = j/2 + 1 := by omega
        rw [hdiv]
        have hcne : copyOf j ≠ 31 := by
          intro h31
          have : j % 64 = 63 := by
            unfold copyOf at h31
            omega
          omega
        unfold copyOf at hcne
        have hlt : j/2 % 32 < 32 := Nat.mod_lt _ (by norm_num)
        have hne : j/2 % 32 ≠ 31 := hcne
        have hlt2 : j/2 % 32 + 1 < 32 := by omega
        have hmod : (j/2 + 1) % 32 = j/2 % 32 + 1 := by
          rw [Nat.add_mod]
          simp only [Nat.one_mod, Nat.add_zero]
          exact Nat.mod_eq_of_lt hlt2
        rw [hmod]
        congr 1
        have h2 : (j+1) % 2 = 0 := by omega
        rw [h2]
        simp only [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
        congr 1
        omega
      have setPcId : (nonceIncrementsOdd w).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) = nonceIncrementsOdd w := by
        simp only [MachineState.setPC]
        congr 1
        rw [←nextPc]
        rfl
      have eq : chainAdvance s j y = nonceIncrementsOdd w := by
        rw [chain_advance_eq, nonceIncrements, odd, ←_hw]
        exact setPcId
      simp only [tail, edge, ite_false, Nat.zero_add]
      rw [eq]
      apply bind_congr
      intro r
      simp [Execution.charge, Nat.add_assoc] <;> omega

/-- One-step identities for the step and cycle ledgers (unconditional). -/
theorem hstep_all (k : Nat) :
    nonceChainSteps (k+1) - nonceChainSteps k = 2 + k%2 + (if k%64=63 then 1 else 0) := by
  unfold nonceChainSteps
  by_cases edge : k%64=63
  · rw [if_pos edge]
    omega
  · rw [if_neg edge]
    omega

theorem hstep_cycles (k : Nat) :
    nonceChainCycles (k+1) - nonceChainCycles k = 9 + k%2 + (if k%64=63 then 1 else 0) := by
  unfold nonceChainCycles
  by_cases edge : k%64=63
  · rw [if_pos edge]
    omega
  · rw [if_neg edge]
    omega

theorem steps_mono (a d : Nat) : nonceChainSteps a ≤ nonceChainSteps (a+d) := by
  induction d generalizing a with
  | zero => simp only [Nat.add_zero]; omega
  | succ d ih =>
    have heq : a + Nat.succ d = (a + d) + 1 := rfl
    rw [heq]
    have h1 : nonceChainSteps (a + d) ≤ nonceChainSteps ((a + d) + 1) := by
      have h := hstep_all (a + d); omega
    have h2 : nonceChainSteps a ≤ nonceChainSteps (a + d) := ih a
    omega

theorem cycles_mono (a d : Nat) : nonceChainCycles a ≤ nonceChainCycles (a+d) := by
  induction d generalizing a with
  | zero => simp only [Nat.add_zero]; omega
  | succ d ih =>
    have heq : a + Nat.succ d = (a + d) + 1 := rfl
    rw [heq]
    have h1 : nonceChainCycles (a + d) ≤ nonceChainCycles ((a + d) + 1) := by
      have h := hstep_cycles (a + d); omega
    have h2 : nonceChainCycles a ≤ nonceChainCycles (a + d) := ih a
    omega

theorem nonce_chain_run (s : MachineState) (j n : Nat) (limit : j+n ≤ nonceChainCount)
    (h : NonceChainFrame s j) (fuel : Nat) :
    execute image (nonceChainSteps (j+n)-nonceChainSteps j+fuel) s true =
      (do let next ← chainRun j s n
          let result ← execute image fuel next true
          return result.charge (nonceChainCycles (j+n)-nonceChainCycles j) n) := by
  induction n generalizing j s with
  | zero => simp [chainRun, Execution.charge]
  | succ n ih =>
    have hstep : nonceChainSteps (j+1) - nonceChainSteps j =
        2 + j%2 + (if j%64=63 then 1 else 0) := by
      unfold nonceChainSteps
      by_cases edge : j%64=63
      · rw [if_pos edge]
        omega
      · rw [if_neg edge]
        omega
    have steps : nonceChainSteps (j+(n+1))-nonceChainSteps j+fuel =
        (2 + j%2 + (if j%64=63 then 1 else 0)) +
        (nonceChainSteps ((j+1)+n)-nonceChainSteps (j+1)+fuel) := by
      have heq : j + (n+1) = (j+1) + n := by omega
      rw [heq, ← hstep]
      have h1 : nonceChainSteps j ≤ nonceChainSteps (j+1) := by
        have h := hstep_all j; omega
      have h2 : nonceChainSteps (j+1) ≤ nonceChainSteps (j+1+n) := steps_mono (j+1) n
      omega
    rw [steps, nonce_chain_step s j (by omega) h]
    simp only [chainRun, bind_assoc]
    apply bind_congr
    intro y
    rw [ih _ _ (by omega) (chain_advance_frame s j y h)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro last
    apply bind_congr
    intro r
    simp only [Execution.charge]
    congr 2
    · have heq2 : j + (n+1) = (j+1) + n := by omega
      rw [heq2, ← hstep_cycles j]
      have hc1 : nonceChainCycles j ≤ nonceChainCycles (j+1) := by
        have h := hstep_cycles j; omega
      have hc2 : nonceChainCycles (j+1) ≤ nonceChainCycles (j+1+n) := cycles_mono (j+1) n
      omega
    · omega

end TwoPermutationPrototype.Quad.Commit.Chain
