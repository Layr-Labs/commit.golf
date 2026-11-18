import CommitGolfCandidate.QuadNonceCommitLoop

/-! Execution of the unrolled chain for every possible reply, in the form of submission c28dd9ca's
`NonceChainExec` (dadon), with the block-end control of variant B'. -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
attribute [local irreducible] execute chainAdvance writeBits chainPermReply

theorem charge_charge (r : Execution) (a b c d : Nat) :
    (r.charge a b).charge c d = r.charge (c + a) (d + b) := by
  cases r
  simp only [Execution.charge, Execution.mk.injEq, true_and]
  omega

theorem charge_congr {r : Execution} {a b c d : Nat} (h₁ : a = c) (h₂ : b = d) :
    r.charge a b = r.charge c d := by
  rw [h₁, h₂]

private theorem pc_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a+b) :=
  (BitVec.ofNat_add a b).symm

/-- Exact one-call execution, including the block-end control when it is fetched. -/
theorem nonce_chain_step (s : MachineState) (j : Nat) (hj : j < nonceChainCount)
    (h : NonceChainFrame s j) (fuel : Nat) :
    execute image (2+j%2+extra j+fuel) s true =
      (do let y ← World.query (.inr (.inr (.inl (chainPermInput s))))
          let r ← execute image fuel (chainAdvance s j y) true
          return r.charge (9+j%2+extra j) 1) := by
  have slot : copyOf j < unroll := Nat.mod_lt _ (by decide)
  have pc : s.pc = BitVec.ofNat 64 (633008+20*copyOf j+8*(j%2)) := by
    simpa [nonceChainPC,Nat.ne_of_lt hj] using h.pc
  have fetchCall : fetch image s = some (.base .ECALL) := by
    have found := fetch_gen_pair (copyOf j) (2*(j%2)) slot (by omega) s (by rw [pc];congr 1;omega)
    have cases : j%2=0 ∨ j%2=1 := by omega
    rcases cases with h | h <;> simpa [packetOp,h] using found
  have source : (s.getReg .x10).toNat=nonceChainSource j := by
    rw [h.input,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold nonceChainSource nonceChainBase;dsimp [nonceChainCount] at hj;omega)]
  have dest : (s.getReg .x12).toNat=nonceChainDest j := by
    rw [h.output,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold nonceChainDest nonceChainBase;dsimp [nonceChainCount] at hj;omega)]
  have call := chain_perm_call _ s ((1+j%2)+(extra j+fuel)) true fetchCall h.ready
    (by rw [source]; unfold nonceChainSource nonceChainBase;omega)
    (by rw [dest]; unfold nonceChainDest nonceChainBase;omega)
    (by rw [source]; unfold nonceChainSource nonceChainBase MEMORY_BYTES;dsimp [nonceChainCount] at hj;omega)
    (by rw [dest]; unfold nonceChainDest nonceChainBase MEMORY_BYTES;dsimp [nonceChainCount] at hj;omega)
  rw [show 2+j%2+extra j+fuel = 1+((1+j%2)+(extra j+fuel)) by omega, call]
  apply bind_congr
  intro y
  let w := chainPermReply s y
  have wpc : w.pc = BitVec.ofNat 64 (4096+4*(157228+5*copyOf j+2*(j%2)+1)) := by
    rw [show w.pc=s.pc+4 from nonce_reply_pc s y,pc,show (4 : Word) = BitVec.ofNat 64 4 from rfl,pc_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  let advance := nonceIncrements w j
  have next := chain_advance_frame s j y h
  have apc : advance.pc = BitVec.ofNat 64 (4096+4*(157228+5*copyOf j+2+3*(j%2))) := by
    rw [show advance.pc=w.pc+BitVec.ofNat 64 (4*(1+j%2)) from nonce_increments_pc w j,wpc,pc_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have key : chainAdvance s j y = advance.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := chain_advance_eq s j y
  rw [nonce_increments_execute (copyOf j) j slot w wpc]
  simp only [bind_assoc,pure_bind]
  have output := next.output
  have limit := next.limit
  rw [key, MachineState.getReg_setPC] at output limit
  by_cases edge : j%2=1 ∧ copyOf j = unroll-1
  · have atBranch : advance.pc = BitVec.ofNat 64 (4096+4*236668) := by
      rw [apc,edge.1,edge.2]
      rfl
    have compare := latch_compare advance j hj output limit
    by_cases last : j+1 = nonceChainCount
    · -- the branch is taken: the exit
      have taken : execInstrBr advance (.BGEU .x12 .x7 8) = advance.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := by
        have notLess : ¬ (j+1 < nonceChainCount) := by omega
        simp only [execInstrBr,compare,notLess,decide_false,Bool.false_eq_true,not_false_eq_true,ite_true,atBranch]
        rw [nonceChainPC,if_pos last]
        exact congrArg advance.setPC (by decide)
      have br := execute_ordinary_step image (.base (.BGEU .x12 .x7 8))
        advance (chainAdvance s j y) fuel true (by simpa [genTailOps] using fetch_gen_tail 0 (by decide) _ (by simpa using atBranch)) (by
          change some (execInstrBr advance (.BGEU .x12 .x7 8)) = _
          rw [taken,key])
      have ex : extra j = 1 := by unfold extra; rw [if_pos edge, if_pos last]
      rw [ex,Nat.add_comm 1 fuel,br]
      simp only [bind_assoc,pure_bind]
      apply bind_congr
      intro r
      exact congrArg _ (by rw [charge_charge,charge_charge]; all_goals exact charge_congr (by simp [instructionCycles] <;> omega) rfl)
    · -- falls through to the backward jump
      have fall : execInstrBr advance (.BGEU .x12 .x7 8) = advance.setPC (BitVec.ofNat 64 (4096+4*236669)) := by
        have less : j+1 < nonceChainCount := by have := hj; omega
        simp only [execInstrBr,compare,less,decide_true,not_true_eq_false,ite_false,atBranch]
        rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl,pc_add]
      let mid := advance.setPC (BitVec.ofNat 64 (4096+4*236669))
      have back : execInstrBr mid (.JAL .x0 1779388) = advance.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := by
        have wrap : copyOf (j+1) = 0 := by
          unfold copyOf at edge ⊢
          unfold unroll at edge ⊢
          omega
        have notLast : j+1 ≠ nonceChainCount := last
        have target : BitVec.ofNat 64 (4096+4*236669) + signExtend21 1779388 =
            BitVec.ofNat 64 (nonceChainPC (j+1)) := by
          have evenNext : (j+1)%2=0 := by omega
          rw [nonceChainPC,if_neg notLast,wrap,evenNext]
          decide
        calc execInstrBr mid (.JAL .x0 1779388) = mid.setPC (mid.pc + signExtend21 1779388) := rfl
          _ = advance.setPC (BitVec.ofNat 64 (4096+4*236669) + signExtend21 1779388) := rfl
          _ = _ := by rw [target]
      have br := execute_ordinary_step image (.base (.BGEU .x12 .x7 8))
        advance mid (fuel+1) true (by simpa [genTailOps] using fetch_gen_tail 0 (by decide) _ (by simpa using atBranch)) (by
          change some (execInstrBr advance (.BGEU .x12 .x7 8)) = _
          rw [fall])
      have jmp := execute_ordinary_step image (.base (.JAL .x0 1779388))
        mid (chainAdvance s j y) fuel true (by simpa [genTailOps] using fetch_gen_tail 1 (by decide) mid rfl) (by
          change some (execInstrBr mid (.JAL .x0 1779388)) = _
          rw [back,key])
      have ex : extra j = 2 := by unfold extra; rw [if_pos edge, if_neg last]
      rw [ex,show 2+fuel = (fuel+1)+1 by omega,br,jmp]
      simp only [bind_assoc,pure_bind]
      apply bind_congr
      intro r
      exact congrArg _ (by rw [charge_charge,charge_charge,charge_charge]; all_goals exact charge_congr (by simp [instructionCycles] <;> omega) rfl)
  · have nextPc : advance.pc = BitVec.ofNat 64 (nonceChainPC (j+1)) := by
      have notLast : j+1 ≠ nonceChainCount := by
        intro hl
        apply edge
        unfold copyOf unroll
        dsimp [nonceChainCount] at hl
        omega
      have step : 5*copyOf (j+1)+2*((j+1)%2)=5*copyOf j+2+3*(j%2) := by
        unfold copyOf unroll at edge ⊢
        omega
      rw [apc,nonceChainPC,if_neg notLast]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have eq : advance = chainAdvance s j y := by
      rw [key,← nextPc]
      cases advance
      rfl
    have ex : extra j = 0 := by unfold extra; rw [if_neg edge]
    rw [ex]
    simp only [Nat.zero_add]
    rw [←eq]
    apply bind_congr
    intro r
    exact congrArg _ (by rw [charge_charge]; all_goals exact charge_congr (by omega) rfl)

theorem steps_succ (j : Nat) (hj : j < nonceChainCount) :
    nonceChainSteps (j+1) = nonceChainSteps j + (2+j%2 + extra j) := by
  unfold nonceChainSteps extra copyOf unroll
  dsimp [nonceChainCount] at hj ⊢
  split <;> split <;> split <;> (try split) <;> omega

theorem cycles_succ (j : Nat) (hj : j < nonceChainCount) :
    nonceChainCycles (j+1) = nonceChainCycles j + (9+j%2 + extra j) := by
  unfold nonceChainCycles extra copyOf unroll
  dsimp [nonceChainCount] at hj ⊢
  split <;> split <;> split <;> (try split) <;> omega

theorem steps_mono (a b : Nat) (hab : a ≤ b) (hb : b ≤ nonceChainCount) :
    nonceChainSteps a ≤ nonceChainSteps b := by
  have half : a/2 ≤ b/2 := by omega
  have tiles : (a/2)/15888 ≤ (b/2)/15888 := by omega
  unfold nonceChainSteps unroll
  dsimp [nonceChainCount] at hb ⊢
  split <;> split <;> omega

theorem cycles_mono (a b : Nat) (hab : a ≤ b) (hb : b ≤ nonceChainCount) :
    nonceChainCycles a ≤ nonceChainCycles b := by
  have half : a/2 ≤ b/2 := by omega
  have tiles : (a/2)/15888 ≤ (b/2)/15888 := by omega
  unfold nonceChainCycles unroll
  dsimp [nonceChainCount] at hb ⊢
  split <;> split <;> omega

theorem nonce_chain_run (s : MachineState) (j n : Nat) (limit : j+n ≤ nonceChainCount)
    (h : NonceChainFrame s j) (fuel : Nat) :
    execute image (nonceChainSteps (j+n)-nonceChainSteps j+fuel) s true =
      (do let next ← chainRun j s n
          let result ← execute image fuel next true
          return result.charge (nonceChainCycles (j+n)-nonceChainCycles j) n) := by
  induction n generalizing j s with
  | zero => simp [chainRun,Execution.charge]
  | succ n ih =>
    have mono := steps_mono (j+1) ((j+1)+n) (by omega) (by omega)
    have monoC := cycles_mono (j+1) ((j+1)+n) (by omega) (by omega)
    have stepsEq : nonceChainSteps (j+(n+1))-nonceChainSteps j+fuel =
        2+j%2+extra j+(nonceChainSteps ((j+1)+n)-nonceChainSteps (j+1)+fuel) := by
      rw [show j+(n+1) = (j+1)+n by omega, steps_succ j (by omega)] at *
      omega
    rw [stepsEq,nonce_chain_step s j (by omega) h]
    simp only [chainRun,bind_assoc]
    apply bind_congr
    intro y
    rw [ih _ _ (by omega) (chain_advance_frame s j y h)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro last
    apply bind_congr
    intro r
    simp only [Execution.charge]
    have cyc := cycles_succ j (by omega)
    rw [show j+(n+1) = (j+1)+n by omega]
    congr 2 <;> omega

end TwoPermutationPrototype.Quad.Commit.Chain
