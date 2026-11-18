import CommitGolfCandidate.K3OpenChainLink

/-! Opener chain block (rows 777..795 and the link groups at rows 4..14), execution: `chain_run`. Owner: S9-L2
(draft by S9-L2; 4-unrolled links). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

/-- The chain trace as the keyed call followed by the link phase. -/
theorem chain_trace_keyed (h : MachineState) (i : Index) :
    chainTrace h i=keyedTrace h (fun a => if chainLinks i=0 then pure (walkRows a chainSkipRows) else
      linkGroupTrace (chainLinks i/4) (walkRows a chainEnterRows) >>= fun g =>
        restTrace (chainLinks i%4) (walkRows g groupOutRows) >>= fun b => pure (walkRows b chainExitRows)) := rfl

theorem chain_run (h : MachineState) (i : Index) (e : ChainEntry h i) (fuel : Nat) :
    execute openingImage (chainSteps i+fuel) h true =
      (do let t ← chainTrace h i; let z ← execute openingImage fuel t true
          return z.charge (chainCycles i) (chainCalls i)) := by
  obtain ⟨preOk,_,_,_,_,_⟩ := chain_before h i e
  have lt := links_lt i
  rw [chain_trace_keyed]
  by_cases zero : chainLinks i=0
  · refine Runs.congr (rows_then h chainPreRows preOk chain_pre_fetch
      (keyed_then h i e (m:=1) (D:=1) (L:=0) fun z => ?_)) ?_ ?_ ?_ fuel
    · obtain ⟨apc,_,a30,_⟩ := after_keyed h i e z
      obtain ⟨ok,_,_,_⟩ := skip_rows _ apc (by rw [a30,zero])
      try dsimp only
      rw [if_pos zero]
      exact runs_rows _ chainSkipRows ok chain_skip_fetch
    · rw [pre_len]; simp only [chainSteps,zero,ite_true]
    · rw [pre_price]; simp only [chainCycles,chainSteps,chainCalls,zero,ite_true]
    · simp only [chainCalls,zero]
  · let q := chainLinks i/4
    let r := chainLinks i%4
    refine Runs.congr (rows_then h chainPreRows preOk chain_pre_fetch
      (keyed_then h i e (m:=3+(7*q+(4+(4*r+1)))) (D:=3+(35*q+(4+(11*r+1)))) (L:=4*q+(r+0)) fun z => ?_))
      ?_ ?_ ?_ fuel
    · obtain ⟨c,hc⟩ : ∃ c, chainLinks i=c+1 := ⟨chainLinks i-1,by omega⟩
      obtain ⟨apc,akeep,a30,_⟩ := after_keyed h i e z
      obtain ⟨el,epc,e10,ekeep,_⟩ := enter_rows _ c apc (by rw [a30,hc]) (by omega)
      have kept (x : Reg) (a : x≠.x7) (b : x≠.x28) (c : x≠.x30) (d : x≠.x31) (f : x≠.x10) :=
        (ekeep x f).trans (akeep x a b c d)
      have ready : LinkGroupReady (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows) (4*q+r) :=
        ⟨epc,(ekeep _ (by decide)).trans (a30.trans (by congr 1; omega)),
          ⟨e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
            (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output,
            (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.selector,
            (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.width,
            (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.primitive⟩⟩
      try dsimp only
      rw [if_neg zero]
      refine (rows_then _ chainEnterRows el chain_enter_fetch
        (group_then q r _ ready (by omega) (m:=4+(4*r+1)) (D:=4+(11*r+1)) (L:=r+0) fun g rg => ?_)).congr
        (by rw [enter_len]) (by rw [enter_price]) rfl
      obtain ⟨ol,op⟩ := out_rows g r (by omega) rg.pc rg.count
      exact (rows_then g groupOutRows ol group_out_fetch
        (rest_then r _ ⟨op.pc,op.r30,rg.regs.keep op.keep⟩ (by omega)
          fun b bpc => runs_rows b chainExitRows ⟨bpc,rfl,trivial⟩ chain_exit_fetch)).congr
        (by rw [out_len,exit_len]) (by rw [out_price,exit_price]) rfl
    · rw [pre_len]; simp only [chainSteps,zero,ite_false,q,r]; omega
    · rw [pre_price]; simp only [chainCycles,chainSteps,chainCalls,zero,ite_false,q,r]; omega
    · simp only [chainCalls,q,r]; omega

end TwoPermutationPrototype.GroupedOpening
