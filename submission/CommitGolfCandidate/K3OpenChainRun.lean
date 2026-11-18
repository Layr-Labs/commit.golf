import CommitGolfCandidate.K3OpenChainLink

/-! Opener chain block (rows 777..795 and the link calls at rows 896..929), execution: `chain_run`. Owner: S9-L2
(draft by S9-L2; 33-call chain). -/
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
    chainTrace h i=keyedTrace h (fun a => callsTrace (chainLinks i) (walkRows a chainEnterRows) >>= fun t =>
      pure (walkRows t chainOutRows)) := rfl

theorem chain_run (h : MachineState) (i : Index) (e : ChainEntry h i) (fuel : Nat) :
    execute openingImage (chainSteps i+fuel) h true =
      (do let t ← chainTrace h i; let z ← execute openingImage fuel t true
          return z.charge (chainCycles i) (chainCalls i)) := by
  obtain ⟨preOk,_,_,_,_,_⟩ := chain_before h i e
  have lt := links_lt i
  rw [chain_trace_keyed]
  let k := chainLinks i
  refine Runs.congr (rows_then h chainPreRows preOk chain_pre_fetch
    (keyed_then h i e (m:=5+(k+2)) (D:=5+(8*k+2)) (L:=k+0) fun z => ?_)) ?_ ?_ ?_ fuel
  · obtain ⟨apc,akeep,a30,_⟩ := after_keyed h i e z
    obtain ⟨el,epc,e10,ekeep,_⟩ := enter_rows _ k lt apc a30
    have kept (x : Reg) (b1 : x≠.x7) (b2 : x≠.x28) (b3 : x≠.x30) (b4 : x≠.x31) (b5 : x≠.x10) :=
      (ekeep x b1 b5 b4).trans (akeep x b1 b2 b3 b4)
    have regs : CallRegs (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows) :=
      ⟨e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
        (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output,
        (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.selector,
        (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.width,
        (kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.primitive⟩
    exact (rows_then _ chainEnterRows el chain_enter_fetch
      (calls_then k _ epc (by omega) regs fun b bpc _ =>
        runs_rows b chainOutRows (out_rows b bpc).1 chain_out_fetch)).congr
      (by rw [enter_len,out_len]) (by rw [enter_price,out_price]) rfl
  · rw [pre_len]; simp only [chainSteps,k]; omega
  · rw [pre_price]; simp only [chainCycles,chainSteps,chainCalls,k]; omega
  · simp only [chainCalls,k]; omega

end TwoPermutationPrototype.GroupedOpening
