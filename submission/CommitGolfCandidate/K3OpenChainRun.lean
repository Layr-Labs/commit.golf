import CommitGolfCandidate.K3OpenChainLink

/-! Opener chain block (rows 777..795), execution: `chain_run`. Owner: S9-L2 (draft by S9-L2). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

theorem chain_run (h : MachineState) (i : Index) (e : ChainEntry h i) (fuel : Nat) :
    execute openingImage (chainSteps i+fuel) h true =
      (do let t ← chainTrace h i; let z ← execute openingImage fuel t true
          return z.charge (chainCycles i) (chainCalls i)) := by
  have lens := chain_lengths
  obtain ⟨preOk,bpc,_,b30,_,bkeep⟩ := chain_before h i e
  have breg (x : Reg) (a : x≠.x7) (b : x≠.x28) (c : x≠.x30) (d : x≠.x31) := bkeep x a b c d
  by_cases zero : chainLinks i=0
  · rw [show chainSteps i+fuel=chainPreRows.length+((chainSkipRows.length+fuel)+1) by
        simp only [chainSteps,zero,if_pos]; rw [lens.1,lens.2.2.1]; omega,
      walk_rows_run h chainPreRows preOk chain_pre_fetch _ true,
      show walkRows h chainPreRows=chainBefore h from rfl,
      execute_permutation_call openingImage _ (chainBefore h) true 128 192 (by decide) (by decide)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.input)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.output)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.selector)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.width)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.primitive) (keyed_fetch _ bpc)]
    simp only [chainTrace,zero,if_pos,bind_assoc,pure_bind]
    apply bind_congr; intro z
    obtain ⟨apc,_,a30,_⟩ := after_keyed h i e z
    obtain ⟨ok,_,_,_⟩ := skip_rows _ apc (by rw [a30,zero])
    rw [walk_rows_run _ chainSkipRows ok chain_skip_fetch _ true]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro y; apply congrArg pure
    simp [Execution.charge,chainCycles,chainCalls,chainSteps,zero,lens.2.1,lens.2.2.2.1]
    all_goals omega
  · obtain ⟨c,hc⟩ : ∃ c, chainLinks i=c+1 := ⟨chainLinks i-1,by omega⟩
    have lt := links_lt i
    rw [show chainSteps i+fuel=chainPreRows.length+((chainEnterRows.length+(3*(c+1)+(1+fuel)))+1) by
        simp only [chainSteps,zero,if_neg,not_false_eq_true]; rw [lens.1,lens.2.2.2.2.1,hc]; omega,
      walk_rows_run h chainPreRows preOk chain_pre_fetch _ true,
      show walkRows h chainPreRows=chainBefore h from rfl,
      execute_permutation_call openingImage _ (chainBefore h) true 128 192 (by decide) (by decide)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.input)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.output)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.selector)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.width)
        ((breg _ (by decide) (by decide) (by decide) (by decide)).trans e.primitive) (keyed_fetch _ bpc)]
    simp only [chainTrace,zero,if_neg,not_false_eq_true,bind_assoc,pure_bind,hc,Nat.add_one_ne_zero,if_false,
      ↓reduceIte]
    apply bind_congr; intro z
    obtain ⟨apc,akeep,a30,_⟩ := after_keyed h i e z
    obtain ⟨ok,epc,e10,ekeep,_⟩ := enter_rows _ c apc (by rw [a30,hc]) (by omega)
    rw [walk_rows_run _ chainEnterRows ok chain_enter_fetch _ true]
    have ready : LinkReady (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows) (c+1) :=
      ⟨epc,(ekeep _ (by decide)).trans (a30.trans (by rw [hc])),
        e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.output),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.selector),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.width),
        (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide)).trans e.primitive)⟩
    rw [link_run c _ ready (by omega) fuel]
    simp only [bind_assoc,pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro y; apply congrArg pure
    simp [Execution.charge,chainCycles,chainCalls,chainSteps,zero,hc,lens.2.1,lens.2.2.2.2.2.1]
    all_goals omega

end TwoPermutationPrototype.GroupedOpening
