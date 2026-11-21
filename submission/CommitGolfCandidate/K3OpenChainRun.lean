import CommitGolfCandidate.K3OpenChainLink

/-! Opener chain block (rows 777..788 and the link block 896..929), execution: `chain_run`. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option pp.deepTerms false

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

theorem chain_run (h : MachineState) (i : Index) (e : ChainEntry h i) (fuel : Nat) :
    execute openingImage (chainSteps i+fuel) h true =
      (do let t ← chainTrace h i; let z ← execute openingImage fuel t true
          return z.charge (chainCycles i) (chainCalls i)) := by
  have lens := chain_lengths
  have lt := links_lt i
  obtain ⟨preOk,bpc,_,_,_,_,bkeep⟩ := chain_before h i e
  have breg (x : Reg) (a : x≠.x3) (b : x≠.x7) (c : x≠.x28) (d : x≠.x30) (f : x≠.x31) := bkeep x a b c d f
  rw [show chainSteps i+fuel=chainPreRows.length+((chainEnterRows.length+(chainLinks i+(1+fuel)))+1) by
      unfold chainSteps; rw [lens.1,lens.2.2.1]; omega,
    walk_rows_run h chainPreRows preOk chain_pre_fetch _ true,
    show walkRows h chainPreRows=chainBefore h from rfl,
    execute_permutation_call openingImage _ (chainBefore h) true 128 192 (by decide) (by decide)
      ((breg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.input)
      ((breg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output)
      ((breg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.selector)
      ((breg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.width)
      ((breg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.primitive) (keyed_fetch _ bpc)]
  simp only [chainTrace,bind_assoc,pure_bind]
  apply bind_congr; intro z
  obtain ⟨apc,akeep,_,a7,_⟩ := after_keyed h i e z
  obtain ⟨ok,epc,e10,ekeep,_⟩ := enter_rows _ (chainLinks i) apc (by rw [a7,tab_t_links]) lt
  rw [walk_rows_run _ chainEnterRows ok chain_enter_fetch _ true]
  have ready : LinkReady (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows) (chainLinks i) :=
    ⟨epc,e10.trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.output),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.selector),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.width),
      (ekeep _ (by decide)).trans ((akeep _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans e.primitive)⟩
  rw [link_run _ _ ready lt fuel]
  simp only [bind_assoc,pure_bind]
  apply bind_congr; intro t
  apply bind_congr; intro y; apply congrArg pure
  simp [Execution.charge,chainCycles,chainCalls,chainSteps,lens.2.1,lens.2.2.2.1]
  all_goals omega

end TwoPermutationPrototype.GroupedOpening
