import CommitGolfCandidate.NonceCheckLoaderEquiv
import CommitGolfCandidate.NonceExpandEntry

/-! The actual compressed checker agrees in exit status with the retained
checker on a valid expanded input. The extra declared fuel pays for every
query-free expansion instruction before the ordinary checker tail resumes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

private theorem run_check (program : Submission) (input : CheckInput)
    (admitted : input.proof.length ≤ program.sizes.proof) :
    program.run .check input=execute (program.image .check) (program.steps .check)
      (program.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

private theorem exit_charge (computation : OracleComp World Execution) (cycles calls : Nat) :
    Execution.exit <$> (do let result ← computation; return result.charge cycles calls)=
      Execution.exit <$> computation := by
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Execution.charge]

theorem nonce_expand_valid_steps_bound (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    nonceExpandValidSteps input.positions.card input.proof.length ≤ capProgram.steps .check := by
  have cardinal : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have lengthBound : input.proof.length ≤ 13421772800 := admitted
  have footerBound : nonceExpandFooterWords input.positions.card input.proof.length ≤ 1677721600 := by
    dsimp only [nonceExpandFooterWords]; omega
  norm_num [LENGTH,LOG_LENGTH] at cardinal
  change nonceExpandValidSteps input.positions.card input.proof.length ≤ 214748365824
  unfold nonceExpandValidSteps nonceExpandFooterSteps
  split <;> omega

theorem nonce_check_valid_exit (input : CheckInput)
    (aligned : input.proof.length%8=0)
    (enough : 536*input.positions.card ≤ input.proof.length)
    (admitted : (nonceExpandedInput input).proof.length ≤ capProgram.sizes.proof) :
    Execution.exit <$> nonceCompressedProgram.run .check input=
      Execution.exit <$> capProgram.run .check (nonceExpandedInput input) := by
  have expandedLength:=nonce_expanded_input_length input enough
  have originalAdmitted : input.proof.length ≤ capProgram.sizes.proof := by omega
  have capacity : input.proof.length+8*input.positions.card ≤ 13421772800 := by
    rw [expandedLength] at admitted
    exact admitted
  have window : capProgram.layout.proof+input.proof.length+8*input.positions.card ≤ MEMORY_BYTES := by
    have loader:=(cap_check_loader_bounds (nonceExpandedInput input) admitted).1
    rw [expandedLength] at loader
    omega
  have cardinal : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have countSmall : input.positions.card<2^64 := by norm_num [LENGTH,LOG_LENGTH] at cardinal; omega
  have stepsBound:=nonce_expand_valid_steps_bound input originalAdmitted
  have core:=nonce_check_tail_exit (nonceExpandedInput input) admitted (nonceCheckExpansionEnd input)
    (nonce_check_loader_equiv input aligned enough admitted)
    (capProgram.steps .check-nonceExpandValidSteps input.positions.card input.proof.length)
  rw [run_check nonceCompressedProgram input originalAdmitted]
  erw [nonce_compressed_initial_same .check input]
  change Execution.exit <$> execute nonceExpandedImage (2*capProgram.steps .check)
      (capProgram.initialState .check input) false=_
  rw [show 2*capProgram.steps .check=1+(nonceExpandValidSteps input.positions.card input.proof.length+
      (capProgram.steps .check-1+(capProgram.steps .check-nonceExpandValidSteps input.positions.card input.proof.length))) by
      have positive : 0<capProgram.steps .check := by decide
      omega,
    nonce_expand_entry_execute _ rfl,
    nonce_expand_valid_execute (nonceCheckExpansionStart input) capProgram.layout.proof
      input.positions.card input.proof.length rfl (by decide) countSmall (by decide) aligned enough
      capacity window rfl rfl rfl]
  rw [exit_charge,exit_charge]
  exact core
end CommitGolfCandidate
