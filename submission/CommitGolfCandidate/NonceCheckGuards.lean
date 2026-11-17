import CommitGolfCandidate.NonceCheckValidExit
import CommitGolfCandidate.NonceExpandReject

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
attribute [local irreducible] nonceExpandHeaderPrefix nonceExpandMinimumPrefix nonceExpandCapacityPrefix

def NonceCheckValid (input : CheckInput) : Prop :=
  input.proof.length%8=0 ∧ 536*input.positions.card ≤ input.proof.length ∧
    input.proof.length+8*input.positions.card ≤ 13421772800

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

theorem nonce_check_invalid_exit (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) (invalid : ¬NonceCheckValid input) :
    Execution.exit <$> nonceCompressedProgram.run .check input=pure .failure := by
  have lengthSmall : input.proof.length<2^64 := by
    have bounded : input.proof.length ≤ 13421772800 := admitted
    omega
  have cardinal : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have productSmall : 536*input.positions.card<2^64 := by norm_num [LENGTH,LOG_LENGTH] at cardinal; omega
  have expandedSmall : input.proof.length+8*input.positions.card<2^64 := by
    norm_num [LENGTH,LOG_LENGTH] at cardinal
    have bounded : input.proof.length ≤ 13421772800 := admitted
    omega
  rw [run_check nonceCompressedProgram input admitted]
  erw [nonce_compressed_initial_same .check input]
  change Execution.exit <$> execute nonceExpandedImage (2*capProgram.steps .check)
    (capProgram.initialState .check input) false=_
  have entry:=nonce_expand_entry_execute (capProgram.initialState .check input) rfl
  rw [show 2*capProgram.steps .check=1+(2*capProgram.steps .check-1) by decide,entry,exit_charge]
  by_cases aligned : input.proof.length%8=0
  · have headerPc : (nonceExpandHeaderPrefix (nonceCheckExpansionStart input) 4).pc=4912 := by
      simpa only [if_pos aligned] using nonce_expand_header_pc (nonceCheckExpansionStart input)
        rfl input.proof.length lengthSmall rfl
    have headerLength : (nonceExpandHeaderPrefix (nonceCheckExpansionStart input) 4).getReg .x17=
        BitVec.ofNat 64 input.proof.length :=
      (nonce_expand_header_register _ .x17 (by decide)).trans rfl
    have headerCount : (nonceExpandHeaderPrefix (nonceCheckExpansionStart input) 4).getReg .x16=
        BitVec.ofNat 64 input.positions.card :=
      (nonce_expand_header_register _ .x16 (by decide)).trans rfl
    rw [show 2*capProgram.steps .check-1=4+(2*capProgram.steps .check-5) by decide,
      nonce_expand_header_execute _ rfl _ false,exit_charge]
    by_cases enough : 536*input.positions.card ≤ input.proof.length
    · have minimumPc : (nonceExpandMinimumState (nonceCheckExpansionStart input)).pc=4932 := by
        simpa only [if_neg (by omega : ¬input.proof.length<536*input.positions.card)] using
          nonce_expand_minimum_pc _ headerPc input.proof.length input.positions.card lengthSmall productSmall headerLength headerCount
      have minimumLength : (nonceExpandMinimumState (nonceCheckExpansionStart input)).getReg .x17=
          BitVec.ofNat 64 input.proof.length :=
        (nonce_expand_minimum_register _ .x17 (by decide)).trans headerLength
      have minimumCount : (nonceExpandMinimumState (nonceCheckExpansionStart input)).getReg .x16=
          BitVec.ofNat 64 input.positions.card :=
        (nonce_expand_minimum_register _ .x16 (by decide)).trans headerCount
      have oversized : 13421772800 < input.proof.length+8*input.positions.card := by
        unfold NonceCheckValid at invalid
        omega
      rw [show 2*capProgram.steps .check-5=5+(2*capProgram.steps .check-10) by decide,
        nonce_expand_minimum_execute _ headerPc _ false,exit_charge,
        show 2*capProgram.steps .check-10=15+(2*capProgram.steps .check-25) by decide,
        nonce_expand_reject_capacity _ minimumPc input.proof.length input.positions.card expandedSmall
          minimumLength minimumCount oversized]
      rfl
    · rw [show 2*capProgram.steps .check-5=8+(2*capProgram.steps .check-13) by decide,
        nonce_expand_reject_short _ headerPc input.proof.length input.positions.card lengthSmall productSmall
          headerLength headerCount (by omega)]
      rfl
  · rw [show 2*capProgram.steps .check-1=7+(2*capProgram.steps .check-8) by decide,
      nonce_expand_reject_alignment _ rfl input.proof.length lengthSmall rfl aligned]
    rfl
end CommitGolfCandidate
