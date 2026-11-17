import CommitGolfCandidate.NonceExpandFlowReady

/-! Complete successful expansion control flow from the guard entry to the
retained checker tail. All calls, backward copies, outer branches and reset
instructions are executed in the concrete image; the prefix has no queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] nonceExpandHeaderPrefix nonceExpandMinimumPrefix
  nonceExpandCapacityPrefix nonceExpandFooterPrefix nonceBackwardReturned

def nonceExpandFooterSteps (words : Nat) : Nat := if words=0 then 1 else 6*words+3

abbrev nonceExpandRecordsEnd (state : MachineState) (count length : Nat) : MachineState :=
  capCountedRun nonceExpandRecordState count
    (nonceExpandRecordEntry (nonceExpandSetupState state) (nonceExpandFooterWords count length))

abbrev nonceExpandCoreState (state : MachineState) (count length : Nat) : MachineState :=
  nonceExpandFinishPrefix (nonceExpandRecordsEnd state count length) 12

def nonceExpandValidSteps (count length : Nat) : Nat :=
  28+nonceExpandFooterSteps (nonceExpandFooterWords count length)+412*count+12

private theorem copy_execute (source target count : Nat) (state : MachineState)
    (ready : NonceBackwardReady.Backward 5096 source target count count state) (fuel : Nat) :
    execute nonceExpandedImage (6*count+1+fuel) state false=
      (do let result ← execute nonceExpandedImage fuel (nonceBackwardReturned state count) false
          return result.charge (6*count+1) 0) := by
  unfold nonceBackwardReturned
  exact NonceCopyProcedure.expanded_copy_execute source target count state ready fuel false

private theorem charges (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0=result.charge (second+first) 0 := by
  simp only [Execution.charge,Nat.zero_add,Nat.add_assoc]

theorem nonce_expand_footer_flow_execute (state : MachineState) (base count length : Nat)
    (facts : NonceExpandSetupFacts base count length state) (baseStart : 8 ≤ base)
    (baseAligned : base%8=0) (aligned : length%8=0) (enough : 536*count ≤ length)
    (window : base+length+8*count ≤ MEMORY_BYTES) (fuel : Nat) :
    execute nonceExpandedImage (nonceExpandFooterSteps (nonceExpandFooterWords count length)+fuel)
      (nonceExpandSetupState state) false=
      (do let result ← execute nonceExpandedImage fuel
            (nonceExpandRecordEntry (nonceExpandSetupState state) (nonceExpandFooterWords count length)) false
          return result.charge (nonceExpandFooterSteps (nonceExpandFooterWords count length)) 0) := by
  by_cases empty : nonceExpandFooterWords count length=0
  · have pc : (nonceExpandSetupState state).pc=5012 := by simpa only [if_pos empty] using facts.pc
    simp only [nonceExpandFooterSteps,nonceExpandRecordEntry,nonceExpandAfterFooter,if_pos empty]
    exact nonce_expand_guard_execute _ pc fuel false
  · have pc : (nonceExpandSetupState state).pc=5008 := by simpa only [if_neg empty] using facts.pc
    have ready:=nonce_expand_footer_ready state base count length facts baseStart baseAligned aligned enough window (by omega)
    have returned:=nonce_expand_footer_return_pc (nonceExpandSetupState state) pc (nonceExpandFooterWords count length)
    simp only [nonceExpandFooterSteps,nonceExpandRecordEntry,nonceExpandAfterFooter,if_neg empty]
    rw [show 6*nonceExpandFooterWords count length+3+fuel=
        1+(6*nonceExpandFooterWords count length+1+(1+fuel)) by omega,
      nonce_expand_footer_call_execute _ pc (6*nonceExpandFooterWords count length+1+(1+fuel)) false,
      copy_execute (base+536*count) (base+544*count) (nonceExpandFooterWords count length) _ ready (1+fuel),
      nonce_expand_guard_execute _ returned fuel false]
    simp only [bind_assoc,pure_bind,charges]
    rw [show 1+(6*nonceExpandFooterWords count length+1+1)=6*nonceExpandFooterWords count length+3 by omega]

theorem nonce_expand_valid_execute (state : MachineState) (base count length : Nat)
    (pc : state.pc=4896) (baseStart : 8 ≤ base) (countSmall : count<2^64)
    (baseAligned : base%8=0) (aligned : length%8=0) (enough : 536*count ≤ length)
    (capacity : length+8*count ≤ 13421772800) (window : base+length+8*count ≤ MEMORY_BYTES)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base) (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) (fuel : Nat) :
    execute nonceExpandedImage (nonceExpandValidSteps count length+fuel) state false=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandCoreState state count length) false
          return result.charge (nonceExpandValidSteps count length+3) 0) := by
  have facts:=nonce_expand_setup_facts state base count length pc baseStart aligned enough capacity proofBase counter reported
  have ready:=nonce_expand_record_entry_ready state base count length facts baseStart countSmall baseAligned aligned enough window
  have finished:=nonce_expand_outer_finished base count count _ ready
  have records:=nonce_expand_outer_execute base count count _ ready (12+fuel) false
  change execute nonceExpandedImage (412*count+(12+fuel))
      (nonceExpandRecordEntry (nonceExpandSetupState state) (nonceExpandFooterWords count length)) false=
    (do let result ← execute nonceExpandedImage (12+fuel) (nonceExpandRecordsEnd state count length) false
        return result.charge (412*count) 0) at records
  rw [show nonceExpandValidSteps count length+fuel=
      28+(nonceExpandFooterSteps (nonceExpandFooterWords count length)+(412*count+(12+fuel))) by
        unfold nonceExpandValidSteps; omega,
    nonce_expand_setup_execute state base count length pc baseStart aligned enough capacity proofBase counter reported
      (nonceExpandFooterSteps (nonceExpandFooterWords count length)+(412*count+(12+fuel))) false,
    nonce_expand_footer_flow_execute state base count length facts baseStart baseAligned aligned enough window
      (412*count+(12+fuel)),records,nonce_expand_finish_execute _ finished.1 fuel false]
  simp only [bind_assoc,pure_bind,charges]
  rw [show 31+(nonceExpandFooterSteps (nonceExpandFooterWords count length)+(412*count+12))=
    nonceExpandValidSteps count length+3 by unfold nonceExpandValidSteps; omega]

end CommitGolfCandidate
