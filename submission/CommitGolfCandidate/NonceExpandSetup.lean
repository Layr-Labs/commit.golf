import CommitGolfCandidate.NonceExpandFooter

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] nonceExpandHeaderPrefix nonceExpandMinimumPrefix
  nonceExpandCapacityPrefix nonceExpandFooterPrefix

abbrev nonceExpandAlignedState (state : MachineState) := nonceExpandHeaderPrefix state 4
abbrev nonceExpandMinimumState (state : MachineState) := nonceExpandMinimumPrefix (nonceExpandAlignedState state) 5
abbrev nonceExpandCapacityState (state : MachineState) := nonceExpandCapacityPrefix (nonceExpandMinimumState state) 12
abbrev nonceExpandSetupState (state : MachineState) := nonceExpandFooterPrefix (nonceExpandCapacityState state) 7

def nonceExpandSetupClobbers : List Reg := [.x6,.x7,.x18,.x19,.x23,.x24,.x25,.x26,.x28,.x29]

theorem nonce_expand_setup_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ nonceExpandSetupClobbers) :
    (nonceExpandSetupState state).getReg reg=state.getReg reg := by
  have distinct : ∀ rd, rd ∈ nonceExpandSetupClobbers → reg ≠ rd := by
    intro rd member equal
    subst reg
    exact outside member
  rw [nonce_expand_footer_register _ reg ⟨distinct _ (by decide),distinct _ (by decide),distinct _ (by decide)⟩,
    nonce_expand_capacity_register _ reg ⟨distinct _ (by decide),distinct _ (by decide),distinct _ (by decide)⟩,
    nonce_expand_minimum_register _ reg ⟨distinct _ (by decide),distinct _ (by decide)⟩,
    nonce_expand_header_register _ reg ⟨distinct _ (by decide),distinct _ (by decide),distinct _ (by decide)⟩]

structure NonceExpandSetupFacts (base count length : Nat) (state : MachineState) : Prop where
  header_pc : (nonceExpandAlignedState state).pc=4912
  minimum_pc : (nonceExpandMinimumState state).pc=4932
  capacity_pc : (nonceExpandCapacityState state).pc=4980
  pc : (nonceExpandSetupState state).pc=if (length-536*count)/8=0 then 5012 else 5008
  memory : (nonceExpandSetupState state).mem=state.mem
  source : (nonceExpandSetupState state).getReg .x23=BitVec.ofNat 64 (base+length-8)
  target : (nonceExpandSetupState state).getReg .x25=BitVec.ofNat 64 (base+(length+8*count)-8)
  words : (nonceExpandSetupState state).getReg .x28=BitVec.ofNat 64 ((length-536*count)/8)
  counter : (nonceExpandSetupState state).getReg .x24=BitVec.ofNat 64 count
  root : (nonceExpandSetupState state).getReg .x26=state.getReg .x11
  expanded : (nonceExpandSetupState state).getReg .x18=BitVec.ofNat 64 (length+8*count)

theorem nonce_expand_setup_facts (state : MachineState) (base count length : Nat)
    (pc : state.pc=4896) (baseStart : 8 ≤ base) (aligned : length%8=0)
    (enough : 536*count ≤ length) (capacity : length+8*count ≤ 13421772800)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) : NonceExpandSetupFacts base count length state := by
  have lengthSmall : length<2^64 := by omega
  have productSmall : 536*count<2^64 := by omega
  have expandedSmall : length+8*count<2^64 := by omega
  have headerLength : (nonceExpandAlignedState state).getReg .x17=BitVec.ofNat 64 length :=
    (nonce_expand_header_register state .x17 (by decide)).trans reported
  have headerCount : (nonceExpandAlignedState state).getReg .x16=BitVec.ofNat 64 count :=
    (nonce_expand_header_register state .x16 (by decide)).trans counter
  have headerPc : (nonceExpandAlignedState state).pc=4912 := by
    simpa only [if_pos aligned] using nonce_expand_header_pc state pc length lengthSmall reported
  have minimumLength : (nonceExpandMinimumState state).getReg .x17=BitVec.ofNat 64 length :=
    (nonce_expand_minimum_register _ .x17 (by decide)).trans headerLength
  have minimumCount : (nonceExpandMinimumState state).getReg .x16=BitVec.ofNat 64 count :=
    (nonce_expand_minimum_register _ .x16 (by decide)).trans headerCount
  have minimumPc : (nonceExpandMinimumState state).pc=4932 := by
    simpa only [if_neg (by omega : ¬length<536*count)] using nonce_expand_minimum_pc
      (nonceExpandAlignedState state) headerPc length count lengthSmall productSmall headerLength headerCount
  have capacityLength : (nonceExpandCapacityState state).getReg .x17=BitVec.ofNat 64 length :=
    (nonce_expand_capacity_register _ .x17 (by decide)).trans minimumLength
  have capacityBase : (nonceExpandCapacityState state).getReg .x15=BitVec.ofNat 64 base := by
    rw [nonce_expand_capacity_register _ .x15 (by decide),nonce_expand_minimum_register _ .x15 (by decide),
      nonce_expand_header_register _ .x15 (by decide)]
    exact proofBase
  have capacityMinimum : (nonceExpandCapacityState state).getReg .x6=BitVec.ofNat 64 (536*count) :=
    (nonce_expand_capacity_register _ .x6 (by decide)).trans
      (nonce_expand_minimum_product _ count headerCount)
  have capacityExpanded : (nonceExpandCapacityState state).getReg .x18=BitVec.ofNat 64 (length+8*count) :=
    nonce_expand_capacity_length _ length count minimumLength minimumCount
  have capacityPc : (nonceExpandCapacityState state).pc=4980 := by
    simpa only [if_neg (by omega : ¬13421772800<length+8*count)] using nonce_expand_capacity_pc
      (nonceExpandMinimumState state) minimumPc length count expandedSmall minimumLength minimumCount
  refine {
    header_pc := headerPc
    minimum_pc := minimumPc
    capacity_pc := capacityPc
    pc := nonce_expand_footer_pc _ capacityPc length (536*count) lengthSmall enough capacityLength capacityMinimum
    memory := ?_
    source := nonce_expand_footer_source _ base length baseStart capacityBase capacityLength
    target := nonce_expand_footer_target _ base (length+8*count) baseStart capacityBase capacityExpanded
    words := nonce_expand_footer_count _ length (536*count) lengthSmall enough capacityLength capacityMinimum
    counter := ?_
    root := ?_
    expanded := ?_ }

  · rw [nonce_expand_footer_memory,nonce_expand_capacity_memory,nonce_expand_minimum_memory,nonce_expand_header_memory]
  · rw [nonce_expand_footer_register _ .x24 (by decide),nonce_expand_capacity_register _ .x24 (by decide),
      nonce_expand_minimum_register _ .x24 (by decide)]
    exact (nonce_expand_header_saved state).2.trans counter
  · rw [nonce_expand_footer_register _ .x26 (by decide),nonce_expand_capacity_register _ .x26 (by decide),
      nonce_expand_minimum_register _ .x26 (by decide)]
    exact (nonce_expand_header_saved state).1
  · rw [nonce_expand_footer_register _ .x18 (by decide)]
    exact capacityExpanded

private theorem charges (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0=result.charge (second+first) 0 := by
  simp only [Execution.charge,Nat.zero_add,Nat.add_assoc]

theorem nonce_expand_setup_execute (state : MachineState) (base count length : Nat)
    (pc : state.pc=4896) (baseStart : 8 ≤ base) (aligned : length%8=0)
    (enough : 536*count ≤ length) (capacity : length+8*count ≤ 13421772800)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (28+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandSetupState state) coins
          return result.charge 31 0) := by
  have facts:=nonce_expand_setup_facts state base count length pc baseStart aligned enough capacity proofBase counter reported
  rw [show 28+fuel=4+(5+(12+(7+fuel))) by omega,
    nonce_expand_header_execute state pc (5+(12+(7+fuel))) coins,
    nonce_expand_minimum_execute _ facts.header_pc (12+(7+fuel)) coins,
    nonce_expand_capacity_execute _ facts.minimum_pc (7+fuel) coins,
    nonce_expand_footer_execute _ facts.capacity_pc fuel coins]
  simp only [bind_assoc,pure_bind,charges]

end CommitGolfCandidate
