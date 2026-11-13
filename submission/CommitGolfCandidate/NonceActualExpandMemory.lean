import CommitGolfCandidate.NonceExpandFlow
import CommitGolfCandidate.NonceExpandFullMemory

/-! Full concrete expansion memory effect, including the query-free setup,
optional backward footer copy, records and register-restoration epilogue. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_expand_complete_memory (state : MachineState) (base count length : Nat)
    (pc : state.pc=4896) (baseStart : 8 ≤ base) (countSmall : count<2^64)
    (baseAligned : base%8=0) (aligned : length%8=0) (enough : 536*count ≤ length)
    (capacity : length+8*count ≤ 13421772800) (window : base+length+8*count ≤ MEMORY_BYTES)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (reported : state.getReg .x17=BitVec.ofNat 64 length) :
    NonceFullExpandMemory base count (nonceExpandFooterWords count length)
      state (nonceExpandCoreState state count length) := by
  let words:=nonceExpandFooterWords count length
  let entry:=nonceExpandRecordEntry (nonceExpandSetupState state) words
  have facts:=nonce_expand_setup_facts state base count length pc baseStart aligned enough capacity proofBase counter reported
  have ready:=nonce_expand_record_entry_ready state base count length facts baseStart countSmall baseAligned aligned enough window
  have initial:=nonce_expand_suffix_initial base count entry
  have recordsFrame:=nonce_expand_outer_memory base count count entry ready entry initial
  have footer : NonceWordMove (base+536*count) (base+544*count) words state entry := by
    by_cases empty : words=0
    · have memory : entry.mem=state.mem := by
        dsimp only [entry,nonceExpandRecordEntry]
        rw [nonce_expand_guard_memory,nonceExpandAfterFooter,if_pos empty]
        exact facts.memory
      constructor
      · intro index inside; omega
      · intro location _
        exact congrArg (fun memory : Word → Word => memory location) memory
    · have footerReady:=nonce_expand_footer_ready state base count length facts baseStart baseAligned aligned enough window (by omega)
      have moved:=nonce_backward_returned_memory (base+536*count) (base+544*count) words _ footerReady
      have first : (nonceExpandFooterCall (nonceExpandSetupState state)).mem=state.mem := by
        rw [nonce_expand_footer_call_memory,facts.memory]
      have last : (nonceBackwardReturned (nonceExpandFooterCall (nonceExpandSetupState state)) words).mem=entry.mem := by
        dsimp only [entry,nonceExpandRecordEntry]
        rw [nonce_expand_guard_memory,nonceExpandAfterFooter,if_neg empty]
      exact nonce_word_move_transfer _ _ words _ _ state entry moved first last
  have lengthEq : length=536*count+8*words := by dsimp only [words,nonceExpandFooterWords]; omega
  have composed:=nonce_expand_footer_records_memory base count words state entry
    (capCountedRun nonceExpandRecordState count entry) (by omega) footer recordsFrame
  have memory : (nonceExpandCoreState state count length).mem=
      (capCountedRun nonceExpandRecordState count entry).mem := nonce_expand_finish_memory _
  constructor
  · intro index inside
    simpa only [MachineState.getMem,memory] using composed.copied index inside
  · intro location outside
    simpa only [MachineState.getMem,memory] using composed.frame location outside
end CommitGolfCandidate
