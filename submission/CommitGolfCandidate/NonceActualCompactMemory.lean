import CommitGolfCandidate.NonceOpeningResult
import CommitGolfCandidate.NonceCompactFullMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_compact_complete_memory (state : MachineState) (base count words : Nat)
    (pc : state.pc=4540) (small : count<2^64)
    (window : base+544*count+8*words ≤ MEMORY_BYTES) (aligned : base%8=0)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (oldEnd : state.getReg .x25=BitVec.ofNat 64 (base+544*count+8*words)) :
    NonceFullCompactMemory base count words state (nonceCodecFinalState state count words) := by
  have ready:=nonce_compact_entry_ready base count state pc small (by omega) aligned proofBase counter
  have initial : NonceCompactPrefixMemory base count count state (nonceCompactEntryState state) := by
    constructor
    · intro index inside
      omega
    · intro location _
      exact congrArg (fun memory : Word → Word => memory location) (nonce_compact_entry_memory state)
  have recordsFrame : NonceCompactPrefixMemory base count 0 state (nonceCompactRecordsEnd state count) :=
    nonce_compact_outer_memory base count count (nonceCompactEntryState state) ready state initial
  have footerMove : NonceWordMove (base+544*count) (base+536*count) words
      (nonceCompactRecordsEnd state count) (nonceCodecFinalState state count words) := by
    by_cases empty : words=0
    · have memory : (nonceCodecFinalState state count words).mem=(nonceCompactRecordsEnd state count).mem := by
        rw [nonceCodecFinalState, if_pos empty, nonce_compact_exit_memory, nonce_compact_footer_memory]
      constructor
      · intro index inside
        omega
      · intro location _
        exact congrArg (fun memory : Word → Word => memory location) memory
    · have footerReady:=nonce_compact_footer_ready state base count words pc small (by omega)
        window aligned proofBase counter oldEnd
      have moved:=nonce_copy_returned_memory (base+544*count) (base+536*count) words _ footerReady
      have first : (nonceCompactFooterCall
          (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3)).mem=
          (nonceCompactRecordsEnd state count).mem := by
        rw [nonce_compact_footer_call_memory, nonce_compact_footer_memory]
      have last : (nonceCopyReturned (nonceCompactFooterCall
          (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3)) words).mem=
          (nonceCodecFinalState state count words).mem := by
        rw [nonceCodecFinalState, if_neg empty, nonce_compact_exit_memory]
      exact nonce_word_move_transfer _ _ words _ _ (nonceCompactRecordsEnd state count)
        (nonceCodecFinalState state count words) moved first last
  exact nonce_compact_prefix_footer_memory base count words state _ _ window recordsFrame footerMove

end CommitGolfCandidate
