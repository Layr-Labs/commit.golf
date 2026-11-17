import CommitGolfCandidate.NonceLoaderFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_expanded_loader_frame (input : CheckInput)
    (aligned : input.proof.length%8=0)
    (enough : 536*input.positions.card ≤ input.proof.length)
    (location : Nat) (locationAligned : location%8=0) (bounded : location<2^64)
    (outside : location<capProgram.layout.proof ∨
      capProgram.layout.proof+(nonceExpandedInput input).proof.length ≤ location) :
    (capProgram.initialState .check (nonceExpandedInput input)).getMem (BitVec.ofNat 64 location)=
      (capProgram.initialState .check input).getMem (BitVec.ofNat 64 location) := by
  have lengthExpanded:=nonce_expanded_input_length input enough
  have baseAligned : capProgram.layout.proof%8=0 := by decide
  have expandedAligned : (nonceExpandedInput input).proof.length%8=0 := by omega
  apply nonce_loader_word_frame capProgram input (nonceExpandedInput input).proof location bounded
  · intro byte bound
    rw [lengthExpanded] at outside
    omega
  · intro byte bound
    omega
end CommitGolfCandidate
