import CommitGolfCandidate.CapCheckRootDigest
import CommitGolfCandidate.CapCheckWordSuffix

/-! Actual final acceptance requires both decoder-word exhaustion and absence
of any partial byte tail. The root comparison uses the same two loaded
digests; no injectivity or collision-freedom assumption is used. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer capCheckProofEndState

theorem cap_check_codec_final (state : MachineState) (cursor : Nat)
    (words : List Digest) (tailBytes commitment : Nat)
    (suffix : CapCheckWordSuffix state cursor words tailBytes)
    (roots : state.getReg .x18=BitVec.ofNat 64 12288)
    (claimed : state.getReg .x26=BitVec.ofNat 64 commitment)
    (commitmentAligned : commitment%8=0) :
    (capCheckFinalResult state).exit=.success ↔
      words=[] ∧ tailBytes=0 ∧
        capReadRoot state 1=readBuffer state commitment 32 := by
  have nextRoots : (capCheckProofEndState state).getReg .x18=
      BitVec.ofNat 64 12288 := by
    rw [cap_check_proof_end_register]
    exact roots
  have nextClaim : (capCheckProofEndState state).getReg .x26=
      BitVec.ofNat 64 commitment := by
    rw [cap_check_proof_end_register]
    exact claimed
  have digest := cap_check_root_passed_digest (capCheckProofEndState state)
    12288 commitment nextRoots nextClaim (by decide) commitmentAligned
  rw [read_buffer_memory_congr _ _ (cap_check_proof_end_memory state) _ _,
    read_buffer_memory_congr _ _ (cap_check_proof_end_memory state) _ _] at digest
  rw [cap_check_final_success,
    cap_check_word_suffix_exhausted state cursor words tailBytes suffix,digest]
  change (words=[] ∧ tailBytes=0) ∧
      capReadRoot state 1=readBuffer state commitment 32 ↔ _
  exact and_assoc

end CommitGolfCandidate
