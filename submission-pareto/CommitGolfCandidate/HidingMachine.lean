import CommitGolfCandidate.S3HidingTransfer
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Identify the commitment and every transmitted proof byte with the salted
reference tree (stage-3 leaves, compression parents). This removes machine
memory from the remaining privacy argument, without replacing the
machine-derived scheme being certified. The reference opening itself is
`referenceOpening` of `S3HidingBase`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The commit refinement's state predicate gives the transfer's facts. -/
theorem committed_state_transfer (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state) :
    S3Committed oracle message state :=
  ⟨correct.1, correct.2.1, correct.2.2⟩

/-- The heap constructed by the machine is the unique reference heap for its
message and retained salts, on every used slot. -/
theorem committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index)
    (node : Nat) (positive : 0 < node) (inside : node < 2*LENGTH) :
    heapDigest state 4294971424 node =
      saltedHeap oracle.compression oracle.permutation message salt node :=
  s3_committed_heap_reference oracle message state
    (committed_state_transfer oracle message state correct) salt salts node positive inside

theorem committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index) :
    readBuffer state submission.layout.commitment 32 =
      saltedHeap oracle.compression oracle.permutation message salt 1 :=
  s3_committed_root_reference oracle message state
    (committed_state_transfer oracle message state correct) salt salts

theorem opening_reference_digest (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index)
    (positions : Positions) (ordinal part : Nat)
    (present : ordinal < positions.card) (inside : part < 25) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state
      (submission.layout.proof+800*ordinal+32*part) 32 =
    referenceOpeningDigest (saltedHeap oracle.compression oracle.permutation message salt)
      salt positions ordinal part :=
  s3_opening_reference_digest oracle message state
    (committed_state_transfer oracle message state correct) salt salts positions ordinal part
    present inside

/-- All bytes emitted by the actual opening image equal the reference proof.
The proof covers arbitrary opening sets, including the empty set. -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (saltedHeap oracle.compression oracle.permutation message salt)
        salt positions :=
  s3_opening_reference_bytes oracle message state
    (committed_state_transfer oracle message state correct) salt salts positions

end CommitGolfCandidate
