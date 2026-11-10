import CommitGolfCandidate.FastOpeningCertificate
/-! Actual compact-format images: the opening skips nonce padding, and the checker reconstructs its zero fourth word. Commitment and ABI are inherited exactly. -/
namespace CommitGolfCandidate.Compact
open CommitGolf

def openingImage : Riscv.Image :=
  { CommitGolfCandidate.submission.image .opening with code :=
    (CommitGolfCandidate.submission.image .opening).code.set 32 25988243 }

def checkImage : Riscv.Image :=
  let code := (CommitGolfCandidate.submission.image .check).code
  ⟨((code.set 7 (792*2^20+6*2^15+6*2^7+19)).set 21 787).set 23 25988243, []⟩

def submission : Submission :=
  { CommitGolfCandidate.submission with image := fun program => match program with
    | .opening => openingImage
    | .check => checkImage
    | program => CommitGolfCandidate.submission.image program }
end CommitGolfCandidate.Compact
