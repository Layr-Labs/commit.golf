import CommitGolfCandidate.NonceCompactHeader

/-! The record pass no longer calls the shared copy routine: each record is one
straight-line block (`NonceCompactTail`). Only the footer still calls the
routine. This module is kept as the import link between the header and the block. -/
namespace CommitGolfCandidate
end CommitGolfCandidate
