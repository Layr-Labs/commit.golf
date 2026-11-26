import CommitGolfCandidate.ReconstructedCheckLaunchGate
import CommitGolfCandidate.ReconstructedCheckLoader
import CommitGolfCandidate.ReconstructedCapSchedule

namespace CommitGolfCandidate.Reconstruction.CheckHonestAdmission
open CommitGolf TwoPermutationPrototype.Sampling Encoding

/-- Every honest encoding satisfies the checker's byte limit, word alignment and
per-position minimum, including the two extreme cardinalities. -/
theorem wire (ps : Positions) (tree : Encoding.Tree) (salts : OpenedSalts ps) :
    let n:=(Wire.bytes (fields tree ps salts)).length
    n≤8355061248 ∧ n%8=0 ∧ CheckLaunchGate.minimum ps.card≤n := by
  have card:=CheckLoader.positions_card_bound ps
  have high:=HonestHeap.cursor_all (ps.sort (·≤·))
  have len: (ps.sort (·≤·)).length=ps.card:=Finset.length_sort _
  change Frontier.cursor (ps.sort (·≤·))≤3633*(ps.sort (·≤·)).length+119472 at high
  rw [len] at high
  have low : 3633*ps.card≤Wire.bits (fields tree ps salts):=by
    unfold fields
    rw [Wire.bits_append,Wire.flat_bits _ _ 3633 (fun x=>record_bits ..),len]
    omega
  rw [Encoding.all_bits] at low
  dsimp only
  rw [Wire.byte_count,Encoding.all_bits]
  unfold alignedBytes CheckLaunchGate.minimum
  omega

end CommitGolfCandidate.Reconstruction.CheckHonestAdmission
