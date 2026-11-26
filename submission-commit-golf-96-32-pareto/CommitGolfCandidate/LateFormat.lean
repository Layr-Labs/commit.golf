import CommitGolfCandidate.LateModel

namespace CommitGolfCandidate.Late
open CommitGolf

theorem record_size (t : Levels) (s : SaltTape) (d : Nat) (i : Index) :
    (record t s d i).length = 24 + 32*d := by
  simp [record, bytes, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  omega

theorem wide_size (t : Levels) (s : SaltTape) (p : Positions) :
    (wideOpening t s p).length = if p.card = BATCH then 72704 else 792*p.card := by
  unfold wideOpening
  split
  · rename_i batch
    simp [List.length_flatMap, record_size, bytes, List.sum_replicate, batch, BATCH]
  · simp [List.length_flatMap, record_size, List.sum_replicate, LOG_LENGTH, Nat.mul_comm]

theorem opening_size (t : Levels) (s : SaltTape) (p : Positions) :
    (opening t s p).length=if p.card=BATCH then 69120 else 792*p.card := by
  by_cases b:p.card=BATCH <;> simp [opening,b,wide_size]

end CommitGolfCandidate.Late
