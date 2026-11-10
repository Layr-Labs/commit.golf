import CommitGolfCandidate.CapLowerDomain
import CommitGolfCandidate.CapHeapCodec

/-! Duplicate-checked honest lower roots populate exactly the same cap view
used by the machine opening. Occupancy comes from the supplied request set;
known payloads come from the commitment heap agreement invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 200000

theorem cap_requested_leaf_domain (positions : Positions) (group : Nat) :
    capOpenRequestedMarks positions (128+group) = true ↔
      ∃ index ∈ positions, (capGroup index).val = group := by
  rw [capOpenRequestedMarks, cap_tree_marks_leaf _ _ (by omega)]
  have count : positions.card = (capOpenRequestedIndices positions).length := by
    simp only [capOpenRequestedIndices, Finset.length_sort]
  rw [count, cap_open_marks_seen_full]
  simp only [capOpenRequestedIndices, Finset.mem_sort]
  constructor
  · rintro ⟨index, member, equal⟩
    exact ⟨index, member, by omega⟩
  · rintro ⟨index, member, equal⟩
    exact ⟨index, member, by omega⟩

theorem cap_honest_roots_lookup (oracle : Oracle) (message : Message)
    (committed : MachineState) (positions : Positions) (roots : CapRootMap)
    (accepted : capLowerBatchRoots oracle.compression
      (capHonestLowerRecords message committed positions) (fun _ => none) = some roots)
    (agree : CapRootsAgree (fun group => heapDigest committed 4294971424 (128+group)) roots)
    (group : Nat) :
    roots group = if capOpenRequestedMarks positions (128+group) then
      some (heapDigest committed 4294971424 (128+group)) else none := by
  have domain := cap_honest_lower_domain oracle message committed positions roots accepted group
  have marked := cap_requested_leaf_domain positions group
  cases known : roots group with
  | none =>
      have absent : capOpenRequestedMarks positions (128+group) = false := by
        cases value : capOpenRequestedMarks positions (128+group)
        · rfl
        · have occupied := domain.mpr (marked.mp value)
          simp only [known, Option.isSome_none, Bool.false_eq_true] at occupied
      simp only [absent, Bool.false_eq_true, ite_false]
  | some value =>
      have present := marked.mpr (domain.mp (by simp [known]))
      have correct := agree group value known
      simp only [present, ite_true, known, correct]

private theorem view_shape (heap : Nat → Digest) (marked : Nat → Bool)
    (height node offset : Nat) (index : node*2^height = 128+offset) :
    capKnownView (fun group => if marked (128+group) then some (heap (128+group)) else none)
      height offset = capHeapView heap marked height node := by
  induction height generalizing node offset with
  | zero =>
      have same : node = 128+offset := by simpa only [Nat.pow_zero, Nat.mul_one] using index
      simp only [capKnownView, capHeapView, same]
  | succ height ih =>
      simp only [capKnownView, capHeapView]
      congr 1
      · apply ih (2*node) offset
        rw [Nat.pow_succ] at index
        nlinarith
      · apply ih (2*node+1) (offset+2^height)
        rw [Nat.pow_succ] at index
        nlinarith

theorem cap_honest_known_view (oracle : Oracle) (message : Message)
    (committed : MachineState) (positions : Positions) (roots : CapRootMap)
    (accepted : capLowerBatchRoots oracle.compression
      (capHonestLowerRecords message committed positions) (fun _ => none) = some roots)
    (agree : CapRootsAgree (fun group => heapDigest committed 4294971424 (128+group)) roots) :
    capKnownView roots 7 0 =
      capHeapView (heapDigest committed 4294971424) (capOpenRequestedMarks positions) 7 1 := by
  have lookup : roots = fun group => if capOpenRequestedMarks positions (128+group) then
      some (heapDigest committed 4294971424 (128+group)) else none := by
    funext group
    exact cap_honest_roots_lookup oracle message committed positions roots accepted agree group
  rw [lookup]
  exact view_shape _ _ 7 1 0 (by decide)

end CommitGolfCandidate
