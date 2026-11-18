import CommitGolfCandidate.S6Model
import CommitGolfCandidate.CapHeapView

/-! The cap-level opening proof of the committed tree as a pure function, and the public transcript.
A record (18 digests, 576 bytes) holds the salt, the three other leaf digests of the leaf's group and the
14 siblings of the group node; the records of the positions come in increasing position order and are followed
by the cap footer, the cap nodes that the records do not determine, in the order of the cap codec. -/
namespace CommitGolfCandidate
open CommitGolf

/-- The 18 digests of the opening record of `index`. -/
def s6OpeningRecord (heap leaf : Nat → Digest) (salt : Index → Digest) (index : Index) : List Digest :=
  salt index :: (List.ofFn fun k : Fin 3 => leaf (s6OtherLeaf index.val k.val)) ++
    List.ofFn (s6Sibling heap index.val)

/-- Cap leaf `node` (heap nodes 256 .. 511) is marked iff an opened position lies below it. -/
def s6CapMarks (positions : Positions) (node : Nat) : Bool :=
  decide (∃ index ∈ positions, 256+index.val/2^16 = node)

/-- The cap footer for the node compression `compress` (the tree's is `s6Compress oracle.compression`). -/
def s6CapFooter (compress : Compression) (heap : Nat → Digest) (positions : Positions) : List Digest :=
  capProof compress (capHeapTree heap 8 1) (capHeapView heap (s6CapMarks positions) 8 1)

/-- The records of the positions, in increasing position order, as little-endian bytes (576 per record). -/
def referenceOpening (heap leaf : Nat → Digest) (salt : Index → Digest) (positions : Positions) : Proof :=
  ((positions.sort (· ≤ ·)).flatMap (s6OpeningRecord heap leaf salt)).flatMap digestBytes

/-- The public transcript as a function of the group digests and the leaf digests: the root of the heap over
`groups`, and the cap-level proof (empty for no positions; else the records, then the footer). -/
def s6TranscriptOf (compress : Compression) (groups leaf : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : Commitment × Proof :=
  let heap := referenceHeap (s6Compress compress) (2^22) groups
  (heap 1, if positions.card = 0 then [] else
    referenceOpening heap leaf salt positions ++
      (s6CapFooter (s6Compress compress) heap positions).flatMap digestBytes)

/-- Public transcript of the committed tree for one salt vector: commitment `s6Heap .. 1` and the cap-level
proof. -/
def referenceTranscript (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (positions : Positions) : Commitment × Proof :=
  s6TranscriptOf compress (s6GroupValues permutation (s6LeafValues permutation message salt))
    (s6LeafValues permutation message salt) salt positions

theorem reference_transcript_root (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (positions : Positions) :
    (referenceTranscript compress permutation message salt positions).1 =
      s6Heap compress permutation message salt 1 := rfl

theorem reference_transcript_proof (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (positions : Positions) :
    (referenceTranscript compress permutation message salt positions).2 =
      if positions.card = 0 then [] else
        referenceOpening (s6Heap compress permutation message salt)
            (s6LeafValues permutation message salt) salt positions ++
          (s6CapFooter (s6Compress compress) (s6Heap compress permutation message salt) positions).flatMap
            digestBytes := rfl

theorem s6_opening_record_length (heap leaf : Nat → Digest) (salt : Index → Digest) (index : Index) :
    (s6OpeningRecord heap leaf salt index).length = 18 := by
  simp [s6OpeningRecord]

theorem s6_digest_bytes_length (digests : List Digest) :
    (digests.flatMap digestBytes).length = 32*digests.length := by
  induction digests with
  | nil => rfl
  | cons digest rest ih =>
      simp only [List.flatMap_cons, List.length_append, digestBytes_length, ih, List.length_cons]
      omega

theorem reference_opening_length (heap leaf : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) : (referenceOpening heap leaf salt positions).length = 576*positions.card := by
  have records : ∀ indices : List Index,
      ((indices.flatMap (s6OpeningRecord heap leaf salt)).flatMap digestBytes).length = 576*indices.length := by
    intro indices
    induction indices with
    | nil => simp
    | cons index rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append, List.length_append, List.length_cons] at ih ⊢
        rw [ih]
        have one : ((s6OpeningRecord heap leaf salt index).flatMap digestBytes).length = 576 := by
          rw [s6_digest_bytes_length, s6_opening_record_length]
        omega
  rw [referenceOpening, records, Finset.length_sort]

/-- The opening depends on the salts at the opened positions only. -/
theorem reference_opening_salt_congr (heap leaf : Nat → Digest) (salt salt' : Index → Digest)
    (positions : Positions) (agree : ∀ index ∈ positions, salt index = salt' index) :
    referenceOpening heap leaf salt positions = referenceOpening heap leaf salt' positions := by
  unfold referenceOpening
  congr 1
  apply List.flatMap_congr
  intro index member
  have opened : index ∈ positions := (Finset.mem_sort _).mp member
  simp only [s6OpeningRecord, agree index opened]

/-- The transcript depends on the salts at the opened positions only. -/
theorem s6_transcript_of_salt_congr (compress : Compression) (groups leaf : Nat → Digest)
    (salt salt' : Index → Digest) (positions : Positions)
    (agree : ∀ index ∈ positions, salt index = salt' index) :
    s6TranscriptOf compress groups leaf salt positions = s6TranscriptOf compress groups leaf salt' positions := by
  simp only [s6TranscriptOf]
  rw [reference_opening_salt_congr _ _ salt salt' positions agree]

/-- The cap view reads the marks of the leaves below its node only. -/
theorem cap_heap_view_marks_congr (roots : Nat → Digest) (marked marked' : Nat → Bool)
    (height node : Nat)
    (agree : ∀ leaf, node*2^height ≤ leaf → leaf < (node+1)*2^height → marked leaf = marked' leaf) :
    capHeapView roots marked height node = capHeapView roots marked' height node := by
  induction height generalizing node with
  | zero =>
      simp only [capHeapView, agree node (by simp) (by simp)]
  | succ height ih =>
      simp only [capHeapView]
      have power : 2^(height+1) = 2*2^height := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [ih (2*node) ?_, ih (2*node+1) ?_]
      · intro leaf lower upper
        apply agree leaf
        · rw [power]; nlinarith
        · rw [power]; nlinarith
      · intro leaf lower upper
        apply agree leaf
        · rw [power]; nlinarith
        · rw [power]; nlinarith

/-- The footer is the same for every marking that agrees with `s6CapMarks` on the cap leaves. -/
theorem s6_cap_footer_marks (compress : Compression) (heap : Nat → Digest) (positions : Positions)
    (marked : Nat → Bool)
    (agree : ∀ node, 256 ≤ node → node < 512 → marked node = s6CapMarks positions node) :
    capProof compress (capHeapTree heap 8 1) (capHeapView heap marked 8 1) =
      s6CapFooter compress heap positions := by
  rw [s6CapFooter, cap_heap_view_marks_congr heap marked (s6CapMarks positions) 8 1
    (fun leaf lower upper => agree leaf (by simpa using lower) (by simpa using upper))]

end CommitGolfCandidate
