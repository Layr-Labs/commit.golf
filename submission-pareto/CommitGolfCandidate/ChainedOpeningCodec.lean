import CommitGolfCandidate.ChainedSplitCodec
import CommitGolfCandidate.ChainedCodecGeometry

/-! Exact record/footer codec for the chained layout, with strict length and padding checks. -/
namespace CommitGolfCandidate.Chained.InteriorCodec
open CommitGolf
open SplitCodec

def recordSpec : Spec :=
  (120,1)::(232,6)::List.ofFn (fun h : Fin 15 => (232,width ⟨h.val,by omega⟩-232))

abbrev Record := Payload recordSpec

theorem record_counts : lowCount recordSpec = 3832 ∧ highCount recordSpec = 24 := by decide +kernel

theorem encode_record_length (record : Record) : (encode record).length = 482 := by
  simpa only [record_counts.1,record_counts.2] using encode_length record

theorem record_roundtrip (record : Record) : unpack recordSpec (encode record) = some record :=
  unpack_encode record

theorem record_missing : unpack recordSpec [] = none := by
  apply unpack_bad_length
  rw [record_counts.1,record_counts.2]
  decide

def footerSpec (nodes : List Nat) : Spec := nodes.map fun node => (232,footerWidth node-232)

theorem footer_spec_bits (nodes : List Nat) :
    lowCount (footerSpec nodes)+highCount (footerSpec nodes) = footerBits nodes := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    have lower : 232 ≤ footerWidth node := by unfold footerWidth; split <;> decide
    change (232+lowCount (footerSpec nodes))+((footerWidth node-232)+highCount (footerSpec nodes)) =
      footerWidth node+footerBits nodes
    omega

theorem encode_footer_length (nodes : List Nat) (footer : Payload (footerSpec nodes)) :
    (encode footer).length = (footerBits nodes+7)/8 := by
  simpa only [footer_spec_bits] using encode_length footer

theorem records_length (records : List Record) : (records.flatMap encode).length = 482*records.length := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    simp only [List.flatMap_cons,List.length_append,encode_record_length,List.length_cons,ih]
    omega

abbrev Footer (positions : Positions) := Payload (footerSpec (footerNodes positions))

def encodeOpening (positions : Positions) (records : List Record) (footer : Footer positions) : Proof :=
  records.flatMap encode ++ encode footer

theorem encode_opening_length (positions : Positions) (records : List Record) (footer : Footer positions)
    (count : records.length = positions.card) : (encodeOpening positions records footer).length = proofLength positions := by
  simp only [encodeOpening,List.length_append,records_length,encode_footer_length,count,proofLength]

theorem encoded_size (positions : Positions) (records : List Record) (footer : Footer positions)
    (count : records.length = positions.card) (scored : positions.card ≤ 128) :
    (encodeOpening positions records footer).length ≤ 65472 := by
  rw [encode_opening_length positions records footer count]
  exact proof_length_bound positions scored

def readRecords : Nat → Proof → Option (List Record × Proof)
  | 0,proof => some ([],proof)
  | count+1,proof => do
    let head ← unpack recordSpec (proof.take 482)
    let rest ← readRecords count (proof.drop 482)
    return (head::rest.1,rest.2)

theorem read_encoded_records (records : List Record) (suffix : Proof) :
    readRecords records.length (records.flatMap encode ++ suffix) = some (records,suffix) := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readRecords]
    rw [List.take_left' (encode_record_length record),List.drop_left' (encode_record_length record),unpack_encode]
    simp only [ih]
    rfl

theorem read_records_accepted (count : Nat) (proof : Proof) (records : List Record) (suffix : Proof)
    (accepted : readRecords count proof = some (records,suffix)) :
    records.length = count ∧ records.flatMap encode ++ suffix = proof := by
  induction count generalizing proof records suffix with
  | zero =>
    have same : [] = records ∧ proof = suffix := Prod.mk.inj (Option.some.inj accepted)
    rcases same with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl⟩
  | succ count ih =>
    change ((unpack recordSpec (proof.take 482)).bind fun head =>
      (readRecords count (proof.drop 482)).bind fun rest => some (head::rest.1,rest.2)) = some (records,suffix) at accepted
    obtain ⟨head,headAccepted,restStep⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨⟨tail,remaining⟩,restAccepted,result⟩ := Option.bind_eq_some_iff.mp restStep
    have same : head::tail = records ∧ remaining = suffix := Prod.mk.inj (Option.some.inj result)
    rcases same with ⟨rfl,rfl⟩
    have data := ih _ _ _ restAccepted
    have headData := accepted_encode _ head headAccepted
    constructor
    · simp only [List.length_cons,data.1]
    · rw [List.flatMap_cons,List.append_assoc,data.2,headData,List.take_append_drop]

def unpackOpening (positions : Positions) (proof : Proof) : Option (List Record × Footer positions) := do
  let (records,rest) ← readRecords positions.card proof
  let footer ← unpack (footerSpec (footerNodes positions)) rest
  return (records,footer)

theorem opening_roundtrip (positions : Positions) (records : List Record) (footer : Footer positions)
    (count : records.length = positions.card) :
    unpackOpening positions (encodeOpening positions records footer) = some (records,footer) := by
  unfold unpackOpening encodeOpening
  rw [←count,read_encoded_records]
  change (do let result ← unpack (footerSpec (footerNodes positions)) (encode footer)
             return (records,result)) = some (records,footer)
  rw [unpack_encode]
  rfl

theorem opening_accepted (positions : Positions) (proof : Proof) (records : List Record) (footer : Footer positions)
    (accepted : unpackOpening positions proof = some (records,footer)) :
    records.length = positions.card ∧ encodeOpening positions records footer = proof := by
  change ((readRecords positions.card proof).bind fun parsed =>
    (unpack (footerSpec (footerNodes positions)) parsed.2).bind fun decoded =>
      some (parsed.1,decoded)) = some (records,footer) at accepted
  obtain ⟨⟨read,rest⟩,ran,final⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨decoded,unpacked,returned⟩ := Option.bind_eq_some_iff.mp final
  have same : read = records ∧ decoded = footer := Prod.mk.inj (Option.some.inj returned)
  rcases same with ⟨rfl,rfl⟩
  have data := read_records_accepted _ _ _ _ ran
  have canonical := accepted_encode rest decoded unpacked
  refine ⟨data.1,?_⟩
  unfold encodeOpening
  rw [canonical]
  exact data.2

theorem opening_empty : unpackOpening ∅ [] = some ([],Payload.nil) := rfl

theorem encode_empty : encodeOpening ∅ [] Payload.nil = [] := rfl

theorem reject_trailing_empty : (unpackOpening ∅ [0]).isNone = true := by decide +kernel

end CommitGolfCandidate.Chained.InteriorCodec
