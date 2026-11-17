import Mathlib.Data.List.TakeDrop

namespace CommitGolfCandidate.NonceCodec

def compact {α : Type} : Nat → List α → List α
  | 0, bytes => bytes
  | count+1, bytes => bytes.take 24 ++ (bytes.drop 32).take 512 ++
      compact count (bytes.drop 544)

def expand {α : Type} (zero : α) : Nat → List α → List α
  | 0, bytes => bytes
  | count+1, bytes => bytes.take 24 ++ List.replicate 8 zero ++
      (bytes.drop 24).take 512 ++ expand zero count (bytes.drop 536)

structure Record (α : Type) where
  nonce : List α
  siblings : List α
  nonce_length : nonce.length = 24
  siblings_length : siblings.length = 512

def full {α : Type} (zero : α) (record : Record α) : List α :=
  record.nonce ++ List.replicate 8 zero ++ record.siblings

def packed {α : Type} (record : Record α) : List α :=
  record.nonce ++ record.siblings

theorem full_length {α : Type} (zero : α) (record : Record α) :
    (full zero record).length = 544 := by
  simp [full, record.nonce_length, record.siblings_length]

theorem packed_length {α : Type} (record : Record α) :
    (packed record).length = 536 := by
  simp [packed, record.nonce_length, record.siblings_length]

theorem compact_cons {α : Type} (zero : α) (record : Record α)
    (tail : List α) (count : Nat) :
    compact (count+1) (full zero record ++ tail) =
      packed record ++ compact count tail := by
  have drop32 : record.nonce.drop 32 = [] := List.drop_eq_nil_of_le (by rw [record.nonce_length]; decide)
  have drop544 : record.nonce.drop 544 = [] := List.drop_eq_nil_of_le (by rw [record.nonce_length]; decide)
  simp [compact, full, packed, List.drop_append, drop32, drop544,
    record.nonce_length, record.siblings_length, List.append_assoc]

theorem expand_cons {α : Type} (zero : α) (record : Record α)
    (tail : List α) (count : Nat) :
    expand zero (count+1) (packed record ++ tail) =
      full zero record ++ expand zero count tail := by
  have drop536 : record.nonce.drop 536 = [] := List.drop_eq_nil_of_le (by rw [record.nonce_length]; decide)
  simp [expand, full, packed, List.drop_append, drop536,
    record.nonce_length, record.siblings_length, List.append_assoc]

def fullRecords {α : Type} (zero : α) (records : List (Record α)) (suffix : List α) : List α :=
  records.foldr (fun record tail => full zero record ++ tail) suffix

def packedRecords {α : Type} (records : List (Record α)) (suffix : List α) : List α :=
  records.foldr (fun record tail => packed record ++ tail) suffix

theorem compact_records {α : Type} (zero : α) (records : List (Record α))
    (suffix : List α) :
    compact records.length (fullRecords zero records suffix) = packedRecords records suffix := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    simpa only [List.length_cons, fullRecords, packedRecords, List.foldr_cons,
      compact_cons] using congrArg (fun tail => packed record ++ tail) ih

theorem expand_records {α : Type} (zero : α) (records : List (Record α))
    (suffix : List α) :
    expand zero records.length (packedRecords records suffix) = fullRecords zero records suffix := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    simpa only [List.length_cons, fullRecords, packedRecords, List.foldr_cons,
      expand_cons] using congrArg (fun tail => full zero record ++ tail) ih

theorem roundtrip {α : Type} (zero : α) (records : List (Record α))
    (suffix : List α) :
    expand zero records.length (compact records.length (fullRecords zero records suffix)) =
      fullRecords zero records suffix := by
  rw [compact_records, expand_records]

theorem full_records_length {α : Type} (zero : α) (records : List (Record α))
    (suffix : List α) :
    (fullRecords zero records suffix).length = 544*records.length + suffix.length := by
  induction records with
  | nil => simp [fullRecords]
  | cons record records ih =>
    simp only [fullRecords, List.foldr_cons, List.length_append, full_length,
      List.length_cons] at ih ⊢
    omega

theorem packed_records_length {α : Type} (records : List (Record α))
    (suffix : List α) :
    (packedRecords records suffix).length = 536*records.length + suffix.length := by
  induction records with
  | nil => simp [packedRecords]
  | cons record records ih =>
    simp only [packedRecords, List.foldr_cons, List.length_append, packed_length,
      List.length_cons] at ih ⊢
    omega

theorem batch_saving {α : Type} (zero : α) (records : List (Record α))
    (suffix : List α) (batch : records.length=128) :
    (packedRecords records suffix).length + 1024 =
      (fullRecords zero records suffix).length := by
  rw [full_records_length, packed_records_length, batch]
  omega

end CommitGolfCandidate.NonceCodec
