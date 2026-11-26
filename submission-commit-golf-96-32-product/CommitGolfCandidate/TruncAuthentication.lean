import CommitGolfCandidate.TruncSound
import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.BindingMachine
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp

def recordSalt (i : CheckInput) (r : Nat) := readBuffer (submission.initialState .check i) (12079599648+792*r) 24

def normalSibling (i : CheckInput) (r l : Nat) :=
  readBuffer (submission.initialState .check i) (12079599648+792*r+24+32*l) 32

def authSalt (i : CheckInput) (r : Nat) :=
  if i.positions.card=BATCH then batchSalt (wideInput i) r else recordSalt i r
def authSibling (H : Compression) (i : CheckInput) (r : Nat) :=
  if i.positions.card=BATCH then fullSibling H (wideInput i) r else normalSibling i r

def authInputs (H : Compression) (i : CheckInput) (r : Nat) :=
  openingInputs H (recordIndex i r) (authSalt i r) (recordValue i r) (recordPath (recordIndex i r) (authSibling H i r))

theorem authInputsLength (H : Compression) (i : CheckInput) (r : Nat) : (authInputs H i r).length=28 := by
  simp only [authInputs,openingInputs,Late.openingInputs,List.length_append,pathInputs_length,record_path_length,Late.inputs]
  rfl

def CheckSound : Prop := ∀ (o : Oracle) (i : CheckInput),
    (o.eval (submission.scheme.check i.commitment i.positions i.values i.proof)).1=true →
    ∀ r< i.positions.card, recordRoot o.compression (recordValue i r) (authSalt i r) (recordIndex i r)
      (authSibling o.compression i r)=i.commitment

theorem conflict (sound : CheckSound) (o : Oracle) (c : Scheme.Claim) (broken : submission.scheme.Breaks o c)
    (l r : Nat) (recs : ConflictingRecords c l r) :
    ∃ x∈authInputs o.compression (claimLeft c) l, ∃ y∈authInputs o.compression (claimRight c) r,
      x≠y ∧ low240 (o.compression x)=low240 (o.compression y) := by
  have left:=sound o (claimLeft c) broken.2.1 l recs.1
  have right:=sound o (claimRight c) broken.2.2 r recs.2.1
  unfold authInputs
  rw [←recs.2.2.1]
  unfold recordRoot at left right
  rw [←recs.2.2.1] at right
  apply openingWitness
  · exact record_path_directions _ _ _
  · exact recs.2.2.2
  · exact left.trans right.symm

end CommitGolfCandidate.Trunc
