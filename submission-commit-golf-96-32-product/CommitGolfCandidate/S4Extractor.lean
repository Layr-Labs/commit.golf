import CommitGolfCandidate.S4Wire
import CommitGolfCandidate.S4CapReplay

namespace CommitGolfCandidate.S4
open CommitGolf OracleComp
open Late (Digest Block submission)

def authData (H : Compression) (i : CheckInput) (r : Nat) :=
  if i.positions.card=BATCH then batchPeers .packed H (readView (wideInput i)) r else (readView (wideInput i)).peers r

def authInputs (H : Compression) (i : CheckInput) (r : Nat) :=
  recordInputs .packed H (readView (wideInput i)) r (authData H i r) 24

def extractCost (i : CheckInput) := if i.positions.card=BATCH then batchCost else 28
def extractRecord (i : CheckInput) (r : Nat) : Queries (extractCost i) (List Block) :=
  if b : i.positions.card=BATCH then Queries.retime (if_pos b : extractCost i=batchCost).symm
    (Queries.map Prod.snd (batchExtract .packed (readView (wideInput i)) r)) else
    Queries.retime (if_neg b : extractCost i=28).symm
    (Queries.map Prod.snd (replayRecord .packed (readView (wideInput i)) r ((readView (wideInput i)).peers r) 24))

theorem extractValue (i : CheckInput) (r : Nat) (o : Oracle) :
    (extractRecord i r).eval o=authInputs o.compression i r := by
  by_cases b : i.positions.card=BATCH <;>
    simp only [extractRecord,authInputs,authData,b,↓reduceDIte,↓reduceIte,Queries.retime,Queries.map,batchExtractValue,replayValue]

theorem extractRun (i : CheckInput) (r : Nat) (o : Oracle) :
    o.run (extractRecord i r).code=pure (authInputs o.compression i r,extractCost i) := by
  rw [(extractRecord i r).runs,extractValue]
theorem authInputsLength (H : Compression) (i : CheckInput) (r : Nat) : (authInputs H i r).length=28 :=
  inputsLength .. 

theorem acceptedRoot (sound : CheckSound) (o : Oracle) (i : CheckInput) (ok : accepted o i)
    (r : Nat) (inside : r < i.positions.card) :
    recordAt .packed o.compression (readView (wideInput i)) r 24 (authData o.compression i r)=i.commitment := by
  have w:=sound o i ok
  change (if i.positions.card=BATCH then _ else _) at w
  by_cases b : i.positions.card=BATCH
  · rw [authData,if_pos b]
    rw [if_pos b] at w
    exact batchImpliesRoot _ _ _ _ w.2 r (by simpa only [b,BATCH] using inside)
  · rw [authData,if_neg b]
    rw [if_neg b] at w
    exact w.2 r inside

def claimLeft (c : Scheme.Claim) : CheckInput := ⟨c.root,c.positions₀,c.values₀,c.proof₀⟩
def claimRight (c : Scheme.Claim) : CheckInput := ⟨c.root,c.positions₁,c.values₁,c.proof₁⟩

def Differ (c : Scheme.Claim) (pair : Nat × Nat) :=
  pair.1 < c.positions₀.card ∧ pair.2 < c.positions₁.card ∧
  recordIndex c.positions₀ pair.1 = recordIndex c.positions₁ pair.2 ∧
  recordValue (claimLeft c) pair.1 ≠ recordValue (claimRight c) pair.2

theorem differing {c : Scheme.Claim} (e : c.Conflicting) : ∃ pair,Differ c pair := by
  obtain ⟨i,hl,hr,diff⟩:=e
  obtain ⟨a,ha,ia,va⟩:=selected (claimLeft c) i hl
  obtain ⟨b,hb,ib,vb⟩:=selected (claimRight c) i hr
  exact ⟨(a,b),ha,hb,ia.trans ib.symm,fun eqv=>diff (va.symm.trans (eqv.trans vb))⟩

noncomputable def selectedRecords (c : Scheme.Claim) : Nat×Nat := open Classical in
  if e : c.Conflicting then (differing e).choose else (0,0)

theorem selected_records_conflict (c : Scheme.Claim) (e : c.Conflicting) : Differ c (selectedRecords c) := by
  simpa only [selectedRecords,dif_pos e] using (differing e).choose_spec

theorem conflict (sound : CheckSound) (o : Oracle) (c : Scheme.Claim) (win : Late.submission.scheme.Breaks o c)
    (a b : Nat) (diff : Differ c (a,b)) :
    Witness .packed o.compression (authInputs o.compression (claimLeft c) a) (authInputs o.compression (claimRight c) b) := by
  obtain ⟨ha,hb,idx,ne⟩:=diff
  exact recordsCollide .packed o.compression _ _ a b _ _ 24 idx ne ((acceptedRoot sound o (claimLeft c) win.2.1 a ha).trans (acceptedRoot sound o (claimRight c) win.2.2 b hb).symm)

end CommitGolfCandidate.S4
