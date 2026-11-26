import CommitGolfCandidate.S4Auth
import CommitGolfCandidate.LateArtifact

namespace CommitGolfCandidate.S4
open CommitGolf CommitGolf.Riscv
open Late (Digest Salt submission)

def recordIndex (p : Positions) (r : Nat) : Index := (p.sort (·≤·))[r]?.getD ⟨0,by decide⟩
def recordValue (i : CheckInput) (r : Nat) : Entry :=
  ((i.positions.attach.sort (fun x y=>x.val≤y.val))[r]?.map i.values).getD 0

def recordBytes (batch : Bool) := if batch then 510 else 824
def fieldOffset (batch : Bool) (h : Nat) :=
  if h=0 then 24 else if batch && decide (1<h) then 120+30*(h-2) else 24+32*(h+1)
def fieldBytes (batch : Bool) (h : Nat) := if batch && decide (1<h) then 30 else 32

def proofAt (i : CheckInput) (off n : Nat) :=
  readBuffer (Late.submission.initialState .check i) (Late.submission.layout.proof+off) n

def readView (i : CheckInput) : View :=
  let batch:=decide (i.positions.card=BATCH)
  let offset r:=r*recordBytes batch
  { idx:=recordIndex i.positions
    entry:=recordValue i
    salt:=fun r=>proofAt i (offset r) 24
    peers:=fun r h=>
      let f:=offset r+fieldOffset batch h
      ((proofAt i f (fieldBytes batch h)).setWidth 256,if h=0 then proofAt i (f+32) 32 else 0)
    slot:=fun j=>(proofAt i (65280+30*j) 30).setWidth 256 }

def wireValid (H : Compression) (i : CheckInput) : Prop :=
  if i.positions.card=BATCH then i.proof.length=70410 ∧ BatchValid .packed H (readView i) i.commitment else
    i.proof.length=i.positions.card*824 ∧ ∀ r < i.positions.card,recordAt .packed H (readView i) r 24 ((readView i).peers r)=i.commitment

def accepted (o : Oracle) (i : CheckInput) :=
  (o.eval (Late.submission.scheme.check i.commitment i.positions i.values i.proof)).1=true

def wideInput (i : CheckInput) : CheckInput :=
  { i with proof:=if i.positions.card=BATCH then if i.proof.length=70080 then Carry.wide i.proof else [] else i.proof }

def CheckSound := ∀ o i,accepted o i → wireValid o.compression (wideInput i)

theorem selected (input : CheckInput) (i : Index) (mem : i ∈ input.positions) :
    ∃ r < input.positions.card, recordIndex input.positions r = i ∧ recordValue input r = input.values ⟨i,mem⟩ := by
  let ps := input.positions
  let xs := ps.attach.sort (fun a b => a.val ≤ b.val)
  have mapped : xs.map Subtype.val = ps.sort (· ≤ ·) := by
    have law := Finset.map_sort (r := fun i j : {i // i ∈ ps} => i.val ≤ j.val)
      (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ ps))
      (s := ps.attach) (by intro a _ b _; rfl)
    simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using law
  have present : (⟨i,mem⟩ : {x // x ∈ ps}) ∈ xs := by simp [xs]
  obtain ⟨r,hr,atIndex⟩ := List.getElem_of_mem present
  have hit : xs[r]? = some ⟨i,mem⟩ := (List.getElem?_eq_getElem hr).trans (congrArg some atIndex)
  refine ⟨r, by simpa only [xs, Finset.length_sort, Finset.card_attach] using hr, ?_, ?_⟩
  · change ((ps.sort (· ≤ ·))[r]?.getD _) = _
    rw [← mapped, List.getElem?_map, hit]; rfl
  · change ((xs[r]?).map input.values).getD _ = _
    rw [hit]; rfl

end CommitGolfCandidate.S4
