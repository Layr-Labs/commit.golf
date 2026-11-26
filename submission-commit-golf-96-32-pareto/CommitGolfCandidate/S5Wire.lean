import CommitGolfCandidate.S5Auth
import CommitGolfCandidate.S5Tail
import CommitGolf.Artifact
namespace CommitGolfCandidate.S5
open CommitGolf CommitGolf.Riscv
open Late (Digest Salt)
open S5Machine.Reader (window)
def recordIndex (p : Positions) (r : Nat) : Index := (p.sort (·≤·))[r]?.getD ⟨0,by decide⟩
def recordValue (i : CheckInput) (r : Nat) : Entry :=
  ((i.positions.attach.sort (fun x y=>x.val≤y.val))[r]?.map i.values).getD 0


def atProof (i : CheckInput) (off n : Nat) := readBuffer (Artifact.submission.initialState .check i) (13421772800+off) n
def plainView (i : CheckInput) : Auth.View where
  idx:=recordIndex i.positions
  entry:=recordValue i
  salt r:=atProof i (824*r) 24
  peers r h:=
    let at_:=824*r+24+32*(if h=0 then 0 else h+1)
    (atProof i at_ 32,if h=0 then atProof i (at_+32) 32 else 0)
  slot _:=0
def layerBits (h : Nat) := 192+((List.range h).map fun j=>(S4.radix j-1)*bits j).sum
def packedInput (i : CheckInput) := (atProof i 0 69396).toNat
def batchView (i : CheckInput) (trial : Fin 4) : Auth.View :=
  let v:=complete (packedInput i) trial.val
  { idx:=recordIndex i.positions
    entry:=recordValue i
    salt:=fun r=>BitVec.ofNat 192 (window v (4030*r) 192)
    peers:=fun r h=>
      let off:=4030*r+layerBits h
      (BitVec.ofNat 256 (window v off (bits h)),if h=0 then BitVec.ofNat 256 (window v (off+256) 256) else 0)
    slot:=fun j=>BitVec.ofNat 256 (window v (515840+230*j) 230) }
def wireValid (H : Compression) (i : CheckInput) : Prop :=
  if i.positions.card=BATCH then i.proof.length=69396 ∧ ∃ trial,Auth.BatchValid H (batchView i trial) i.commitment else
    i.proof.length=i.positions.card*824 ∧ ∀ r < i.positions.card,
      Auth.recordAt H (plainView i) r 24 ((plainView i).peers r)=i.commitment
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

end CommitGolfCandidate.S5
