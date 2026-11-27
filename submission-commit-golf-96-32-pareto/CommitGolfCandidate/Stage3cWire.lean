import CommitGolfCandidate.Stage3cAuth
import CommitGolfCandidate.Stage3cReadWindow
import CommitGolf.Artifact
set_option Elab.async false
namespace CommitGolfCandidate.Pw
open CommitGolf CommitGolf.Riscv
open Late (Digest Salt)
open Chained.BinaryMachine.Reader (window)
def recordIndex (p : Positions) (r : Nat) : Index := (p.sort (·≤·))[r]?.getD ⟨0,by decide⟩
def recordValue (i : CheckInput) (r : Nat) : Entry :=
  ((i.positions.attach.sort (fun x y=>x.val≤y.val))[r]?.map i.values).getD 0

def atProof (i : CheckInput) (off n : Nat) := readBuffer (Artifact.submission.initialState .check i) (13421772800+off) n
/-- An ordinary record is the 24-byte salt and one 32-byte sibling per level: 792 bytes. -/
def plainView (i : CheckInput) : Auth.View where
  idx:=recordIndex i.positions
  entry:=recordValue i
  salt r:=atProof i (792*r) 24
  peers r h:=(atProof i (792*r+24+32*h) 32,0)
  slot _:=0
def layerBits (h : Nat) := 192+((List.range h).map bits).sum
def packedInput (i : CheckInput) := (atProof i 0 67840).toNat
/-- A batch proof is 128 records of 3,780 bits (salt, then the fifteen siblings below the cap)
followed by 256 slots of 230 bits. All 542,720 bits are transmitted. -/
def batchView (i : CheckInput) : Auth.View :=
  let v:=packedInput i
  { idx:=recordIndex i.positions
    entry:=recordValue i
    salt:=fun r=>BitVec.ofNat 192 (window v (3780*r) 192)
    peers:=fun r h=>(BitVec.ofNat 256 (window v (3780*r+layerBits h) (bits h)),0)
    slot:=fun j=>BitVec.ofNat 256 (window v (483840+230*j) 230) }
def wireBits := 8*67840
def batchFields (t : Late.Levels) (s : Late.SaltTape) (xs : List Index) :=
  xs.flatMap (Chained.Binary.recordFields t s)++(List.range 256).map (Chained.Binary.slot t xs)
def wireValid (H : Compression) (i : CheckInput) : Prop :=
  if i.positions.card=BATCH then i.proof.length=67840 ∧ Auth.BatchValid H (batchView i) i.commitment else
    i.proof.length=i.positions.card*792 ∧ ∀ r < i.positions.card,
      Auth.recordAt H (plainView i) r 24 ((plainView i).peers r)=i.commitment
theorem layer_bits : ∀ h : Fin 16,layerBits h.val=([192,448,704,944,1184,1424,1664,1904,2144,2384,2620,2854,3087,3319,3550,3780] : List Nat)[h.val]! := by
  decide +kernel
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

end CommitGolfCandidate.Pw
