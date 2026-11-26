import CommitGolfCandidate.ReconstructedWire
import CommitGolfCandidate.ReconstructedLeafTape
import CommitGolfCandidate.ReconstructedLeafTree

namespace CommitGolfCandidate.Reconstruction.Encoding
open CommitGolf TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64
open Wire
variable {α : Type}
set_option maxRecDepth 8192

abbrev Tree := Nat → Nat → Binding.Digest

def compress (c : Compression) : Binding.Compress := fun k => Binding.unpack (c (Binding.encodeKey k))
def projected (tape : DigestTape) (j : Nat) := Binding.project 24 (Binding.unpack (tape (LeafTree.leafNumber j)))
def reference (c : Compression) (tape : DigestTape) : Tree := CommitParents.node (compress c) (projected tape)

def lows (depth : Nat) := sameSize.lows[depth]?.getD 0
def base (depth : Nat) := sameSize.bases[depth]?.getD 1

/-- The checker reads three full low words and the low portion of the high word. -/
def lowFields (n : Binding.Digest) (width : Nat) : List Field :=
  [⟨n.1.toNat,64⟩,⟨n.1.toNat >>> 64,64⟩,⟨n.1.toNat >>> 128,64⟩,⟨n.2.toNat,width-192⟩]

def highDigit (n : Binding.Digest) (width : Nat) := n.2.toNat >>> (width-192)

def sibling (i : Index) (d : Nat) := (((2^24+i.val) >>> (24-d)) ^^^ 1)

def recordHeader (tree : Tree) (i : Index) :=
  (List.range 10).foldl (fun h j =>
    let d := 10+j
    h*base d+highDigit (tree d (sibling i d)) (lows d)) 0

def record (tree : Tree) (i : Index) (salt : BitVec 128) : List Field :=
  let hdr := recordHeader tree i
  [⟨salt.toNat,64⟩,⟨salt.toNat >>> 64,56⟩,⟨hdr,64⟩,⟨hdr >>> 64,38⟩] ++
    (List.range 15).flatMap (fun j => let d := 24-j; lowFields (tree d (sibling i d)) (lows d))

def headerValue (digit : Nat → Nat) : List Nat → Nat
  | [] => 0
  | i::tail => digit i+211*headerValue digit tail

def capHeaders (digit : Nat → Nat) : List Nat → List Field
  | [] => []
  | a::b::c::d::rest => ⟨headerValue digit [a,b,c,d],31⟩ :: capHeaders digit rest
  | rest => [⟨headerValue digit rest,31⟩]

def cap (tree : Tree) : Nat → List Bool → List Field
  | 0,_ => []
  | d+1,active =>
    let depth := d+1
    let (next,missing) := Frontier.scan (2^depth) active
    missing.flatMap (fun j => lowFields (tree depth j) (lows depth)) ++
      (if 8≤depth then capHeaders (fun j => highDigit (tree depth j) (lows depth)) missing else []) ++
      cap tree d next

def fields (tree : Tree) (positions : Positions) (salts : OpenedSalts positions) :=
  let sequence := positions.sort (·≤·)
  (sequence.flatMap (fun i => record tree i (publicOpenedSalts salts i))) ++ cap tree 9 (Frontier.flags sequence)

def build : TranscriptBuilder := fun c positions salts tape =>
  let tree := reference c tape
  (Binding.pack (tree 0 1),bytes (fields tree positions salts))

theorem low_bits (n : Binding.Digest) (w : Nat) : bits (lowFields n w) = 192+(w-192) := by
  simp only [lowFields,bits,Nat.add_zero];omega

private theorem flat (xs : List α) (f : α→List Field) (sz : α→Nat) (eq : ∀ x, bits (f x)=sz x) :
    bits (xs.flatMap f)=(xs.map sz).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,bits_append,eq,ih,List.map_cons,List.sum_cons]

theorem record_bits (tree : Tree) (i : Index) (salt : BitVec 128) : bits (record tree i salt)=3633 := by
  rw [record,bits_append]
  have n := flat (List.range 15) (fun j => lowFields (tree (24-j) (sibling i (24-j))) (lows (24-j)))
    (fun j => 192+(lows (24-j)-192)) (fun j => low_bits ..)
  rw [n]
  rfl

theorem cap_header_bits (f : Nat → Nat) (xs : List Nat) :
    bits (capHeaders f xs)=31*((xs.length+3)/4) := by
  match xs with
  | [] => rfl
  | [_] => simp [capHeaders,bits]
  | [_,_] => simp [capHeaders,bits]
  | [_,_,_] => simp [capHeaders,bits]
  | a::b::c::d::tail =>
    simp only [capHeaders,bits,cap_header_bits f tail,List.length_cons]
    omega

private theorem ordinary (t : Tree) (d : Nat) (small : d≤7) (flags : List Bool) :
    bits (cap t d flags)=240*Frontier.ordinaryFields d flags := by
  induction d generalizing flags with
  | zero => simp [cap,bits,Frontier.ordinaryFields]
  | succ n ih =>
    have widths : ∀ j : Fin 7, lows (j.val+1)=240 := by decide
    have w := widths ⟨n,by omega⟩
    change lows (n+1)=240 at w
    have count (ids : List Nat) : bits (ids.flatMap (fun j => lowFields (t (n+1) j) (lows (n+1))))=240*ids.length := by
      apply Wire.flat_bits
      intro j
      rw [low_bits,w]
    simp only [cap,bits_append,show ¬8≤n+1 by omega,ite_false,bits,Nat.add_zero,
      count,ih (by omega),Frontier.ordinaryFields,Nat.mul_add]

theorem all_bits (t : Tree) (ps : Positions) (salts : OpenedSalts ps) :
    bits (fields t ps salts)=Frontier.cursor (ps.sort (·≤·)) := by
  let xs := ps.sort (·≤·)
  let a := Frontier.scan 512 (Frontier.flags xs)
  let b := Frontier.scan 256 a.1
  have paid (d : Nat) (ids : List Nat) (w : lows d=224) :
      bits (ids.flatMap (fun j => lowFields (t d j) (lows d))) = 224*ids.length := by
    apply Wire.flat_bits
    intro j
    rw [low_bits,w]
  rw [fields,bits_append,Wire.flat_bits _ _ 3633 (fun x => record_bits ..)]
  change 3633*xs.length+bits (cap t 9 (Frontier.flags xs)) = _
  have eq : cap t 9 (Frontier.flags xs) =
      (a.2.flatMap (fun j => lowFields (t 9 j) (lows 9)) ++ capHeaders (fun j => highDigit (t 9 j) (lows 9)) a.2) ++
      ((b.2.flatMap (fun j => lowFields (t 8 j) (lows 8)) ++ capHeaders (fun j => highDigit (t 8 j) (lows 8)) b.2) ++ cap t 7 b.1) := rfl
  rw [eq]
  simp only [bits_append,paid 9 _ (by decide),paid 8 _ (by decide),cap_header_bits,ordinary t 7 (by decide)]
  change _ = 3633*xs.length+224*(a.2.length+b.2.length)+31*((a.2.length+3)/4+(b.2.length+3)/4)+240*Frontier.ordinaryFields 7 b.1
  omega

theorem batch (c : Compression) (ps : Positions) (salts : OpenedSalts ps) (tape : DigestTape) (h : ps.card=128) :
    (build c ps salts tape).2.length≤65544 := by
  change (bytes (fields _ _ _)).length ≤ _
  rw [byte_count,all_bits]
  have len : (ps.sort (·≤·)).length=ps.card := Finset.length_sort _
  exact (Frontier.cursor_bound _ (len.trans h)).2

end CommitGolfCandidate.Reconstruction.Encoding
