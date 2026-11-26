import CommitGolfCandidate.S5HonestBatchWire
import CommitGolfCandidate.S5NormalOpen
namespace CommitGolfCandidate.S5
open CommitGolf CommitGolf.Riscv
open Late (Levels SaltTape Digest node bytes)
open S5Machine
open S5Machine.Check (initial proof_byte)
open S5Machine.Open (normalBytes bottomSibling pathBytes mate)
def ContainsAt (xs : Proof) (off : Nat) (v : Proof) := ∃ l r : Proof, l.length=off ∧ xs=l++v++r

theorem ContainsAt.trans {xs mid obj : Proof} {a b : Nat}
    (x : ContainsAt xs a mid) (y : ContainsAt mid b obj) : ContainsAt xs (a+b) obj := by
  obtain ⟨l,r,hl,h⟩ := x;obtain ⟨s,t,hs,e⟩ := y
  exact ⟨l++s,t++r,by simp [hl,hs],by rw [h,e];simp [List.append_assoc]⟩

theorem flat_field {α : Type} (xs : List α) (f : α → Proof) (size : Nat)
    (width : ∀ x, (f x).length=size) (r : Nat) (h : r<xs.length) :
    ContainsAt (xs.flatMap f) (size*r) (f xs[r]) := by
  induction xs generalizing r with
  | nil => simp at h
  | cons x xs ih =>
    cases r with
    | zero => exact ⟨[],xs.flatMap f,by simp,by simp⟩
    | succ r =>
      have hr : r<xs.length := by simpa using h
      obtain ⟨l,t,hlen,split⟩ := ih r hr
      refine ⟨f x++l,t,?_,?_⟩
      · rw [List.length_append,width,hlen,Nat.mul_succ,Nat.add_comm]
      · simp only [List.flatMap_cons,split,List.getElem_cons_succ,List.append_assoc]

theorem parsed {x : CheckInput} {n off : Nat} {v : BitVec (8*n)} (f : ContainsAt x.proof off (bytes v))
    (capacity : x.proof.length≤17179869184) : atProof x off n=v := by
  obtain ⟨l,r,hlen,eq⟩ := f
  have bLen : (bytes (n:=n) v).length=n := by simp [bytes]
  have count := congrArg List.length eq
  simp only [List.length_append,hlen,bLen] at count
  have bytesOk (j : Nat) (hj : j<n) :
      (initial x).getByte (BitVec.ofNat 64 (Check.proofBase+off+j))=v.extractLsb' (8*(0+j)) 8 := by
    have lt : off+j<x.proof.length := by omega
    have hi : Check.proofBase+(off+j)<2^64 := by unfold Check.proofBase;omega
    rw [Nat.add_assoc]
    apply (proof_byte x _ lt hi).trans
    have point := congrArg (fun xs : Proof => xs[off+j]?) eq
    have bj : j<(bytes (n:=n) v).length := by simpa only [bLen] using hj
    rw [List.getElem?_eq_getElem lt] at point
    simp only [List.append_assoc] at point
    rw [List.getElem?_append_right (by omega), hlen,Nat.add_sub_cancel_left,List.getElem?_append_left bj,
      List.getElem?_eq_getElem bj] at point
    simpa only [bytes,List.getElem_ofFn,Nat.zero_add] using Option.some.inj point
  exact (read_serialized_slice (initial x) v (Check.proofBase+off) 0 n bytesOk).trans BitVec.extractLsb'_eq_self

private theorem as_sibling (t : Levels) (i : Index) (h : Nat) (pos : 0<h) :
    node t h (mate i h)=Auth.sibling t i.val h 0 := by
  unfold Auth.sibling
  rw [S4.nextIndex,S4.childPos,show S4.radix h=2 from if_neg (by omega)]
  apply congrArg (node t h)
  let j:=S4.nodeIndex i.val h
  change j ^^^ 1=2*(j/2)+(j%2+0+1)%2
  by_cases even : j%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega
private theorem bottom_peer (t : Levels) (i : Index) (k : Nat) : bottomSibling t i (k+1)=Auth.sibling t i.val 0 k := by
  change node t 0 _=node t 0 _;apply congrArg (node t 0)
  simp [Open.bottomSibling,Open.slotNumber,S4.nodeIndex,S4.childPos,S4.span,S4.radix,Nat.add_assoc]

private theorem before_path (t : Levels) (salt : SaltTape) (i : Index) :
    ContainsAt (normalBytes t salt i) 88 (pathBytes t i 1 23) := by
  let p:=bytes (n:=24) (salt i)++bytes (n:=32) (bottomSibling t i 1)++bytes (n:=32) (bottomSibling t i 2)
  exact ⟨p,[],by simp [p,bytes],by simp [p,normalBytes,List.append_assoc]⟩

theorem normal_wire (o : Oracle) (m : Message) (ps : Positions) (s : SaltTape) (normal : ps.card≠BATCH) :
    wireValid o.compression (canonicalInput o m ps s) := by
  let t:=S5Hiding.tree o.compression m s
  let x:=canonicalInput o m ps s
  let xs:=Open.indices ps
  have view : x.proof=xs.flatMap (normalBytes t s):=Open.normal_opening t s ps normal
  have size : x.proof.length=ps.card*824:=by
    rw [view,List.length_flatMap];simp only [Open.normal_length,List.map_const',List.sum_replicate_nat,Nat.nsmul_eq_mul,
      show xs.length=ps.card from Finset.length_sort ..]
  have cap : x.proof.length≤17179869184:=by
    rw [size]
    have le : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
    change ps.card≤16777216 at le;omega
  change (if ps.card=BATCH then _ else x.proof.length=ps.card*824 ∧ _)
  rw [if_neg normal];refine ⟨size,?_⟩
  intro r hr
  change r<ps.card at hr
  let i:=recordIndex ps r
  have small : r<xs.length:=by simpa only [xs,Open.indices,Finset.length_sort] using hr
  have idx : xs[r]=i:=by change xs[r]=xs[r]?.getD _;rw [List.getElem?_eq_getElem small];rfl
  have loc : ContainsAt x.proof (824*r) (normalBytes t s i):=by
    rw [view,←idx];exact flat_field xs _ 824 (Open.normal_length t s) r small
  have salt : (plainView x).salt r=s i:=by
    have start : ContainsAt (normalBytes t s i) 0 (bytes (n:=24) (s i)):=⟨[],bytes (n:=32) (bottomSibling t i 1)++bytes (n:=32) (bottomSibling t i 2)++pathBytes t i 1 23,rfl,by simp [normalBytes,List.append_assoc]⟩
    exact parsed (loc.trans start) cap
  have peers (h : Nat) (bh : h<24) : (plainView x).peers r h=Auth.truePeers t i h:=by
    by_cases bottom : h=0
    · subst h
      let a:=bytes (n:=24) (s i)
      let b:=bytes (n:=32) (bottomSibling t i 1)
      let d:=bytes (n:=32) (bottomSibling t i 2)
      have lo : ContainsAt (normalBytes t s i) 24 b:=⟨a,d++pathBytes t i 1 23,by simp [a,bytes],by simp [normalBytes,a,b,d,List.append_assoc]⟩
      have hi : ContainsAt (normalBytes t s i) 56 d:=⟨a++b,pathBytes t i 1 23,by simp [a,b,bytes],by simp [normalBytes,a,b,d,List.append_assoc]⟩
      apply Prod.ext
      · exact (parsed (loc.trans lo) cap).trans (bottom_peer t i 0)
      · have read:=parsed (loc.trans hi) cap
        change atProof x (824*r+24+32*0+32) 32=_
        rw [show 824*r+24+32*0+32=824*r+56 by omega,read];exact bottom_peer t i 1
    · have inPath:=flat_field (List.range' 1 23) (fun n=>bytes (n:=32) (node t n (mate i n))) 32
        (fun _=>by simp [bytes]) (h-1) (by simp;omega)
      have hit : (List.range' 1 23)[h-1]'(by simp;omega)=h:=by simp;omega
      rw [hit] at inPath
      have read:=parsed (loc.trans ((before_path t s i).trans inPath)) cap
      apply Prod.ext
      · change atProof x (824*r+24+32*(if h=0 then 0 else h+1)) 32=Auth.sibling t i.val h 0
        rw [if_neg bottom,show 824*r+24+32*(h+1)=824*r+(88+32*(h-1)) by omega,read];exact as_sibling t i h (by omega)
      · simp [plainView,Auth.truePeers,bottom]
  have path:=Auth.honestRecord o.compression m s t (Auth.honestTree ..) (plainView x) r 24 (by decide) salt (honestValue o m ps s r hr) peers
  have root : S4.nodeIndex i.val 24=0:=by have b : S4.nodeIndex i.val 24<1:=Auth.indexInside i 24;omega
  change Auth.recordAt o.compression (plainView x) r 24 _=node t 24 0
  exact path.trans (congrArg (node t 24) root)
end CommitGolfCandidate.S5
