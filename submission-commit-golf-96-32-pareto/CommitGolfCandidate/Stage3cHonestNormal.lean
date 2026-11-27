import CommitGolfCandidate.Stage3cHonestWire
set_option Elab.async false
namespace CommitGolfCandidate.Pw
open CommitGolf CommitGolf.Riscv
open Late (Levels SaltTape Digest node bytes)
open Chained.BinaryMachine
open Chained.BinaryMachine.Check (initial proof_byte)
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

def pathBytes (t : Levels) (i : Index) : Proof :=
  (List.range 24).flatMap fun level=>bytes (n:=32) (node t level ((i.val/2^level) ^^^ 1))
theorem record_split (t : Levels) (s : SaltTape) (i : Index) :
    Late.record t s 24 i=bytes (n:=24) (s i)++pathBytes t i := rfl
theorem record_length (t : Levels) (s : SaltTape) (i : Index) : (Late.record t s 24 i).length=792 := by
  rw [record_split];simp [pathBytes,bytes,List.length_flatMap]

attribute [local irreducible] Late.node Chained.Binary.treeM in
theorem normal_wire (o : Oracle) (m : Message) (ps : Positions) (s : SaltTape) (normal : ps.card≠BATCH) :
    wireValid o.compression (canonicalInput o m ps s) := by
  let t:=Chained.Binary.treeM (M:=Id) o.compression m s
  let x:=canonicalInput o m ps s
  let xs:=Open.indices ps
  have view : x.proof=xs.flatMap (Late.record t s 24):=if_neg normal
  have size : x.proof.length=ps.card*792:=by
    rw [view,List.length_flatMap]
    simp only [record_length,List.map_const',List.sum_replicate_nat,Nat.nsmul_eq_mul,
      show xs.length=ps.card from Finset.length_sort ..,smul_eq_mul]
  have cap : x.proof.length≤17179869184:=by
    rw [size]
    have le : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
    change ps.card≤16777216 at le;omega
  change (if ps.card=BATCH then _ else x.proof.length=ps.card*792 ∧ _)
  rw [if_neg normal];refine ⟨size,?_⟩
  intro r hr
  change r<ps.card at hr
  let i:=recordIndex ps r
  have small : r<xs.length:=by simpa only [xs,Open.indices,Finset.length_sort] using hr
  have idx : xs[r]=i:=by change xs[r]=xs[r]?.getD _;rw [List.getElem?_eq_getElem small];rfl
  have loc : ContainsAt x.proof (792*r) (Late.record t s 24 i):=by
    rw [view,←idx];exact flat_field xs _ 792 (record_length t s) r small
  have salt : (plainView x).salt r=s i:=by
    have start : ContainsAt (Late.record t s 24 i) 0 (bytes (n:=24) (s i)):=⟨[],pathBytes t i,rfl,by rw [record_split];simp⟩
    exact parsed (loc.trans start) cap
  have peers (h : Nat) (bh : h<24) : (plainView x).peers r h=Auth.truePeers t i h:=by
    have rest : ContainsAt (Late.record t s 24 i) 24 (pathBytes t i):=⟨bytes (n:=24) (s i),[],by simp [bytes],by rw [record_split];simp⟩
    have inPath:=flat_field (List.range 24) (fun n=>bytes (n:=32) (node t n ((i.val/2^n) ^^^ 1))) 32
      (fun _=>by simp [bytes]) h (by simp;omega)
    simp only [List.getElem_range] at inPath
    have read:=parsed (loc.trans (rest.trans inPath)) cap
    apply Prod.ext
    · change atProof x (792*r+24+32*h) 32=node t h (Auth.peerIndex (Geo.nodeIndex i.val h))
      rw [show 792*r+24+32*h=792*r+(24+32*h) by omega,read,Auth.peer_xor];rfl
    · rfl
  have path:=Auth.honestRecord o.compression m s t (Auth.honestTree ..) (plainView x) r 24 (by decide) salt (honestValue o m ps s r hr) peers
  have root : Geo.nodeIndex i.val 24=0:=by
    have b : Geo.nodeIndex i.val 24<Geo.width 24:=Auth.indexInside i 24
    rw [Geo.width_le 24 (by decide)] at b;simpa using b
  change Auth.recordAt o.compression (plainView x) r 24 _=node t LOG_LENGTH 0
  exact path.trans (congrArg (node t 24) root)

theorem canonical_valid (o : Oracle) (m : Message) (ps : Positions) (s : Late.SaltTape) :
    wireValid o.compression (canonicalInput o m ps s) := by
  by_cases b : ps.card=BATCH
  · change (if ps.card=BATCH then _ else _);rw [if_pos b]
    exact ⟨Chained.BinaryMachine.Check.opening_length _ _ _ b,honest_batch_wire o m ps s b⟩
  · exact normal_wire o m ps s b
end CommitGolfCandidate.Pw
