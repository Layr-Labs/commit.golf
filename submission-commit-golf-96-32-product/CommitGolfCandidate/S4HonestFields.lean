import CommitGolfCandidate.S4Inputs
import CommitGolfCandidate.S4ProofSize
import CommitGolfCandidate.S4HonestCap
namespace CommitGolfCandidate.S4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape Digest bytes node)
open Machine (initial proof_byte)
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
    (capacity : x.proof.length≤17179869184) : proofAt x off n=v := by
  obtain ⟨l,r,hlen,eq⟩ := f
  have bLen : (bytes (n:=n) v).length=n := by simp [bytes]
  have count := congrArg List.length eq
  simp only [List.length_append,hlen,bLen] at count
  have bytesOk (j : Nat) (hj : j<n) :
      (initial x).getByte (BitVec.ofNat 64 (Machine.proofBase+off+j))=v.extractLsb' (8*(0+j)) 8 := by
    have lt : off+j<x.proof.length := by omega
    have hi : Machine.proofBase+(off+j)<2^64 := by unfold Machine.proofBase;omega
    rw [Nat.add_assoc]
    apply (proof_byte x _ lt hi).trans
    have point := congrArg (fun xs : Proof => xs[off+j]?) eq
    have bj : j<(bytes (n:=n) v).length := by simpa only [bLen] using hj
    rw [List.getElem?_eq_getElem lt] at point
    simp only [List.append_assoc] at point
    rw [List.getElem?_append_right (by omega), hlen,Nat.add_sub_cancel_left,List.getElem?_append_left bj,
      List.getElem?_eq_getElem bj] at point
    simpa only [bytes,List.getElem_ofFn,Nat.zero_add] using Option.some.inj point
  exact (read_serialized_slice (initial x) v (Machine.proofBase+off) 0 n bytesOk).trans BitVec.extractLsb'_eq_self

def canonicalInput (m : Message) (ps : Positions) (tree : Levels) (s : SaltTape) : CheckInput :=
  ⟨node tree LOG_LENGTH 0,ps,m.restrict ps, opening .byte tree s ps⟩

theorem honestValue (m : Message) (ps : Positions) (tree : Levels) (s : SaltTape) (r : Nat) (hr : r<ps.card) :
    recordValue (canonicalInput m ps tree s) r = m (recordIndex ps r) := by
  let xs := ps.attach.sort (fun i j => i.val≤j.val)
  have mapped : xs.map Subtype.val = ps.sort (·≤·) := by
    have law := Finset.map_sort (r := fun i j : {i // i ∈ ps} => i.val ≤ j.val)
      (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ ps))
      (s := ps.attach) (by intro a _ b _; rfl)
    simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using law
  change (xs[r]?.map (m.restrict ps)).getD 0 = _
  unfold recordIndex
  rw [←mapped,List.getElem?_map,List.getElem?_eq_getElem (show r<xs.length by simpa [xs] using hr)]
  rfl


end CommitGolfCandidate.S4
