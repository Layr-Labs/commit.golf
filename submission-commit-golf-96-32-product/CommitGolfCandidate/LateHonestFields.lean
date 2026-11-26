import CommitGolfCandidate.LateCheckInputs
import CommitGolfCandidate.LateFormat

namespace CommitGolfCandidate.Late.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private def ContainsAt (xs : Proof) (off : Nat) (v : Proof) := ∃ l r : Proof, l.length=off ∧ xs=l++v++r

private theorem ContainsAt.trans {xs mid obj : Proof} {a b : Nat}
    (x : ContainsAt xs a mid) (y : ContainsAt mid b obj) : ContainsAt xs (a+b) obj := by
  obtain ⟨l,r,hl,h⟩ := x;obtain ⟨s,t,hs,e⟩ := y
  exact ⟨l++s,t++r,by simp [hl,hs],by rw [h,e];simp [List.append_assoc]⟩

private theorem flat_field {α : Type} (xs : List α) (f : α → Proof) (size : Nat)
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

private theorem parsed {x : CheckInput} {n off : Nat} {v : BitVec (8*n)} (f : ContainsAt x.proof off (bytes v))
    (capacity : x.proof.length≤13421772800) : proofAt x off n=v := by
  obtain ⟨l,r,hlen,eq⟩ := f
  have bLen : (bytes (n:=n) v).length=n := by simp [bytes]
  have count := congrArg List.length eq
  simp only [List.length_append,hlen,bLen] at count
  have bytesOk (j : Nat) (hj : j<n) :
      (initial x).getByte (BitVec.ofNat 64 (Open.proofBase+off+j))=v.extractLsb' (8*(0+j)) 8 := by
    have lt : off+j<x.proof.length := by omega
    have hi : Open.proofBase+(off+j)<2^64 := by unfold Open.proofBase;omega
    rw [Nat.add_assoc]
    apply (proof_byte x _ lt hi).trans
    have point := congrArg (fun xs : Proof => xs[off+j]?) eq
    have bj : j<(bytes (n:=n) v).length := by simpa only [bLen] using hj
    rw [List.getElem?_eq_getElem lt] at point
    simp only [List.append_assoc] at point
    rw [List.getElem?_append_right (by omega), hlen,Nat.add_sub_cancel_left,List.getElem?_append_left bj,
      List.getElem?_eq_getElem bj] at point
    simpa only [bytes,List.getElem_ofFn,Nat.zero_add] using Option.some.inj point
  exact (read_serialized_slice (initial x) v (Open.proofBase+off) 0 n bytesOk).trans BitVec.extractLsb'_eq_self

def canonicalInput (m : Message) (ps : Positions) (tree : Levels) (s : SaltTape) : CheckInput :=
  ⟨node tree LOG_LENGTH 0,ps,m.restrict ps, wideOpening tree s ps⟩

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

private theorem sane (m : Message) (p : Positions) (t : Levels) (s : SaltTape) :
    (canonicalInput m p t s).proof.length≤13421772800 := by
  change (wideOpening t s p).length≤_
  rw [wide_size];have le : p.card≤LENGTH := by simpa using Finset.card_le_univ p
  change p.card≤16777216 at le;split <;> omega

private theorem record_field (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (r : Nat) (hr : r<ps.card) :
    let x := canonicalInput m ps t s
    ContainsAt x.proof (start x r) (record t s (depth x) (recordIndex ps r)) := by
  let xs := ps.sort (·≤·)
  have len : xs.length=ps.card := Finset.length_sort ..
  have fit : r<xs.length := by omega
  let d := depth (canonicalInput m ps t s)
  have wholeRecord := flat_field xs (record t s d) (24+32*d) (fun i=>record_size t s d i) r fit
  have index : recordIndex ps r=xs[r] := by change xs[r]?.getD _=xs[r];rw [List.getElem?_eq_getElem fit];rfl
  obtain ⟨a,b,ha,eq⟩ := wholeRecord
  by_cases batch : ps.card=BATCH
  · have hd : d=16 := by change (if ps.card=BATCH then 16 else 24) = _;rw [if_pos batch]
    refine ⟨a,b++(List.range 128).flatMap (fun p => bytes (n:=32) (capSlot t xs p)),?_,?_⟩
    · exact ha.trans (Nat.mul_comm ..)
    · change wideOpening t s ps = a ++ record t s d (recordIndex ps r) ++ _
      rw [wideOpening,if_pos batch,←hd,index]
      exact (congrArg (· ++ _) eq).trans (by simp [List.append_assoc,xs])
  · have hd : d=24 := by change (if ps.card=BATCH then 16 else 24)=_;rw [if_neg batch]
    refine ⟨a,b,ha.trans (Nat.mul_comm ..),?_⟩
    change wideOpening t s ps = a++record t s d (recordIndex ps r)++b
    rw [wideOpening,if_neg batch,index]
    exact (show LOG_LENGTH=d from hd.symm) ▸ eq

theorem honest_salt (m : Message) (p : Positions) (t : Levels) (s : SaltTape) (r : Nat) (hr : r<p.card) :
    salt (canonicalInput m p t s) r = s (recordIndex p r) := by
  apply parsed _ (sane m p t s)
  obtain ⟨l,z,len,wholeRecord⟩ := record_field m p t s r hr
  let i:=recordIndex p r
  let d:=depth (canonicalInput m p t s)
  let tail:=(List.range d).flatMap fun j=>bytes (n:=32) (node t j ((i.val/2^j) ^^^ 1))
  refine ⟨l,tail++z,len,?_⟩
  rw [wholeRecord]
  exact (by simp only [record,List.append_assoc];rfl)

theorem honest_sibling (m : Message) (p : Positions) (t : Levels) (s : SaltTape) (r l : Nat) (hr : r<p.card)
    (hl : l<depth (canonicalInput m p t s)) :
    sibling (canonicalInput m p t s) r l=node t l (((recordIndex p r).val/2^l) ^^^ 1) := by
  let x := canonicalInput m p t s;let d := depth x;let i := recordIndex p r
  apply parsed _ (sane m p t s)
  have wholeRecord := record_field m p t s r hr
  let field (j : Nat) := bytes (n:=32) (node t j ((i.val/2^j) ^^^ 1))
  obtain ⟨a,b,len,eq⟩ := flat_field (List.range d) field 32 (by intro; simp [field,bytes]) l
    (by simpa only [List.length_range] using hl)
  rw [List.getElem_range] at eq
  have sub : ContainsAt (record t s d i) (24+32*l) (field l) := by
    refine ⟨bytes (n:=24) (s i) ++ a,b,by simp [bytes,len] <;> omega,?_⟩
    unfold record; change _ ++ (List.range d).flatMap field=_
    rw [eq];simp [List.append_assoc]
  have total := wholeRecord.trans sub
  simpa only [Nat.add_assoc] using total

theorem honest_slot (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (p : Nat)
    (batch : ps.card=BATCH) (hp : p<128) :
    supplied (canonicalInput m ps t s) p = capSlot t (ps.sort (·≤·)) p := by
  apply parsed _ (sane m ps t s)
  let xs := ps.sort (·≤·)
  let f (j : Nat) := bytes (n:=32) (capSlot t xs j)
  obtain ⟨a,b,len,eq⟩ := flat_field (List.range 128) f 32 (by intro; simp [f,bytes]) p
    (by simpa only [List.length_range] using hp)
  rw [List.getElem_range] at eq
  refine ⟨xs.flatMap (record t s 16) ++ a,b,?_,?_⟩
  · simp [List.length_flatMap,record_size,List.sum_replicate,xs,batch,BATCH,len]
  · change wideOpening t s ps=_;rw [wideOpening,if_pos batch]
    change _ ++ (List.range 128).flatMap f = _
    rw [eq];simp [List.append_assoc,xs,f]

end CommitGolfCandidate.Late.Check
