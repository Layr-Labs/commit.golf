import CommitGolfCandidate.LateCheckInputs
import CommitGolfCandidate.LateOpenOutput

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
  ⟨node tree LOG_LENGTH 0,ps,m.restrict ps, opening tree s ps⟩

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
  change (opening t s p).length≤_
  rw [opening_size];have le : p.card≤LENGTH := by simpa using Finset.card_le_univ p
  change p.card≤16777216 at le;split <;> omega

private theorem record_field (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (r : Nat) (hr : r<ps.card)
    (normal : ps.card≠BATCH) :
    let x := canonicalInput m ps t s
    ContainsAt x.proof (start x r) (record t s 24 (recordIndex ps r)) := by
  let xs := ps.sort (·≤·)
  have len : xs.length=ps.card := Finset.length_sort ..
  have fit : r<xs.length := by omega
  have wholeRecord := flat_field xs (record t s 24) (24+32*24) (fun i=>record_size t s 24 i) r fit
  have index : recordIndex ps r=xs[r] := by change xs[r]?.getD _=xs[r];rw [List.getElem?_eq_getElem fit];rfl
  obtain ⟨a,b,ha,eq⟩ := wholeRecord
  refine ⟨a,b,?_,?_⟩
  · change a.length = r*(if ps.card = BATCH then 510 else 792); rw [if_neg normal, ha, Nat.mul_comm]
  · change opening t s ps = a++record t s 24 (recordIndex ps r)++b
    rw [opening,if_neg normal,index]
    exact eq

private theorem batch_field (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (r : Nat) (hr : r<ps.card)
    (batch : ps.card=BATCH) :
    let x := canonicalInput m ps t s
    ContainsAt x.proof (start x r) (batchRecord t s (recordIndex ps r)) := by
  let xs := ps.sort (·≤·)
  have len : xs.length=ps.card := Finset.length_sort ..
  have fit : r<xs.length := by omega
  have wholeRecord := flat_field xs (batchRecord t s) 510 (fun i=>batch_record_size t s i) r fit
  have index : recordIndex ps r=xs[r] := by change xs[r]?.getD _=xs[r];rw [List.getElem?_eq_getElem fit];rfl
  obtain ⟨a,b,ha,eq⟩ := wholeRecord
  refine ⟨a,b++(List.range 128).flatMap (fun p => bytes (n:=30) (low240 (capSlot t xs p))),?_,?_⟩
  · change a.length = r*(if ps.card = BATCH then 510 else 792); rw [if_pos batch, ha, Nat.mul_comm]
  · change opening t s ps = a ++ batchRecord t s (recordIndex ps r) ++ _
    rw [opening,if_pos batch,index]
    exact (congrArg (· ++ _) eq).trans (by simp [List.append_assoc,xs])

private theorem batch_record_eq (t : Levels) (s : SaltTape) (i : Index) :
    batchRecord t s i = bytes (n:=24) (s i) ++ Open.bPath t i 0 16 := by
  rw [Open.batch_record_split, ← Open.bpath_append]

private theorem bpath_field (t : Levels) (i : Index) (l : Nat) (hl : l<16) :
    ContainsAt (Open.bPath t i 0 16) (Open.bOff l) (batchSibling t l (Open.mate i l)) := by
  refine ⟨Open.bPath t i 0 l, Open.bPath t i (l+1) (15-l), ?_, ?_⟩
  · rw [Open.bpath_len]; simp [Open.bOff]
  · have e : Open.bPath t i 0 16 = Open.bPath t i 0 l ++ Open.bPath t i (0+l) ((15-l)+1) := by
      rw [← Open.bpath_append, show l+((15-l)+1) = 16 by omega]
    rw [e, Open.bpath_cons, Nat.zero_add, List.append_assoc]

theorem honest_salt (m : Message) (p : Positions) (t : Levels) (s : SaltTape) (r : Nat) (hr : r<p.card) :
    salt (canonicalInput m p t s) r = s (recordIndex p r) := by
  apply parsed _ (sane m p t s)
  let i:=recordIndex p r
  by_cases batch : p.card=BATCH
  · obtain ⟨l,z,len,wholeRecord⟩ := batch_field m p t s r hr batch
    refine ⟨l,Open.bPath t i 0 16++z,len,?_⟩
    rw [wholeRecord,batch_record_eq]; simp only [List.append_assoc]; rfl
  · obtain ⟨l,z,len,wholeRecord⟩ := record_field m p t s r hr batch
    let tail:=(List.range 24).flatMap fun j=>bytes (n:=32) (node t j ((i.val/2^j) ^^^ 1))
    refine ⟨l,tail++z,len,?_⟩
    rw [wholeRecord]
    exact (by simp only [record,List.append_assoc];rfl)

theorem honest_sibling (m : Message) (p : Positions) (t : Levels) (s : SaltTape) (r l : Nat) (hr : r<p.card)
    (hl : l<depth (canonicalInput m p t s))
    (stored : ∀ d j, CutHeight d → j<levelCount d → node t d j = widen (low240 (node t d j))) :
    sibling (canonicalInput m p t s) r l=node t l (((recordIndex p r).val/2^l) ^^^ 1) := by
  let x := canonicalInput m p t s;let i := recordIndex p r
  by_cases batch : p.card=BATCH
  · have hl16 : l<16 := by change l < (if p.card=BATCH then 16 else 24) at hl; rw [if_pos batch] at hl; exact hl
    have sub : ContainsAt (batchRecord t s i) (24+Open.bOff l) (batchSibling t l (Open.mate i l)) := by
      obtain ⟨a,b,len,eq⟩ := bpath_field t i l hl16
      exact ⟨bytes (n:=24) (s i) ++ a,b,by rw [List.length_append,len]; simp [bytes],by rw [batch_record_eq,eq]; simp [List.append_assoc]⟩
    have total := (batch_field m p t s r hr batch).trans sub
    have mb : Open.mate i l < levelCount l := Open.mate_bound i l (by change l<24; omega)
    by_cases low : l<3
    · have v : batchSibling t l (Open.mate i l) = bytes (n:=32) (node t l (Open.mate i l)) := by
        unfold batchSibling; rw [if_pos low]
      rw [v] at total
      unfold sibling; rw [if_neg (by omega)]
      apply parsed _ (sane m p t s)
      have off : start x r+24+32*l = start x r+(24+Open.bOff l) := by
        unfold Open.bOff; rw [if_pos (by omega)]; omega
      rw [off]; exact total
    · have v : batchSibling t l (Open.mate i l) = bytes (n:=30) (low240 (node t l (Open.mate i l))) := by
        unfold batchSibling; rw [if_neg low]
      rw [v] at total
      unfold sibling; rw [if_pos ⟨batch, by omega⟩]
      have off : start x r+120+30*(l-3) = start x r+(24+Open.bOff l) := by
        unfold Open.bOff; split_ifs <;> omega
      rw [off, parsed total (sane m p t s)]
      exact (stored l _ ⟨by omega, by omega⟩ mb).symm
  · obtain ⟨a0,b0,len0,eq0⟩ := record_field m p t s r hr batch
    have hl24 : l<24 := by change l < (if p.card=BATCH then 16 else 24) at hl; rw [if_neg batch] at hl; exact hl
    unfold sibling; rw [if_neg (by tauto)]
    apply parsed _ (sane m p t s)
    let field (j : Nat) := bytes (n:=32) (node t j ((i.val/2^j) ^^^ 1))
    obtain ⟨a,b,len,eq⟩ := flat_field (List.range 24) field 32 (by intro; simp [field,bytes]) l
      (by simpa only [List.length_range] using hl24)
    rw [List.getElem_range] at eq
    have sub : ContainsAt (record t s 24 i) (24+32*l) (field l) := by
      refine ⟨bytes (n:=24) (s i) ++ a,b,by simp [bytes,len] <;> omega,?_⟩
      unfold record; change _ ++ (List.range 24).flatMap field=_
      rw [eq];simp [List.append_assoc]
    have total := (show ContainsAt x.proof (start x r) (record t s 24 i) from ⟨a0,b0,len0,eq0⟩).trans sub
    simpa only [Nat.add_assoc] using total

theorem honest_slot (m : Message) (ps : Positions) (t : Levels) (s : SaltTape) (p : Nat)
    (batch : ps.card=BATCH) (hp : p<128)
    (stored : ∀ d j, CutHeight d → j<levelCount d → node t d j = widen (low240 (node t d j))) :
    supplied (canonicalInput m ps t s) p = capSlot t (ps.sort (·≤·)) p := by
  let xs := ps.sort (·≤·)
  let f (j : Nat) := bytes (n:=30) (low240 (capSlot t xs j))
  obtain ⟨a,b,len,eq⟩ := flat_field (List.range 128) f 30 (by intro; simp [f,bytes]) p
    (by simpa only [List.length_range] using hp)
  rw [List.getElem_range] at eq
  have field : ContainsAt (canonicalInput m ps t s).proof (65280+30*p) (f p) := by
    refine ⟨xs.flatMap (batchRecord t s) ++ a,b,?_,?_⟩
    · simp [List.length_flatMap,batch_record_size,List.sum_replicate,xs,batch,BATCH,len]
    · change opening t s ps=_;rw [opening,if_pos batch]
      change _ ++ (List.range 128).flatMap f = _
      rw [eq];simp [List.append_assoc,xs,f]
  have key : widen (low240 (capSlot t xs p)) = capSlot t xs p := by
    unfold capSlot
    cases e : xs.find? (fun i => i.val / 2^17 == p) with
    | none => exact (stored 17 p ⟨by decide,by decide⟩ hp).symm
    | some i => exact (stored 16 _ ⟨by decide,by decide⟩ (Open.mate_bound i 16 (by decide))).symm
  unfold supplied; rw [parsed field (sane m ps t s)]; exact key

end CommitGolfCandidate.Late.Check
