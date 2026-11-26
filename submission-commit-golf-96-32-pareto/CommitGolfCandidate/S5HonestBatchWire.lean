import CommitGolfCandidate.S5FieldLocation
import CommitGolfCandidate.S5WireBytes
import CommitGolfCandidate.S5HonestCap
namespace CommitGolfCandidate.S5
open CommitGolf
open Late (Levels SaltTape Digest node)
open S5Machine (canonicalInput)
open S5Machine.Reader (window)
theorem honestValue (o : Oracle) (m : Message) (ps : Positions) (s : SaltTape) (r : Nat) (hr : r<ps.card) :
    recordValue (canonicalInput o m ps s) r = m (recordIndex ps r) := by
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


theorem true_completion (x : CheckInput) (t : Levels) (s : SaltTape) (batch : x.positions.card=BATCH)
    (e : x.proof=opening t s x.positions) :
    ∃ trial : Fin 4, complete (packedInput x) trial.val=encode (batchFields t s (S5Machine.Open.indices x.positions)) := by
  have len : (S5Machine.Open.indices x.positions).length=128:=(Finset.length_sort ..).trans batch
  obtain ⟨trial,h⟩:=true_trial t s _ len
  refine ⟨trial,?_⟩;rw [S5Machine.Check.packed_roundtrip x t s batch e]
  simpa only [complete,Nat.mod_mod] using h
private theorem get_node (t : Levels) (h j : Nat) (fit : S5Machine.Open.WireFits t) (small : h≤16) :
    BitVec.ofNat 256 ((node t h j).toNat%2^(bits h))=node t h j:=by
  rw [Nat.mod_eq_of_lt (fit h small j),BitVec.ofNat_toNat,BitVec.setWidth_eq]
private theorem get_sib (t : Levels) (i : Index) (h k : Nat) (fit : S5Machine.Open.WireFits t) (small : h≤16) :
    BitVec.ofNat 256 ((Auth.sibling t i.val h k).toNat%2^(bits h))=Auth.sibling t i.val h k:=get_node t _ _ fit small

theorem honest_batch_wire (o : Oracle) (m : Message) (ps : Positions) (s : SaltTape) (batch : ps.card=BATCH) :
    let x:=canonicalInput o m ps s
    ∃ trial : Fin 4,Auth.BatchValid o.compression (batchView x trial) x.commitment := by
  let x:=canonicalInput o m ps s
  let t:=S5Hiding.tree o.compression m s
  let xs:=S5Machine.Open.indices ps
  let num:=encode (batchFields t s xs)
  have fit:=S5Machine.Open.honest_fits o.compression m s
  have len : xs.length=128:=(Finset.length_sort ..).trans batch
  obtain ⟨q,eqv⟩:=true_completion x t s batch rfl
  have eqn : complete (packedInput x) q.val=num:=eqv
  let v:=batchView x q
  have idx (r : Nat) (hr : r<xs.length) : v.idx r=xs[r]:=by
    change (xs[r]?.getD _)=xs[r];rw [List.getElem?_eq_getElem hr];rfl
  refine ⟨q,?_⟩;apply Auth.honestBatch o.compression m s t (Auth.honestTree ..) v
  · intro r hr
    have small : r<xs.length:=by omega
    let i:=xs[r]
    have rx : v.idx r=i:=idx r small
    have row:=record_located t s xs r small
    have saltData:= (row.nested (salt_located t s i)).get
    change window num (4030*r+0) 192=(s i).toNat%2^192 at saltData
    have peer (h k : Nat) (bh : h<15) (bk : k<S4.radix h-1) :
        BitVec.ofNat 256 (window num (4030*r+layerBits h+k*bits h) (bits h))=Auth.sibling t i.val h k := by
      have data:=(row.nested (peer_located t s i h k bh bk)).get
      change window num (4030*r+(layerBits h+k*bits h)) _=_ at data
      rw [Nat.add_assoc,data];exact get_sib t i h k fit (by omega)
    refine ⟨?_,honestValue o m ps s r (by change r<ps.card;rw [batch];exact hr),?_⟩
    · change BitVec.ofNat 192 (window (complete (packedInput x) q.val) (4030*r) 192)=_
      rw [eqn,rx,show window num (4030*r) 192=_ from saltData,Nat.mod_eq_of_lt (s i).isLt,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    · intro h bh;rw [rx]
      change (BitVec.ofNat 256 (window (complete (packedInput x) q.val) _ _),if h=0 then _ else _) =_
      rw [eqn];apply Prod.ext
      · simpa only [Auth.truePeers,Nat.zero_mul,Nat.add_zero] using peer h 0 bh (by unfold S4.radix;split <;> decide)
      · by_cases zero : h=0
        · subst h;simpa only [Auth.truePeers,bits,ite_true,Nat.one_mul] using peer 0 1 (by decide) (by decide)
        · simp only [Auth.truePeers,if_neg zero]
  · apply Auth.canonicalSlots t ps batch v idx
    intro j hj
    have slotData:=(slot_located t s xs len j hj).get
    change window num (515840+230*j) 230=(slot t xs j).2%2^230 at slotData
    change BitVec.ofNat 256 (window (complete (packedInput x) q.val) (515840+230*j) 230)=_
    rw [eqn,slotData]
    change BitVec.ofNat 256 ((slot t xs j).2%2^230)=BitVec.ofNat 256 (slot t xs j).2
    rw [S5Machine.Open.slot_eq]
    let l:=(S5Machine.Open.flags xs j).1;let r:=(S5Machine.Open.flags xs j).2
    let d:=S5Machine.Open.slotLevel l r
    have bound : d≤16:=by unfold d S5Machine.Open.slotLevel;split <;> decide
    have w : bits d=230:=by unfold d S5Machine.Open.slotLevel;split <;> decide
    have ready:=fit d bound (S5Machine.Open.slotIndex j l r)
    rw [w] at ready;exact congrArg (BitVec.ofNat 256) (Nat.mod_eq_of_lt ready)
end CommitGolfCandidate.S5
