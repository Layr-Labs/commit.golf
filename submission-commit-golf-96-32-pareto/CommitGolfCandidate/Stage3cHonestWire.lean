import CommitGolfCandidate.Stage3cHonestTree
import CommitGolfCandidate.Stage3cWireBytes
import CommitGolfCandidate.Stage3cBatchCharge
import CommitGolfCandidate.Stage3cCapField
import CommitGolfCandidate.Stage3cBatchFrame
import CommitGolfCandidate.Stage3cCachedTree
/-! Honest openings of the ptr image are wire-valid: every record of the canonical proof
authenticates to the committed root, and the batch proof passes the bucket and cap tests. -/
set_option Elab.async false
namespace CommitGolfCandidate.Pw
open CommitGolf
open Late (Levels SaltTape Digest node)

/-- The checker input of an honest commitment and opening. -/
noncomputable def canonicalInput (o : Oracle) (m : Message) (ps : Positions) (salt : SaltTape) : CheckInput :=
  let tree:=Chained.Binary.treeM (M:=Id) o.compression m salt
  ⟨node tree LOG_LENGTH 0,ps,m.restrict ps,Chained.Binary.opening tree salt ps⟩

namespace Auth
open Geo (width radix nodeIndex)

structure HonestTree (H : Compression) (m : Message) (s : SaltTape) (t : Levels) : Prop where
  leaf : ∀ i : Index,node t 0 i.val=Late.leaf H (i.val.testBit 0) (s i) (m i)
  parent : ∀ h<24,∀ j < width (h+1),node t (h+1) j=compressRow H (h+1) ((row h
    (node t h (2*j)) (node t h (2*j+1)) 0))
  missing : ∀ h≤24,∀ j,width h≤j → node t h j=0

private theorem finLookup {α : Type} (n : Nat) (f : Fin n→α) (i : Fin n) (z : α) :
    ((List.finRange n).map f)[i.val]?.getD z=f i := by
  have b : i.val<(List.finRange n).length:=by rw [List.length_finRange];exact i.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem b,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

private theorem count_width (h : Nat) (b : h≤24) : Chained.BinaryMachine.levelCount h=width h := by
  rw [Geo.width_le h b];rfl

theorem honestTree (H : Compression) (m : Message) (s : SaltTape) :
    HonestTree H m s (Chained.Binary.treeM (M:=Id) H m s) := by
  let t:=Chained.Binary.treeM (M:=Id) H m s
  let base : Nat→Digest:=fun k=>(Chained.BinaryMachine.initialList H m s)[k]?.getD 0
  have eqn (h j : Nat) (limit : h≤24) (inside : j<width h) :
      node t h j=Chained.BinaryMachine.treeNode H base h j :=
    Chained.BinaryMachine.fixed_tree_node H m s h j limit (by rw [count_width h limit];exact inside)
  constructor
  · intro i
    rw [eqn 0 i.val (by decide) (by rw [Geo.width_le 0 (by decide)];exact i.isLt)]
    exact finLookup LENGTH (fun j=>Late.leaf H (j.val.testBit 0) (s j) (m j)) i 0
  · intro h bh j bj
    have wl : width h=2*width (h+1):=by rw [Geo.width_le h (by omega),Geo.width_le (h+1) (by omega),
      show 24-h=(24-(h+1))+1 by omega,Nat.pow_succ];omega
    rw [eqn (h+1) j (by omega) bj,eqn h (2*j) (by omega) (by omega),eqn h (2*j+1) (by omega) (by omega),row_parent]
    rfl
  · intro h bh j out
    have len:=Chained.BinaryMachine.layer_size H m s h bh
    rw [count_width h bh] at len
    show node (Chained.Binary.treeM (M:=Id) H m s) h j=0
    rw [Chained.BinaryMachine.model_cached]
    unfold node
    rw [List.getElem?_eq_none (by omega)];rfl

def peerIndex (j : Nat) := 2*(j/2)+(1-j%2)
theorem peer_xor (j : Nat) : j ^^^ 1=peerIndex j := by
  unfold peerIndex
  by_cases even : j%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega

def truePeers (t : Levels) (i : Index) (h : Nat) : Peers :=
  (node t h (peerIndex (nodeIndex i.val h)),0)

theorem trueStep (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree H m s t) (i : Index) (h : Nat) (lim : h<24) :
    compressRow H (h+1) ((payload (lane h (nodeIndex i.val h)) (node t h (nodeIndex i.val h)) (truePeers t i h)))=
      node t (h+1) (nodeIndex i.val (h+1)) := by
  let j:=nodeIndex i.val h
  have up : nodeIndex i.val (h+1)=j/2:=Geo.nextIndex _ _
  rw [up,tree.parent h lim _ (by rw [←up];exact indexInside i (h+1))]
  apply congrArg (compressRow H (h+1))
  exact (binaryPayload h j (node t h)).trans rfl

theorem honestRecord (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree H m s t) (v : View) (r n : Nat) (limit : n≤24)
    (salt : v.salt r=s (v.idx r)) (value : v.entry r=m (v.idx r))
    (peers : ∀ h<n,v.peers r h=truePeers t (v.idx r) h) :
    recordAt H v r n (v.peers r)=node t n (nodeIndex (v.idx r).val n) := by
  induction n with
  | zero=>change Late.leaf H _ _ _=node t 0 _
          rw [salt,value];simpa only [nodeIndex,Geo.span,pow_zero,Nat.div_one] using (tree.leaf (v.idx r)).symm
  | succ n ih=>
    change compressRow H (n+1) ((payload _ (recordAt H v r n _) _))=_
    rw [ih (by omega) (fun h bh=>peers h (by omega)),peers n (by omega)]
    exact trueStep H m s t tree (v.idx r) n (by omega)

def First (v : View) (u : Nat) := (List.range 128).find? (fun r=>bucket v r==u)

private theorem found {v : View} {u r : Nat} (e : First v u=some r) : r<128 ∧ bucket v r=u :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some e),beq_iff_eq.mp (List.find?_some (p:=fun r=>bucket v r==u) e)⟩

private theorem absent {v : View} {u : Nat} (e : First v u=none) {r : Nat} (hr : r<128) : bucket v r≠u :=
  fun eqv=>(List.find?_eq_none.mp e r (List.mem_range.mpr hr)) (beq_iff_eq.mpr eqv)

def SlotRule (t : Levels) (v : View) := ∀ j<256,∀ y : Digest,
  ((∀ r<128,bucket v r/2≠j) → node t 16 j=y) →
  (∀ r<128,bucket v r/2=j → node t 15 (2*j+(1-bucket v r%2))=y) → v.slot j=y

private theorem bucket_div (i : Index) : nodeIndex i.val 15=i.val/32768 := rfl

theorem canonicalSlots (t : Levels) (ps : Positions) (b : ps.card=128) (v : View)
    (idx : ∀ r (hr : r<(ps.sort (·≤·)).length),v.idx r=(ps.sort (·≤·))[r])
    (slots : ∀ j<256,v.slot j=BitVec.ofNat 256 (Chained.Binary.slot t (ps.sort (·≤·)) j).value) : SlotRule t v := by
  intro j bj y fallback hit
  rw [slots j bj]
  let xs:=ps.sort (·≤·)
  have size : xs.length=128:=(Finset.length_sort ..).trans b
  have witness (n : Nat) (h : xs.any (fun i=>i.val/32768==n)) :
      ∃ r<128,bucket v r=n := by
    obtain ⟨i,hi,good⟩:=List.any_eq_true.mp h
    obtain ⟨r,hr,e⟩:=List.getElem_of_mem hi
    exact ⟨r,by omega,(congrArg (fun i : Index=>nodeIndex i.val 15) ((idx r hr).trans e)).trans (beq_iff_eq.mp good)⟩
  have absent (n : Nat) (h : xs.any (fun i=>i.val/32768==n)=false) (r : Nat) (hr : r<128) :
      bucket v r≠n := by
    intro wrong
    have ir : r<xs.length := by omega
    have e : xs.any (fun i=>i.val/32768==n)=true :=
      List.any_eq_true.mpr ⟨xs[r],List.getElem_mem ir,beq_iff_eq.mpr ((congrArg (fun i : Index=>nodeIndex i.val 15) (idx r ir).symm).trans wrong)⟩
    simp_all
  change BitVec.ofNat 256 (Chained.Binary.slot t xs j).value=y
  unfold Chained.Binary.slot
  cases l : xs.any (fun i=>i.val/32768==2*j) <;> cases rr : xs.any (fun i=>i.val/32768==2*j+1)
  · simpa only [l,rr,Bool.false_or,Bool.false_eq_true,ite_false,BitVec.ofNat_toNat,BitVec.setWidth_eq] using
      fallback (fun r hr=>by have :=absent _ l r hr;have :=absent _ rr r hr;omega)
  · obtain ⟨r,hr,found⟩:=witness _ rr
    have v:=hit r hr (by omega);simp [l,rr,found] at v ⊢;exact v
  · obtain ⟨r,hr,found⟩:=witness _ l
    have v:=hit r hr (by omega);simp [l,rr,found] at v ⊢;exact v
  · obtain ⟨r,hr,found⟩:=witness _ rr
    have v:=hit r hr (by omega);simp [l,rr,found] at v ⊢;exact v

theorem honestBatch (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree H m s t) (v : View) (fields : ∀ r<128,
      v.salt r=s (v.idx r) ∧ v.entry r=m (v.idx r) ∧ ∀ h<15,v.peers r h=truePeers t (v.idx r) h)
    (slot : SlotRule t v) : BatchValid H v (node t 24 0) := by
  let tab:=lower H v
  have lo (r : Nat) (br : r<128) : tab r=node t 15 (bucket v r):=
    honestRecord H m s t tree v r 15 (by decide) (fields r br).1 (fields r br).2.1 (fields r br).2.2
  have lookup (u r : Nat) (e : First v u=some r) : tab r=node t 15 u:= (lo r (found e).1).trans (congrArg (node t 15) (found e).2)
  have pair (j : Nat) (bj : j<256) : batchCap H v j=node t 16 j := by
    have par := tree.parent 15 (by decide) j (by rw [Geo.width_le 16 (by decide)];exact bj)
    change node t 16 j=compressRow H 16 ((Late.parentBlock (node t 15 (2*j)) (node t 15 (2*j+1)))) at par
    change mergePair H ((First v (2*j)).map tab) ((First v (2*j+1)).map tab) (v.slot j)=_
    cases l : First v (2*j) with
    | none=>
      cases rr : First v (2*j+1) with
      | none=>
        apply slot j bj _ (fun _=>rfl)
        intro r br e;have hl:=absent l br;have hr:=absent rr br;omega
      | some r=>
        have sl : v.slot j=node t 15 (2*j):=slot j bj _ (fun e=>by have a:=found rr;have:=e r a.1;omega)
          (fun q bq e=>by have:=absent l bq;congr 1;omega)
        simp only [mergePair,Option.map_none,Option.map_some,Option.isNone_none,Option.isNone_some,
          Bool.true_and,Bool.false_eq_true,ite_false,Option.getD_none,Option.getD_some,lookup _ _ rr,sl]
        exact par.symm
    | some a=>
      cases rr : First v (2*j+1) with
      | none=>
        have sl : v.slot j=node t 15 (2*j+1):=slot j bj _ (fun e=>by have hb:=found l;have:=e a hb.1;omega)
          (fun q bq e=>by have:=absent rr bq;congr 1;omega)
        simp only [mergePair,Option.map_none,Option.map_some,Option.isNone_none,Option.isNone_some,
          Bool.false_and,Bool.false_eq_true,ite_false,Option.getD_none,Option.getD_some,lookup _ _ l,sl]
        exact par.symm
      | some b=>
        simp only [mergePair,Option.map_some,Option.isNone_some,Bool.false_and,Bool.false_eq_true,ite_false,
          Option.getD_some,lookup _ _ l,lookup _ _ rr]
        exact par.symm
  constructor
  · intro r br
    change (First v (bucket v r)).map tab=some (tab r)
    cases e : First v (bucket v r) with
    | none=>exact False.elim ((absent e br) rfl)
    | some q=>rw [Option.map_some,lookup _ _ e,lo r br]
  · have upperEq (k j : Nat) (limit : k≤8) : upper H (batchCap H v) k j=node t (16+k) j := by
      induction k generalizing j with
      | zero=>
        by_cases bj : j<256
        · exact (if_pos bj).trans (pair j bj)
        · exact (if_neg bj).trans (tree.missing 16 (by decide) j (by rw [Geo.width_le 16 (by decide)];omega)).symm
      | succ k ih=>
        rw [upper]
        have height : 16+(k+1)=17+k:=by omega
        rw [height]
        by_cases bj : j<width (17+k)
        · rw [if_pos bj,ih _ (by omega),ih _ (by omega)]
          have e:=tree.parent (16+k) (by omega) j (by simpa only [show 16+k+1=17+k by omega] using bj)
          simpa only [show 16+k+1=17+k by omega,row_block] using e.symm
        · rw [if_neg bj];exact (tree.missing (17+k) (by omega) j (by omega)).symm
    exact upperEq 8 0 (by decide)
end Auth

open Chained.BinaryMachine.Writer (widths encode_bound encode_append)
open Chained.BinaryMachine.Reader (window)
abbrev Field := Chained.Binary.Field

theorem field_at (pre rest : List Field) (w v : Nat) :
    window (Chained.Binary.encode (pre++⟨w,v⟩::rest)) (widths pre) w=v%2^w := by
  rw [encode_append]
  unfold window
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (encode_bound pre),Nat.zero_add,Chained.Binary.encode,
    Nat.add_mul_mod_self_left,Nat.mod_mod]

def Located (whole : List Field) (at_ : Nat) (part : List Field) := ∃ pre rest : List Field,widths pre=at_ ∧ whole=pre++(part++rest)
theorem Located.nested {x y z a b} (f : Located x a y) (g : Located y b z) : Located x (a+b) z := by
  obtain ⟨pre,post,pa,e⟩:=f;obtain ⟨l,r,lb,g⟩:=g
  exact ⟨pre++l,r++post,by simp [widths,←pa,←lb],by rw [e,g];simp [List.append_assoc]⟩
theorem Located.append {xs p s} (loc : Located xs p s) (tail : List Field) : Located (xs++tail) p s := by
  obtain ⟨pre,post,width,eq⟩:=loc;exact ⟨pre,post++tail,width,by rw [eq];simp [List.append_assoc]⟩
theorem Located.prepend {xs p s} (loc : Located xs p s) (head : List Field) : Located (head++xs) (widths head+p) s := by
  obtain ⟨pre,post,width,eq⟩:=loc;exact ⟨head++pre,post,by simp [widths,←width],by rw [eq,List.append_assoc]⟩
theorem Located.get {fs at_ w v} (loc : Located fs at_ [⟨w,v⟩]) : window (Chained.Binary.encode fs) at_ w=v%2^w := by
  obtain ⟨pre,tail,eq,h⟩:=loc;rw [←eq,h];exact field_at pre tail w v
private theorem flat_at {α} (xs : List α) (f : α→List Field) (j : Nat) (hj : j<xs.length) :
    Located (xs.flatMap f) (widths ((xs.take j).flatMap f)) (f xs[j]) := by
  induction xs generalizing j with
  | nil=>simp at hj
  | cons a as ih=>
    cases j with
    | zero=>exact ⟨[],as.flatMap f,rfl,rfl⟩
    | succ j=>
      have small : j<as.length:=by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj
      have h:=(ih j small).prepend (f a)
      simpa only [List.flatMap_cons,List.take_succ_cons,List.getElem_cons_succ,widths,List.map_append,List.sum_append] using h
private theorem map_at (xs : List Nat) (f : Nat→Field) (j : Nat) (hj : j<xs.length) :
    Located (xs.map f) (widths ((xs.take j).map f)) [f xs[j]] := by
  have lift (as : List Nat) : as.flatMap (fun k=>[f k])=as.map f := by induction as <;> simp_all
  simpa only [lift] using flat_at xs (fun k=>[f k]) j hj

def peerField (t : Levels) (i : Index) (level : Nat) : Field :=
  ⟨if level=0 then 256 else Chained.wireWidth (Chained.Binary.height (level-1)),
   (node t level ((i.val/2^level) ^^^ 1)).toNat⟩
theorem peer_bits (t : Levels) (i : Index) (level : Nat) : (peerField t i level).bits=bits level := by
  cases level <;> rfl
theorem record_shape (t : Levels) (s : SaltTape) (i : Index) :
    Chained.Binary.recordFields t s i=⟨192,(s i).toNat⟩::(List.range 15).map (peerField t i) := rfl

theorem record_located (tree : Levels) (salt : SaltTape) (xs : List Index) (r : Nat) (hr : r<xs.length) :
    Located (batchFields tree salt xs) (3780*r) (Chained.Binary.recordFields tree salt xs[r]) := by
  have f:=(flat_at xs (fun i=>Chained.Binary.recordFields tree salt i) r hr).append ((List.range 256).map (Chained.Binary.slot tree xs))
  have len:=Chained.BinaryMachine.Open.record_width_sum tree salt (xs.take r)
  rw [List.length_take,Nat.min_eq_left hr.le] at len
  rw [←len];exact f

theorem salt_located (t s i) : Located (Chained.Binary.recordFields t s i) 0 [⟨192,(s i).toNat⟩] :=
  ⟨[],(List.range 15).map (peerField t i),rfl,rfl⟩

theorem peer_located (t s) (i : Index) (h : Nat) (bh : h<15) :
    Located (Chained.Binary.recordFields t s i) (layerBits h) [⟨bits h,(node t h ((i.val/2^h) ^^^ 1)).toNat⟩] := by
  have h2:=(map_at (List.range 15) (peerField t i) h (by simpa only [List.length_range] using bh)).prepend [⟨192,(s i).toNat⟩]
  simp only [List.take_range,Nat.min_eq_left bh.le,List.getElem_range] at h2
  have width : widths [(⟨192,(s i).toNat⟩ : Field)]+widths ((List.range h).map (peerField t i))=layerBits h := by
    simp only [widths,layerBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_map,Nat.add_zero]
    congr 1;apply congrArg;apply List.map_congr_left;intro l _;exact peer_bits t i l
  rw [width] at h2
  have e : peerField t i h=⟨bits h,(node t h ((i.val/2^h) ^^^ 1)).toNat⟩:=by
    cases h <;> rfl
  rw [e] at h2;exact h2

theorem slot_located (tree : Levels) (salt : SaltTape) (xs : List Index) (len : xs.length=128) (j : Nat) (hj : j<256) :
    Located (batchFields tree salt xs) (483840+230*j) [Chained.Binary.slot tree xs j] := by
  have f:=(map_at (List.range 256) (Chained.Binary.slot tree xs) j (by simpa only [List.length_range] using hj)).prepend
    (Chained.BinaryMachine.Open.recordFields tree salt xs)
  rw [Chained.BinaryMachine.Open.record_width_sum,len,List.take_range,Nat.min_eq_left hj.le,List.getElem_range] at f
  have width : widths ((List.range j).map (Chained.Binary.slot tree xs))=230*j:=by
    simp [widths,Chained.Binary.slot,List.map_map,Function.comp_def,Nat.mul_comm]
  rw [width] at f;exact f

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

private theorem get_node (t : Levels) (h j : Nat) (fit : Chained.BinaryMachine.Open.WireFits t) (small : h≤16) :
    BitVec.ofNat 256 ((node t h j).toNat%2^(bits h))=node t h j:=by
  rw [bits_eq,Nat.mod_eq_of_lt (fit h small j),BitVec.ofNat_toNat,BitVec.setWidth_eq]

attribute [local irreducible] Late.node Chained.Binary.treeM Chained.Binary.opening in
set_option maxRecDepth 20000 in
theorem honest_batch_wire (o : Oracle) (m : Message) (ps : Positions) (s : SaltTape) (batch : ps.card=BATCH) :
    let x:=canonicalInput o m ps s
    Auth.BatchValid o.compression (batchView x) x.commitment := by
  let x:=canonicalInput o m ps s
  let t:=Chained.Binary.treeM (M:=Id) o.compression m s
  let xs:=Chained.BinaryMachine.Open.indices ps
  let num:=Chained.Binary.encode (batchFields t s xs)
  have fit:=Chained.BinaryMachine.Open.honest_fits o.compression m s
  have len : xs.length=128:=(Finset.length_sort ..).trans batch
  have eqn : packedInput x=num%2^wireBits:=Chained.BinaryMachine.Check.packed_roundtrip x t s batch rfl
  have win (a w : Nat) (inside : a+w≤wireBits) : window (packedInput x) a w=window num a w := by
    rw [eqn];exact Chained.BinaryMachine.Check.window_mod num wireBits a w inside
  let v:=batchView x
  have idx (r : Nat) (hr : r<xs.length) : v.idx r=xs[r]:=by
    change (xs[r]?.getD _)=xs[r];rw [List.getElem?_eq_getElem hr];rfl
  apply Auth.honestBatch o.compression m s t (Auth.honestTree ..) v
  · intro r hr
    have small : r<xs.length:=by omega
    let i:=xs[r]
    have rx : v.idx r=i:=idx r small
    have row:=record_located t s xs r small
    have saltData:= (row.nested (salt_located t s i)).get
    change window num (3780*r+0) 192=(s i).toNat%2^192 at saltData
    refine ⟨?_,honestValue o m ps s r (by change r<ps.card;rw [batch];exact hr),?_⟩
    · change BitVec.ofNat 192 (window (packedInput x) (3780*r) 192)=_
      rw [win _ _ (by unfold wireBits;omega),rx,show window num (3780*r) 192=_ from saltData,Nat.mod_eq_of_lt (s i).isLt,
        BitVec.ofNat_toNat,BitVec.setWidth_eq]
    · intro h bh;rw [rx]
      have width : layerBits h+bits h≤3780 := (by decide +kernel : ∀ j : Fin 15,layerBits j.val+bits j.val≤3780) ⟨h,bh⟩
      have data:=(row.nested (peer_located t s i h bh)).get
      change (BitVec.ofNat 256 (window (packedInput x) (3780*r+layerBits h) (bits h)),0)=_
      rw [win _ _ (by unfold wireBits;omega),data,get_node t h _ fit (by omega)]
      unfold Auth.truePeers;rw [Auth.peer_xor];rfl
  · apply Auth.canonicalSlots t ps batch v idx
    intro j hj
    have slotData:=(slot_located t s xs len j hj).get
    change window num (483840+230*j) 230=(Chained.Binary.slot t xs j).value%2^230 at slotData
    change BitVec.ofNat 256 (window (packedInput x) (483840+230*j) 230)=_
    rw [win _ _ (by unfold wireBits;omega),slotData]
    change BitVec.ofNat 256 ((Chained.Binary.slot t xs j).value%2^230)=BitVec.ofNat 256 (Chained.Binary.slot t xs j).value
    rw [Chained.BinaryMachine.Open.slot_eq]
    let l:=(Chained.BinaryMachine.Open.flags xs j).1;let r:=(Chained.BinaryMachine.Open.flags xs j).2
    let d:=Chained.BinaryMachine.Open.slotLevel l r
    have bound : d≤16:=by unfold d Chained.BinaryMachine.Open.slotLevel;split <;> decide
    have w : Chained.BinaryMachine.levelBits d=230:=by unfold d Chained.BinaryMachine.Open.slotLevel;split <;> decide
    have ready:=fit d bound (Chained.BinaryMachine.Open.slotIndex j l r)
    rw [w] at ready;exact congrArg (BitVec.ofNat 256) (Nat.mod_eq_of_lt ready)
end CommitGolfCandidate.Pw
