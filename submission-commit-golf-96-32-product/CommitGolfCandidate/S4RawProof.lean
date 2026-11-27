import CommitGolfCandidate.S4OpenInput
import CommitGolfCandidate.S4RecordWire
namespace CommitGolfCandidate.S4.Open
open CommitGolf
open Late (Trapdoor TrapdoorAgrees Levels SaltTape slice nodeAddress rowAddress Digest)

def siblingAddress (i : Index) (h n : Nat) :=
  rowAddress h (nodeIndex i.val (h+1))+32*((childPos i.val h+n+1)%radix h)
def slotAddress (xs : List Index) (j : Nat) :=
  if marks xs (2*j) then Late.nodeAddress 15 (2*j+1) else if marks xs (2*j+1) then Late.nodeAddress 15 (2*j)
  else Late.nodeAddress 16 j

def field (td : Trapdoor) (batch : Bool) (i : Index) : Place→Field
  | none=>(192,(slice td (Late.sharedSaltAddr i) 24).setWidth 256)
  | some (h,n)=>(if batch then bits .byte h else 256,slice td (siblingAddress i h n) 32)

def rawRecord (td : Trapdoor) (batch : Bool) (i : Index) :=
  (places batch).flatMap fun q=>mainBytes (field td batch i q)

def rawOutput (td : Trapdoor) (ps : Positions) : Proof :=
  let xs:=indices ps
  if ps.card=BATCH then xs.flatMap (rawRecord td true) ++ (List.range 171).flatMap
    (fun j=>mainBytes (240,slice td (slotAddress xs j) 32))
  else xs.flatMap (rawRecord td false)

theorem rawRecordCorrect (td : Trapdoor) (t : Levels) (s : SaltTape) (agree : TrapdoorAgrees td t s)
    (b : Bool) (i : Index) : rawRecord td b i=mainRecord b t s i := by
  simp only [rawRecord,mainRecord,recordPlaces,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro q member;apply congrArg mainBytes
  cases q with
  | none=>simp only [field,fieldAt,agree.salt]
  | some q=>
    obtain ⟨h,n⟩:=q
    simp only [places,List.mem_cons,List.mem_flatMap,List.mem_map,List.mem_range,Option.some.injEq,Prod.mk.injEq,
      reduceCtorEq,false_or] at member
    obtain ⟨u,hu,k,_,e,z⟩:=member
    subst u;subst k
    have within : h<24:=by split at hu <;> omega
    exact congrArg (fun v : Digest=>(if b then bits .byte h else 256,v)) (sourceSibling td t s agree i h n within)

theorem rawSlotCorrect (td : Trapdoor) (ps : Positions) (t : Levels) (s : SaltTape) (agree : TrapdoorAgrees td t s)
    (j : Nat) (bj : j<171) : slice td (slotAddress (indices ps) j) 32=pairSlot t (indices ps) j := by
  have sorted : (indices ps).Pairwise (·≤·):=Finset.pairwise_sort ..
  rw [orderedSlot t _ sorted]
  unfold slotAddress chooseSlot
  split
  · exact agree.nodes 15 (by decide) _ (show 2*j+1<342 by omega)
  · split
    · exact agree.nodes 15 (by decide) _ (show 2*j<342 by omega)
    · exact agree.nodes 16 (by decide) j bj

private theorem serializeWhole (fs : List Field) (whole : ∀ f∈fs,f.1≠238) : serialize fs=fs.flatMap mainBytes := by
  have z : (fs.filter fun f=>f.1==238)=[]:=by
    apply List.filter_eq_nil_iff.mpr;intro f member;exact fun e=>whole f member (beq_iff_eq.mp e)
  simp only [serialize,z,List.map_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,show 7/8=0 by decide,List.range_zero,List.append_nil] <;> rfl

private theorem recordWhole (b : Bool) (t : Levels) (s : SaltTape) (i : Index) (f : Field) (member : f∈record .byte b t s i) : f.1≠238 := by
  rw [recordPlaces,List.mem_map] at member
  obtain ⟨q,_,rfl⟩:=member
  cases q with
  | none=>exact (by decide : (192 : Nat)≠238)
  | some p=>obtain ⟨h,k⟩:=p;change (if b then bits .byte h else 256)≠238
            have no : ¬(Profile.byte=Profile.packed ∧ 6≤h):=fun t=>by cases t.1
            cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,bits,if_neg no] <;> (try split_ifs) <;> decide

theorem rawOutputCorrect (td : Trapdoor) (ps : Positions) (t : Levels) (s : SaltTape) (agree : TrapdoorAgrees td t s) :
    rawOutput td ps=opening .byte t s ps := by
  let xs:=indices ps
  have recs (b : Bool) : xs.flatMap (rawRecord td b)=(xs.flatMap (record .byte b t s)).flatMap mainBytes := by
    rw [List.flatMap_assoc];apply List.flatMap_congr;intro i _;exact rawRecordCorrect td t s agree b i
  have allRec (b : Bool) (f : Field) (hf : f∈xs.flatMap (record .byte b t s)) : f.1≠238:=by
    obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp hf;exact recordWhole b t s i f hi
  unfold rawOutput opening;dsimp only
  by_cases b : ps.card=BATCH
  · rw [if_pos b,if_pos b,serializeWhole]
    · rw [List.flatMap_append,List.flatMap_map,recs]
      apply congrArg (_++·);apply List.flatMap_congr;intro j mem
      exact congrArg (fun x : Digest=>mainBytes (240,x)) (rawSlotCorrect td ps t s agree j (List.mem_range.mp mem))
    · intro f hf
      rcases List.mem_append.mp hf with left|right
      · exact allRec true f left
      · obtain ⟨j,_,rfl⟩:=List.mem_map.mp right;exact (by decide : (240 : Nat)≠238)
  · rw [if_neg b,if_neg b]
    change xs.flatMap (rawRecord td false)=serialize (xs.flatMap (record .byte false t s))
    rw [serializeWhole _ (allRec false)];exact recs false
def codedOutput (td : Trapdoor) (ps : Positions) :=
  if ps.card=BATCH then Carry.packed (rawOutput td ps) else rawOutput td ps
theorem codedCorrect (td : Trapdoor) (ps : Positions) (t : Levels) (s : SaltTape) (agree : TrapdoorAgrees td t s) :
    codedOutput td ps=actualOpening t s ps := by
  unfold codedOutput actualOpening;rw [rawOutputCorrect _ _ _ _ agree]
end CommitGolfCandidate.S4.Open
