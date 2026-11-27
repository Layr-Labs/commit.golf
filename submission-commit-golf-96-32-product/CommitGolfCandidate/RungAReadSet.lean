import CommitGolfCandidate.RungAHonest
namespace CommitGolfCandidate.RungA
open CommitGolf
open Late (Trapdoor Levels SaltTape Digest slice nodeAddress levelCount node)
open S4 S4.Open
private theorem recOn (td : Trapdoor) (t : Levels) (s : SaltTape) (b : Bool) (i : Index)
    (salt : slice td (Late.sharedSaltAddr i) 24=s i) (sib : ∀ h n,h<24 → slice td (siblingAddress i h n) 32=sibling t i.val h n) : rawRecord td b i=mainRecord b t s i := by
  simp only [rawRecord,mainRecord,recordPlaces,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro q member;apply congrArg mainBytes
  cases q with
  | none=>simp only [field,fieldAt,salt]
  | some q=>
    obtain ⟨h,n⟩:=q
    simp only [places,List.mem_cons,List.mem_flatMap,List.mem_map,List.mem_range,Option.some.injEq,Prod.mk.injEq,
      reduceCtorEq,false_or] at member
    obtain ⟨u,hu,k,_,e,z⟩:=member
    subst u;subst k
    have within : h<24:=by split at hu <;> omega
    exact congrArg (fun v : Digest=>(if b then bits .byte h else 256,v)) (sib h n within)

private theorem slotOn {o m r td after ps} (f : FusedTrapdoor .twentyFour o m r td)
    (built : Rebuilt .twentyFour o.compression ps td after) (j : Nat) (lim : j<171) :
    slice after (slotAddress (indices ps) j) 32=pairSlot (tree o m r) (indices ps) j := by
  have sorted : (indices ps).Pairwise (·≤·):=Finset.pairwise_sort ..
  rw [orderedSlot _ _ sorted];unfold slotAddress chooseSlot
  have stored (h p : Nat) (low : 4≤h) (high:h≤24) (real:p<levelCount h) :
      slice after (nodeAddress h p) 32=node (tree o m r) h p :=
    (retainedSlot built h p low high real).trans (f.stored _ low high _ real)
  split
  · exact stored 15 _ (by decide) (by decide) (show 2*j+1<342 by omega)
  · split
    · exact stored 15 _ (by decide) (by decide) (show 2*j<342 by omega)
    · exact stored 16 _ (by decide) (by decide) lim

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

private theorem rawOn {o m r td after ps} (f : FusedTrapdoor .twentyFour o m r td)
    (built : Rebuilt .twentyFour o.compression ps td after) :
    rawOutput after ps=S4.opening .byte (tree o m r) (R4.pairSalts r) ps := by
  let xs:=indices ps
  let t:=tree o m r;let s:=R4.pairSalts r
  have recs (b : Bool) : xs.flatMap (rawRecord after b)=(xs.flatMap (record .byte b t s)).flatMap mainBytes := by
    rw [List.flatMap_assoc];apply List.flatMap_congr;intro i hit
    have mem : i∈ps:=by simpa [xs,indices] using hit
    exact recOn after t s b i (saltCorrect f built _) (siblingCorrect f built i mem)
  have allRec (b : Bool) (f : Field) (hf : f∈xs.flatMap (record .byte b t s)) : f.1≠238:=by
    obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp hf;exact recordWhole b t s i f hi
  unfold rawOutput S4.opening;dsimp only
  by_cases b : ps.card=BATCH
  · rw [if_pos b,if_pos b,serializeWhole]
    · rw [List.flatMap_append,List.flatMap_map,recs]
      apply congrArg (_++·);apply List.flatMap_congr;intro j mem
      exact congrArg (fun x : Digest=>mainBytes (240,x)) (slotOn f built j (List.mem_range.mp mem))
    · intro f hf
      rcases List.mem_append.mp hf with left|right
      · exact allRec true f left
      · obtain ⟨j,_,rfl⟩:=List.mem_map.mp right;exact (by decide : (240 : Nat)≠238)
  · rw [if_neg b,if_neg b]
    change xs.flatMap (rawRecord after false)=serialize (xs.flatMap (record .byte false t s))
    rw [serializeWhole _ (allRec false)];exact recs false

theorem writerBytes {o m r td after ps} (f : FusedTrapdoor .twentyFour o m r td)
    (built : Rebuilt .twentyFour o.compression ps td after) :
    codedOutput after ps=S4.actualOpening (tree o m r) (R4.pairSalts r) ps := by
  unfold codedOutput S4.actualOpening;rw [rawOn f built]
end CommitGolfCandidate.RungA
