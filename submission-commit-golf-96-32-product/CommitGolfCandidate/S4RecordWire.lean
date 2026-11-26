import CommitGolfCandidate.S4HonestFields
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest bytes)

abbrev Place := Option (Nat×Nat)
def places (b : Bool) : List Place :=
  none::(List.range (if b then 15 else 24)).flatMap fun h=>(List.range (radix h-1)).map fun n=>some (h,n)
def wireWidth (b : Bool) : Place→Nat
  | none=>24
  | some (h,_)=>fieldBytes b h
def fieldAt (b : Bool) (t : Levels) (s : SaltTape) (i : Index) : Place→Field
  | none=>(192,(s i).setWidth 256)
  | some (h,k)=>(if b then bits .byte h else 256,sibling t i.val h k)

theorem recordPlaces (b : Bool) (t : Levels) (s : SaltTape) (i : Index) :
    record .byte b t s i=(places b).map (fieldAt b t s i) := by
  simp only [record,places,List.map_cons,List.map_flatMap,List.map_map,Function.comp_def,fieldAt]

private theorem widthsAt (b : Bool) (q : Place) (hq : q∈places b) (t : Levels) (s : SaltTape) (i : Index) :
    (fieldAt b t s i q).1=8*wireWidth b q := by
  cases q with
  | none=>rfl
  | some q=>
    obtain ⟨h,n⟩:=q
    simp only [places,List.mem_cons,List.mem_flatMap,List.mem_map,List.mem_range,Option.some.injEq,Prod.mk.injEq,
      reduceCtorEq,false_or] at hq
    obtain ⟨h',lh,n',_,a,b'⟩:=hq
    subst h';subst n';cases b <;> simp [fieldAt,wireWidth,fieldBytes,bits] at lh ⊢ <;> split_ifs <;> omega

theorem baseField (n : Nat) (d : Digest) : mainBytes (8*n,d)=bytes (n:=n) (d.setWidth (8*n)) := by
  apply List.ext_getElem
  · simp [mainBytes,bytes]
  · intro j a b
    have limit : j<n:=by simpa [bytes] using b
    simp only [mainBytes,bytes,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [BitVec.extractLsb'_setWidth_of_le (by omega)]

private theorem locate {α : Type} (xs : List α) (f : α→Proof) (r : Nat) (br : r<xs.length) :
    ContainsAt (xs.flatMap f) ((xs.take r).flatMap f).length (f xs[r]) := by
  induction xs generalizing r with
  | nil=>simp at br
  | cons x xs ih=>
    cases r with
    | zero=>exact ⟨[],xs.flatMap f,rfl,rfl⟩
    | succ r=>
      obtain ⟨a,b,eq,e⟩:=ih r (by simpa using br)
      refine ⟨f x++a,b,by simp [eq],?_⟩
      simp only [List.flatMap_cons,e,List.getElem_cons_succ,List.append_assoc]

def placePos (h n : Nat) := if h=0 then 1+n else 2+h
private theorem directory : ∀ b : Bool,∀ h : Fin 24,∀ n : Fin 2,
  h.val<(if b then 15 else 24) → n.val<radix h.val-1 →
    let k:=placePos h n
    k<(places b).length ∧ (places b)[k]?=some (some (h.val,n.val)) ∧
    (((places b).take k).map (wireWidth b)).sum=fieldOffset b h+32*n := by decide

def mainRecord (b : Bool) (t : Levels) (s : SaltTape) (i : Index) :=
  (record .byte b t s i).flatMap mainBytes

theorem mainRecordSize (b : Bool) (t : Levels) (s : SaltTape) (i : Index) :
    (mainRecord b t s i).length=recordBytes b := by
  have lengths : (mainRecord b t s i).length=mainSize (record .byte b t s i) := by
    unfold mainRecord mainSize;simp [mainBytes,List.map_map,Function.comp_def]
  rw [lengths,mainSize,recordWidths];cases b <;> decide

theorem mainContains (b : Bool) (t : Levels) (s : SaltTape) (i : Index) (q : Place) (k : Nat)
    (bk : k<(places b).length) (atPlace : (places b)[k]?=some q) :
    ContainsAt (mainRecord b t s i) ((((places b).take k).map (wireWidth b)).sum)
      (bytes (n:=wireWidth b q) ((fieldAt b t s i q).2.setWidth (8*wireWidth b q))) := by
  let f:=fun l=>mainBytes (fieldAt b t s i l)
  have fs (l : Place) (bl : l∈places b) : (f l).length=wireWidth b l:=by
    simp only [f,mainBytes,List.length_map,List.length_range,widthsAt b l bl t s i,Nat.mul_div_cancel_left _ (by decide : 0<8)]
  have value : (places b)[k]=q:=Option.some.inj ((List.getElem?_eq_getElem bk).symm.trans atPlace)
  have mem : q∈places b:=value ▸ List.getElem_mem bk
  have size : (((places b).take k).flatMap f).length=((((places b).take k).map (wireWidth b)).sum) := by
    rw [List.length_flatMap];apply congrArg List.sum;apply List.map_congr_left
    intro l bl;exact fs l (List.mem_of_mem_take bl)
  have h:=locate (places b) f k bk
  rw [value,size] at h
  have fw : f q=bytes (n:=wireWidth b q) ((fieldAt b t s i q).2.setWidth (8*wireWidth b q)):=by
    change mainBytes _=_
    rw [show fieldAt b t s i q=(8*wireWidth b q,(fieldAt b t s i q).2) from Prod.ext (widthsAt _ _ mem ..) rfl]
    exact baseField .. 
  rw [fw] at h
  simpa only [mainRecord,recordPlaces,List.flatMap_map,Function.comp_def,f] using h

theorem mainSalt (b : Bool) (t : Levels) (s : SaltTape) (i : Index) :
    ContainsAt (mainRecord b t s i) 0 (bytes (n:=24) (s i)) := by
  have e:=mainContains b t s i none 0 (by simp [places]) rfl
  simpa only [wireWidth,fieldAt,List.take_zero,List.map_nil,List.sum_nil,BitVec.setWidth_setWidth_of_le _ (by decide : 192≤256),
    BitVec.setWidth_eq] using e

theorem mainSibling (b : Bool) (t : Levels) (s : SaltTape) (i : Index) (h n : Nat)
    (level : h<(if b then 15 else 24)) (bn : n<radix h-1) :
    ContainsAt (mainRecord b t s i) (fieldOffset b h+32*n)
      (bytes (n:=fieldBytes b h) ((sibling t i.val h n).setWidth (8*fieldBytes b h))) := by
  have hh : h<24:=by split at level <;> omega
  have nn : n<2:=by unfold radix at bn;split at bn <;> omega
  obtain ⟨bk,eq,off⟩:=directory b ⟨h,hh⟩ ⟨n,nn⟩ level bn
  have e:=mainContains b t s i _ _ bk eq
  rwa [off] at e
end CommitGolfCandidate.S4
