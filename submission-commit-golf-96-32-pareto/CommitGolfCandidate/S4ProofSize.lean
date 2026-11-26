import CommitGolfCandidate.S4Model
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape)
def widths (p : Profile) (batch : Bool) : List Nat :=
  192::(List.range (if batch then 15 else 24)).flatMap
    (fun h=>List.replicate (radix h-1) (if batch then bits p h else 256))
theorem recordWidths (p : Profile) (b : Bool) (t : Levels) (s : SaltTape) (i : Index) :
    (record p b t s i).map Prod.fst=widths p b := by
  simp only [record,widths,List.map_cons,List.map_flatMap,List.map_map,Function.comp_def,List.map_const',
    List.length_range]
def mainSize (fs : List Field) := ((fs.map Prod.fst).map (·/8)).sum
def tailCount (fs : List Field) := ((fs.map Prod.fst).filter (·==238)).length

theorem mainAppend (x y : List Field) : mainSize (x++y)=mainSize x+mainSize y := by simp [mainSize]
theorem tailsAppend (x y : List Field) : tailCount (x++y)=tailCount x+tailCount y := by simp [tailCount]
theorem serializeLength (fs : List Field) : (serialize fs).length=mainSize fs+(6*tailCount fs+7)/8 := by
  have lenMain : (fs.flatMap mainBytes).length=mainSize fs := by
    induction fs with
    | nil=>rfl
    | cons x xs ih=>simp only [List.flatMap_cons,List.length_append,mainBytes,List.length_map,List.length_range,ih,
        mainSize,List.map_cons,List.sum_cons]
  have lenTail : (fs.filter fun f=>f.1==238).length=tailCount fs := by
    clear lenMain
    induction fs with
    | nil=>rfl
    | cons x xs ih=>simp only [tailCount,List.map_cons,List.filter_cons];split <;> simp_all [tailCount]
  simp only [serialize,List.length_append,lenMain,List.length_map,List.length_range,lenTail]

private theorem flatSize {α : Type} (f : α→List Field) (w : List Field→Nat) (base : w []=0)
    (append : ∀ l r,w (l++r)=w l+w r) (xs : List α) (c : Nat) (all : ∀ a,w (f a)=c) :
    w (xs.flatMap f)=xs.length*c := by
  induction xs with
  | nil=>simpa using base
  | cons a xs ih=>rw [List.flatMap_cons,append,all,ih,List.length_cons,Nat.succ_mul];omega

private theorem uniformMain {α : Type} (xs : List α) (w : Nat) (f : α→Late.Digest) :
    mainSize (xs.map fun j=>(w,f j))=xs.length*(w/8) := by
  induction xs with
  | nil=>simp [mainSize]
  | cons x xs ih=>
    change w/8+mainSize (xs.map (fun j=>(w,f j)))=(xs.length+1)*(w/8)
    rw [ih,Nat.succ_mul,Nat.add_comm]
private theorem uniformTails {α : Type} (xs : List α) (w : Nat) (f : α→Late.Digest) :
    tailCount (xs.map fun j=>(w,f j))=if w=238 then xs.length else 0 := by
  induction xs with
  | nil=>simp [tailCount]
  | cons x xs ih=>
    by_cases b : w=238
    · simpa only [tailCount,List.map_cons,List.length_cons,List.filter_cons,b,beq_self_eq_true,ite_true] using congrArg (·+1) ih
    · simpa only [tailCount,List.map_cons,List.filter_cons,beq_iff_eq,if_neg b] using ih
def recordMain (p : Profile) (b : Bool) := ((widths p b).map (·/8)).sum
def recordTails (p : Profile) (b : Bool) := ((widths p b).filter (·==238)).length

attribute [local irreducible] pairSlot record
set_option maxRecDepth 5000 in
theorem openingSize (p : Profile) (t : Levels) (s : SaltTape) (ps : Positions) :
    (opening p t s ps).length=if ps.card=BATCH then (if p=.byte then 70410 else 70080) else 824*ps.card := by
  have main (b : Bool) (i : Index) : mainSize (record p b t s i)=recordMain p b := by rw [mainSize,recordWidths];rfl
  have tails (b : Bool) (i : Index) : tailCount (record p b t s i)=recordTails p b := by rw [tailCount,recordWidths];rfl
  have records (b : Bool) :=flatSize (record p b t s) mainSize rfl mainAppend (ps.sort (·≤·)) (recordMain p b) (main b)
  have extras (b : Bool) :=flatSize (record p b t s) tailCount rfl tailsAppend (ps.sort (·≤·)) (recordTails p b) (tails b)
  have capMain : mainSize ((List.range 171).map fun j=>(bits p 16,pairSlot t (ps.sort (·≤·)) j))=171*(bits p 16/8) := by
    exact (uniformMain (List.range 171) _ _).trans (by rw [List.length_range])
  have capTails : tailCount ((List.range 171).map fun j=>(bits p 16,pairSlot t (ps.sort (·≤·)) j))=if bits p 16=238 then 171 else 0 := by
    exact (uniformTails (List.range 171) _ _).trans (by rw [List.length_range])
  unfold opening;dsimp only;split
  · rename_i eqv
    rw [serializeLength,mainAppend,tailsAppend,records,extras,Finset.length_sort,eqv,capMain,capTails]
    cases p <;> decide
  · rename_i eqv
    rw [serializeLength,records,extras,Finset.length_sort]
    have m : recordMain p false=824:=by cases p <;> decide
    have z : recordTails p false=0:=by cases p <;> decide
    simp [m,z,Nat.mul_comm]
theorem actualOpeningSize (t : Levels) (s : SaltTape) (ps : Positions) :
    (actualOpening t s ps).length=if ps.card=BATCH then 70080 else 824*ps.card := by
  unfold actualOpening;split
  · apply Carry.packed_length
  · rename_i n;rw [openingSize,if_neg n]
end CommitGolfCandidate.S4
