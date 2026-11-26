import CommitGolfCandidate.S5HonestTree
import CommitGolfCandidate.S5Wire
import CommitGolfCandidate.S5BatchCharge
namespace CommitGolfCandidate.S5
open CommitGolf
open Late (Levels SaltTape)
open S5Machine.Writer (widths)
open S5Machine.Reader (window)
def Located (whole : List Field) (at_ : Nat) (part : List Field) := ∃ pre rest : List Field,widths pre=at_ ∧ whole=pre++(part++rest)
theorem Located.nested {x y z a b} (f : Located x a y) (g : Located y b z) : Located x (a+b) z := by
  obtain ⟨pre,post,pa,e⟩:=f;obtain ⟨l,r,lb,g⟩:=g
  exact ⟨pre++l,r++post,by simp [widths,←pa,←lb],by rw [e,g];simp [List.append_assoc]⟩
theorem Located.append {xs p s} (loc : Located xs p s) (tail : List Field) : Located (xs++tail) p s := by
  obtain ⟨pre,post,width,eq⟩:=loc;exact ⟨pre,post++tail,width,by rw [eq];simp [List.append_assoc]⟩
theorem Located.prepend {xs p s} (loc : Located xs p s) (head : List Field) : Located (head++xs) (widths head+p) s := by
  obtain ⟨pre,post,width,eq⟩:=loc;exact ⟨head++pre,post,by simp [widths,←width],by rw [eq,List.append_assoc]⟩
theorem Located.get {fs at_ w v} (loc : Located fs at_ [(w,v)]) : window (encode fs) at_ w=v%2^w := by
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

def stageFields (tree : Levels) (i : Index) (d : Nat) :=
  (List.range (S4.radix d-1)).map fun j=>(bits d,(Auth.sibling tree i.val d j).toNat)
theorem stage_width (t i d) : widths (stageFields t i d)=(S4.radix d-1)*bits d := by
  unfold widths stageFields;simp [List.map_map,Function.comp_def]
theorem layers_width (t i) (ls : List Nat) : widths (ls.flatMap (stageFields t i))=(ls.map fun d=>(S4.radix d-1)*bits d).sum := by
  induction ls with
  | nil=>rfl
  | cons x ls ih=>rw [List.flatMap_cons,S5Machine.Open.sum_append,stage_width,ih];rfl

theorem record_located (tree : Levels) (salt : SaltTape) (xs : List Index) (r : Nat) (hr : r<xs.length) :
    Located (batchFields tree salt xs) (4030*r) (record tree salt xs[r] true) := by
  have f:=(flat_at xs (fun i=>record tree salt i true) r hr).append ((List.range 171).map (slot tree xs))
  have len:=S5Machine.Open.record_width_sum tree salt (xs.take r)
  rw [List.length_take,Nat.min_eq_left hr.le] at len
  rw [←len];exact f

theorem salt_located (t s i) : Located (record t s i true) 0 [(192,(s i).toNat)] :=
  ⟨[],(List.range 15).flatMap (stageFields t i),rfl,rfl⟩

theorem peer_located (t s i) (h k : Nat) (bh : h<15) (bk : k<S4.radix h-1) :
    Located (record t s i true) (layerBits h+k*bits h) [(bits h,(Auth.sibling t i.val h k).toNat)] := by
  have h1:=(flat_at (List.range 15) (stageFields t i) h (by simpa only [List.length_range] using bh)).prepend [(192,(s i).toNat)]
  simp only [List.getElem_range,List.take_range,Nat.min_eq_left bh.le,layers_width] at h1
  let f:=fun j=>(bits h,(Auth.sibling t i.val h j).toNat)
  have h2:=map_at (List.range (S4.radix h-1)) f k (by simpa only [List.length_range] using bk)
  simp only [List.take_range,Nat.min_eq_left bk.le,List.getElem_range] at h2
  have width : widths ((List.range k).map f)=k*bits h:=by simp [widths,f,List.map_map,Function.comp_def]
  rw [width] at h2
  exact h1.nested h2

theorem slot_located (tree : Levels) (salt : SaltTape) (xs : List Index) (len : xs.length=128) (j : Nat) (hj : j<171) :
    Located (batchFields tree salt xs) (515840+230*j) [slot tree xs j] := by
  have f:=(map_at (List.range 171) (slot tree xs) j (by simpa only [List.length_range] using hj)).prepend
    (S5Machine.Open.recordFields tree salt xs)
  rw [S5Machine.Open.record_width_sum,len,List.take_range,Nat.min_eq_left hj.le,List.getElem_range] at f
  have width : widths ((List.range j).map (slot tree xs))=230*j:=by simp [widths,slot,List.map_map,Function.comp_def,Nat.mul_comm]
  rw [width] at f;exact f
end CommitGolfCandidate.S5
