import CommitGolfCandidate.S5WriterCode
import CommitGolfCandidate.S5Model
namespace CommitGolfCandidate.S5Machine.Writer
open CommitGolf
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

/-- Pending bits in the last output word and instructions already charged. -/
structure Meter where
  bits : Nat
  cycles : Nat
  deriving DecidableEq

def push (m : Meter) (n : Nat) : Meter :=
  let used:=m.bits+n
  let readCost:=(fetchWord (n<64)).length+mix.length
  let writeCost:=if used<64 then 0 else (spill (used=64)).length
  ⟨used%64,m.cycles+readCost+writeCost⟩

def measureField (m : Meter) (n : Nat) : Meter :=
  let full := (List.replicate (n/64) 64).foldl push m
  let final := if n%64=0 then full else push full (n%64)
  {final with cycles:=final.cycles+finish.length}

def recordWidths : List Nat := 192::(List.range 15).flatMap fun d=>
  (List.range (S4.radix d-1)).map fun _=>S5.bits d

theorem record_widths (t s ix) :
    (S5.record t s ix true).map Prod.fst=recordWidths := by
  simp [S5.record,recordWidths,List.map_flatMap,List.map_map,Function.comp_def]

def measureFields (widths : List Nat) := widths.foldl measureField

def repeated {α} (f : α→α) : Nat→α→α
  | 0,x=>x
  | n+1,x=>repeated f n (f x)

def fieldMeter :=
  repeated (fun m=>measureField m 230) 171
    (repeated (measureFields recordWidths) 128 ⟨0,0⟩)

theorem writer_charge : fieldMeter=⟨34,159588⟩ := by decide +kernel

/-- An untouched pair executes 19 instructions outside the packing subroutine.
A touched pair saves two, three or four, according to its two mark bytes. -/
def capCost (left right : Bool) :=
  if left then (if right then 16 else 17) else if right then 15 else 19

theorem cap_discount (marks : List (Bool × Bool)) (touched : ∃ m∈marks,m.1 || m.2) :
    (marks.map (fun m=>capCost m.1 m.2)).sum+2 ≤ 19*marks.length := by
  have all (xs : List (Bool × Bool)) :
      (xs.map (fun m=>capCost m.1 m.2)).sum ≤ 19*xs.length := by
    induction xs with
    | nil=>simp
    | cons m xs ih=>rcases m with ⟨a,b⟩;cases a <;> cases b <;> simp [capCost,Nat.mul_add] at * <;> omega
  induction marks with
  | nil=>simp at touched
  | cons m xs ih=>
    rcases m with ⟨a,b⟩
    by_cases hit : (a || b)=true
    · have tail:=all xs
      cases a <;> cases b <;> simp [capCost,Nat.mul_add] at * <;> omega
    · have tail : ∃ m∈xs,m.1 || m.2 := by
        obtain ⟨w,mem,hw⟩:=touched
        rcases List.mem_cons.mp mem with rfl | mem
        · exact False.elim (hit hw)
        · exact ⟨w,mem,hw⟩
      have bound:=ih tail
      cases a <;> cases b <;> simp [capCost,Nat.mul_add] at * <;> omega

theorem scheduled_bound (evenRecords : Nat) (marks : List (Bool × Bool)) (num : marks.length=171)
    (evenBound : evenRecords≤128) (touched : ∃ m∈marks,m.1 || m.2) :
    118+128*218+evenRecords+4+(marks.map (fun m=>capCost m.1 m.2)).sum+
      34+fieldMeter.cycles ≤ 191023 := by
  have savings:=cap_discount marks touched
  rw [num] at savings
  rw [writer_charge]
  dsimp
  omega
def capMarks (xs : List Index) (p : Nat) : Bool × Bool :=
  (xs.any fun i=>i.val/49152==2*p, xs.any fun i=>i.val/49152==2*p+1)

theorem marked_pair (i : Index) (xs : List Index) (present : i∈xs) :
    ∃ m∈(List.range 171).map (capMarks xs), m.1 || m.2 := by
  let n := i.val/49152
  let p := n/2
  have bound:=i.isLt
  change i.val<16777216 at bound
  have inside : p<171 := by dsimp [p,n];omega
  refine ⟨capMarks xs p,List.mem_map.mpr ⟨p,List.mem_range.mpr inside,rfl⟩,?_⟩
  have sides : n=2*p ∨ n=2*p+1 := by dsimp [p];omega
  apply Bool.or_eq_true_iff.mpr
  rcases sides with left | right
  · exact Or.inl (List.any_eq_true.mpr ⟨i,present,beq_iff_eq.mpr left⟩)
  · exact Or.inr (List.any_eq_true.mpr ⟨i,present,beq_iff_eq.mpr right⟩)

def batchCost (xs : List Index) :=
  118+128*218+(xs.filter fun i => i.val%2==0).length+4+
    (((List.range 171).map (capMarks xs)).map (fun m=>capCost m.1 m.2)).sum+34+fieldMeter.cycles

theorem batch_bound (xs : List Index) (batch : xs.length=128) : batchCost xs≤191023 := by
  have pos : 0<xs.length := by omega
  let i:=xs[0]'pos
  apply scheduled_bound
  · simp
  · exact (List.length_filter_le ..).trans (le_of_eq batch)
  · exact marked_pair i xs (List.getElem_mem pos)

end CommitGolfCandidate.S5Machine.Writer
