import CommitGolfCandidate.ChainedTailParseBuffer

/-! Width-generic inverse byte-stream plan and exact consumed-bit accounting. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf

structure ParsedTailPlan where
  fields : List (List Bool)
  carry : List Bool
  read : Nat

def tailParsePlan : List Nat → List Bool → (Nat → List Bool) → ParsedTailPlan
  | [],front,_ => ⟨[],front,0⟩
  | width::widths,front,input =>
    let advance := if front.length<width then 1 else 0
    let loaded := if front.length<width then front++input 0 else front
    let rest := tailParsePlan widths (nextParsedBits front (input 0) width) (fun i => input (advance+i))
    ⟨loaded.take width::rest.fields,rest.carry,advance+rest.read⟩

def pullBitBytes (input : Nat → List Bool) : Nat → List Bool
  | 0 => []
  | count+1 => input 0++pullBitBytes (fun i => input (1+i)) count

theorem tail_parse_plan_length (widths : List Nat) (front : List Bool) (input : Nat → List Bool) :
    (tailParsePlan widths front input).fields.length=widths.length := by
  induction widths generalizing front input with
  | nil => rfl
  | cons width widths ih => simp only [tailParsePlan,List.length_cons,ih]

theorem tail_parse_plan_read_bound (widths : List Nat) (front : List Bool) (input : Nat → List Bool) :
    (tailParsePlan widths front input).read≤widths.length := by
  induction widths generalizing front input with
  | nil => simp [tailParsePlan]
  | cons width widths ih =>
    have bound := ih (nextParsedBits front (input 0) width)
      (fun i => input ((if front.length<width then 1 else 0)+i))
    simp only [tailParsePlan,List.length_cons]
    by_cases more : front.length<width <;> simp only [more,↓reduceIte] at bound ⊢ <;> omega

theorem tail_parse_plan_pending (widths : List Nat) (front : List Bool) (input : Nat → List Bool)
    (pending : front.length<8) (byteSize : ∀ i, (input i).length=8) :
    (tailParsePlan widths front input).carry.length<8 := by
  induction widths generalizing front input with
  | nil => exact pending
  | cons width widths ih =>
    exact ih _ _ (next_parsed_pending front (input 0) width pending (byteSize 0))
      (fun i => byteSize _)

theorem tail_parse_plan_widths (widths : List Nat) (front : List Bool) (input : Nat → List Bool)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ width ∈ widths, width≤6) :
    (tailParsePlan widths front input).fields.map List.length=widths := by
  induction widths generalizing front input with
  | nil => rfl
  | cons width widths ih =>
    have bound := small width (by simp)
    have restSmall : ∀ value ∈ widths, value≤6 := fun value member => small value (by simp [member])
    have enough : width≤(if front.length<width then front++input 0 else front).length := by
      split
      · simp only [List.length_append,byteSize]
        omega
      · omega
    simp only [tailParsePlan,List.map_cons,List.length_take,Nat.min_eq_left enough]
    rw [ih _ _ (fun i => byteSize _) restSmall]

theorem tail_parse_plan_bits (widths : List Nat) (front : List Bool) (input : Nat → List Bool) :
    (tailParsePlan widths front input).fields.flatten++(tailParsePlan widths front input).carry=
      front++pullBitBytes input (tailParsePlan widths front input).read := by
  induction widths generalizing front input with
  | nil => simp [tailParsePlan,pullBitBytes]
  | cons width widths ih =>
    let advance := if front.length<width then 1 else 0
    let loaded := if front.length<width then front++input 0 else front
    let shifted := fun i => input (advance+i)
    let rest := tailParsePlan widths (nextParsedBits front (input 0) width) shifted
    have inductionResult := ih (nextParsedBits front (input 0) width) shifted
    change (loaded.take width++rest.fields.flatten)++rest.carry=
      front++pullBitBytes input (advance+rest.read)
    rw [List.append_assoc,inductionResult]
    change loaded.take width++(loaded.drop width++pullBitBytes shifted rest.read)=_
    rw [←List.append_assoc,List.take_append_drop]
    by_cases more : front.length<width
    · have moved : advance=1 := ite_eq_left more
      rw [moved,show 1+rest.read=rest.read+1 by omega,pullBitBytes]
      simp only [loaded,shifted,advance,more,↓reduceIte,List.append_assoc]
    · have stayed : advance=0 := ite_eq_right more
      rw [stayed,Nat.zero_add]
      simp only [loaded,shifted,advance,more,↓reduceIte,Nat.zero_add]

end CommitGolfCandidate.Chained.Native
