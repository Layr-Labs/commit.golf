import CommitGolfCandidate.S5OpeningCost
import CommitGolfCandidate.S5ReadWindow
namespace CommitGolfCandidate.S5
open CommitGolf
set_option maxRecDepth 12000
attribute [local irreducible] List.range encode
open S5Machine.Writer (widths encode_bound encode_append recordWidths record_widths)
open S5Machine.Reader (window)

/-- All completions share the 69,396 transmitted bytes. The final cap field
contains the only two bits determined by the checker's four trials. -/
def batchFields (t s) (xs : List Index) :=
  xs.flatMap (fun i=>record t s i true)++(List.range 171).map (slot t xs)
def wireBits := 8*69396

theorem field_width (t s i) : widths (record t s i true)=4030 := by
  unfold widths;rw [record_widths];decide +kernel
private theorem records_width (t s) (xs : List Index) :
    widths (xs.flatMap (fun i=>record t s i true))=4030*xs.length := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>
    simp only [List.flatMap_cons,widths,List.map_append,List.sum_append,List.length_cons]
    change widths (record t s i true)+widths (xs.flatMap _)=_
    rw [field_width,ih];omega

theorem batch_width (t s) (xs : List Index) (size : xs.length=128) :
    widths (batchFields t s xs)=wireBits+2 := by
  unfold batchFields widths;rw [List.map_append,List.sum_append]
  change widths (xs.flatMap _)+_=_
  rw [records_width,size]
  have sums (js : List Nat) : ((js.map (slot t xs)).map Prod.fst).sum=js.length*230 := by
    induction js with
    | nil=>rfl
    | cons j js ih=>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,ih]
      change 230+js.length*230=js.length*230+230;omega
  have cap:=sums (List.range 171)
  rw [List.length_range] at cap
  rw [cap];decide

def complete (v trial : Nat) := v%2^wireBits+2^wireBits*trial
private theorem four_parts (v e : Nat) (bound : v<2^(e+2)) :
    ∃ j : Fin 4, v%2^e+2^e*j.val=v := by
  have hi : v/2^e<4 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos e)).mpr (by rw [Nat.mul_comm];simpa only [pow_add,show (2:Nat)^2=4 by decide] using bound)
  exact ⟨⟨v/2^e,hi⟩,Nat.mod_add_div ..⟩

theorem true_trial (t s xs) (size : xs.length=128) :
    let v:=encode (batchFields t s xs)
    ∃ j : Fin 4,complete v j.val=v := by
  let v:=encode (batchFields t s xs)
  have b:=encode_bound (batchFields t s xs)
  rw [batch_width t s xs size] at b
  exact four_parts v wireBits b

theorem field_at (pre rest : List Field) (w v : Nat) :
    window (encode (pre++(w,v)::rest)) (widths pre) w=v%2^w := by
  rw [encode_append]
  unfold window
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt (encode_bound pre),Nat.zero_add,encode,
    Nat.add_mul_mod_self_left,Nat.mod_mod]
end CommitGolfCandidate.S5
