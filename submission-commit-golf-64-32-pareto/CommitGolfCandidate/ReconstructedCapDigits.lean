import CommitGolfCandidate.ReconstructedRecordDigits

namespace CommitGolfCandidate.Reconstruction.CapDigits
open CommitGolf Encoding Wire RecordDigits
set_option maxRecDepth 12000

def extract : Nat → Nat → List Nat × Nat
  | 0,v => ([],v)
  | n+1,v =>
    let tail := extract n (v/211)
    (v%211::tail.1,tail.2)

theorem decode (digit : Nat → Nat) (xs : List Nat) (bounded : ∀ i, digit i<211) :
    extract xs.length (headerValue digit xs) = (xs.map digit,0) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [List.length_cons,headerValue,extract,List.map_cons,Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (bounded j),Nat.add_mul_div_left _ _ (by decide : 0<211),
      Nat.div_eq_of_lt (bounded j),Nat.zero_add,ih]

theorem header_lt (digit : Nat → Nat) (xs : List Nat) (bounded : ∀ i, digit i<211) :
    headerValue digit xs<211^xs.length := by
  induction xs with
  | nil => exact Nat.zero_lt_one
  | cons j xs ih =>
    have h := bounded j
    simp only [headerValue,List.length_cons,pow_succ]
    omega

/-- Decode each group of one through four siblings and check its unused high bits. -/
def groups (digit : Nat → Nat) : List Nat → List (List Nat)
  | [] => []
  | a::b::c::d::rest => [digit a,digit b,digit c,digit d] :: groups digit rest
  | rest => [rest.map digit]

def recover : List Nat → List Field → Option (List (List Nat))
  | [],[] => some []
  | _::_::_::_::rest,f::fs => do
    let ds := extract 4 (clipped f)
    if ds.2≠0 then none else return ds.1 :: (← recover rest fs)
  | xs,[f] => if xs.isEmpty ∨ xs.length>3 then none else
    let ds := extract xs.length (clipped f)
    if ds.2≠0 then none else some [ds.1]
  | _,_ => none

private theorem fitted (digit : Nat → Nat) (xs : List Nat) (bounded : ∀ i, digit i<211)
    (small : xs.length≤4) : clipped ⟨headerValue digit xs,31⟩ = headerValue digit xs := by
  exact Nat.mod_eq_of_lt ((header_lt digit xs bounded).trans_le ((Nat.pow_le_pow_right (by decide : 0<211) small).trans (by decide : 211^4≤2^31)))

theorem cap_roundtrip (digit : Nat → Nat) (xs : List Nat) (bounded : ∀ i, digit i<211) :
    recover xs (capHeaders digit xs) = some (groups digit xs) := by
  match xs with
  | [] => rfl
  | [a] =>
    have h := decode digit [a] bounded
    change extract 1 (headerValue digit [a]) = (_,0) at h
    have fit := fitted digit [a] bounded (by change 1≤4;decide)
    simp [recover,groups,capHeaders,fit,h]
  | [a,b] =>
    have h := decode digit [a,b] bounded
    change extract 2 (headerValue digit [a,b]) = (_,0) at h
    have fit := fitted digit [a,b] bounded (by change 2≤4;decide)
    simp [recover,groups,capHeaders,fit,h]
  | [a,b,c] =>
    have h := decode digit [a,b,c] bounded
    change extract 3 (headerValue digit [a,b,c]) = (_,0) at h
    have fit := fitted digit [a,b,c] bounded (by change 3≤4;decide)
    simp [recover,groups,capHeaders,fit,h]
  | a::b::c::d::rest =>
    have host := decode digit [a,b,c,d] bounded
    change extract 4 (headerValue digit [a,b,c,d])=([digit a,digit b,digit c,digit d],0) at host
    simp only [capHeaders,recover,fitted digit [a,b,c,d] bounded (by change 4≤4;decide),host,ne_eq,not_true_eq_false,
      ite_false,groups,cap_roundtrip digit rest bounded,Option.pure_def]
    rfl

theorem paid (t : Encoding.Tree) (g : canonical t) (d : Depth) (paidDepth : d.val=8 ∨ d.val=9) (xs : List Nat) :
    recover xs (capHeaders (fun j => highDigit (t d j) (lows d)) xs) =
      some (groups (fun j => highDigit (t d j) (lows d)) xs) := by
  apply cap_roundtrip
  intro j
  have b := digit_bound t g d j
  have baseEq : base d.val=211 := by rcases paidDepth with h|h <;> rw [h] <;> decide
  rwa [baseEq] at b

theorem lower_digits (t : Encoding.Tree) (good : canonical t) (i : Index) (xs : List Depth) :
    HonestDivision.digitList (ds t good i xs) = xs.map (fun d : Depth => highDigit (t d.val (sibling i d.val)) (lows d.val)) := by
  induction xs with
  | nil => rfl
  | cons d xs ih => simp only [ds,HonestDivision.digitList,ih,List.map_cons]

private theorem recombine (n k : Nat) : n%2^k ||| ((n/2^k)*2^k)=n := by
  have low := Nat.mod_lt n (Nat.two_pow_pos k)
  rw [Nat.or_comm,Nat.mul_comm (n/2^k) (2^k),←Nat.two_pow_add_eq_or_of_lt low]
  exact Nat.div_add_mod n (2^k)

/-- Reattaching the digit to the transmitted low field recovers the high word for
every tree depth, including depths whose implicit digit is zero. -/
theorem high_word (x : Binding.Digest) (w : Nat) :
    clipped ⟨x.2.toNat,w-192⟩ ||| (highDigit x w <<< (w-192)) = x.2.toNat := by
  exact (show ∀ (n k : Nat), n%2^k ||| ((n >>> k) <<< k) = n from fun n k => by
    rw [Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq];exact recombine n k) x.2.toNat (w-192)

end CommitGolfCandidate.Reconstruction.CapDigits
