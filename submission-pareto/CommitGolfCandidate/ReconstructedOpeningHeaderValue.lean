import CommitGolfCandidate.ReconstructedOpeningHeader336
import CommitGolfCandidate.ReconstructedOpeningHorner
import CommitGolfCandidate.ReconstructedOpeningWordFields

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf RiscvZkvm.Rv64 OpeningCursor OpeningWordFields OpeningHeaderAddress
set_option maxRecDepth 12000
set_option maxHeartbeats 900000

def digitAt (x : Context) (d : Nat) := digit (top x d) d
def partialHeader (x : Context) : Nat → Nat
  | 0 => 0
  | n+1 => partialHeader x n * Encoding.base (10+n) + digitAt x (10+n)

theorem digit10 (x : Context) : v257 x=W (digitAt x 10) := extract10 (top x 10)
theorem low10 (x : Context) : v257 x=W (partialHeader x 1) := by simpa only [partialHeader,Nat.zero_mul,Nat.zero_add,Nat.add_zero] using digit10 x

theorem digit11 (x : Context) : v269 x=W (digitAt x 11) := extract11 (top x 11)
theorem product11 (x : Context) : v259 x=W (partialHeader x 1*1325) := by
  change v257 x*W 1325=_
  rw [low10,←BitVec.ofNat_mul]
theorem low11 (x : Context) : v270 x=W (partialHeader x 2) := by
  change v259 x+v269 x=W (partialHeader x 1*1325+digitAt x 11)
  rw [product11,digit11,←BitVec.ofNat_add]

theorem digit12 (x : Context) : v281 x=W (digitAt x 12) := extract12 (top x 12)
theorem product12 (x : Context) : v271 x=W (partialHeader x 2*1325) := by
  change v270 x*W 1325=_
  rw [low11,←BitVec.ofNat_mul]
theorem low12 (x : Context) : v282 x=W (partialHeader x 3) := by
  change v271 x+v281 x=W (partialHeader x 2*1325+digitAt x 12)
  rw [product12,digit12,←BitVec.ofNat_add]

theorem digit13 (x : Context) : v294 x=W (digitAt x 13) := extract13 (top x 13)
theorem product13 (x : Context) : v284 x=W (partialHeader x 3*1677) := by
  change v282 x*W 1677=_
  rw [low12,←BitVec.ofNat_mul]
theorem low13 (x : Context) : v295 x=W (partialHeader x 4) := by
  change v284 x+v294 x=W (partialHeader x 3*1677+digitAt x 13)
  rw [product13,digit13,←BitVec.ofNat_add]

theorem digit14 (x : Context) : v303 x=W (digitAt x 14) := extract14 (top x 14)
theorem product14 (x : Context) : v296 x=W (partialHeader x 4*1677) := by
  change v295 x*W 1677=_
  rw [low13,←BitVec.ofNat_mul]
theorem low14 (x : Context) : v304 x=W (partialHeader x 5) := by
  change v296 x+v303 x=W (partialHeader x 4*1677+digitAt x 14)
  rw [product14,digit14,←BitVec.ofNat_add]

theorem digit15 (x : Context) : v313 x=W (digitAt x 15) := extract15 (top x 15)
theorem product15 (x : Context) : v306 x=W (partialHeader x 5*137) := by
  change v304 x*W 137=_
  rw [low14,←BitVec.ofNat_mul]
theorem low15 (x : Context) : v314 x=W (partialHeader x 6) := by
  change v306 x+v313 x=W (partialHeader x 5*137+digitAt x 15)
  rw [product15,digit15,←BitVec.ofNat_add]

theorem digit16 (x : Context) : v323 x=W (digitAt x 16) := extract16 (top x 16)
theorem product16 (x : Context) : v316 x=W (partialHeader x 6*1491) := by
  change v314 x*W 1491=_
  rw [low15,←BitVec.ofNat_mul]
theorem low16 (x : Context) : v324 x=W (partialHeader x 7) := by
  change v316 x+v323 x=W (partialHeader x 6*1491+digitAt x 16)
  rw [product16,digit16,←BitVec.ofNat_add]

theorem digit17 (x : Context) : v332 x=W (digitAt x 17) := extract17 (top x 17)
theorem product17 (x : Context) : v325 x=W (partialHeader x 7*1491) := by
  change v324 x*W 1491=_
  rw [low16,←BitVec.ofNat_mul]
theorem low17 (x : Context) : v333 x=W (partialHeader x 8) := by
  change v325 x+v332 x=W (partialHeader x 7*1491+digitAt x 17)
  rw [product17,digit17,←BitVec.ofNat_add]

theorem digit18 (x : Context) : v340 x=W (digitAt x 18) := extract18 (top x 18)
theorem product18 (x : Context) : v334 x=W (partialHeader x 8*1677) := by
  change v333 x*W 1677=_
  rw [low17,←BitVec.ofNat_mul]
theorem low18 (x : Context) : v341 x=W (partialHeader x 9) := by
  change v334 x+v340 x=W (partialHeader x 8*1677+digitAt x 18)
  rw [product18,digit18,←BitVec.ofNat_add]

theorem digit19 (x : Context) : v343 x=W (digitAt x 19) := extract19 (top x 19)
theorem product19 (x : Context) : v342 x=W (partialHeader x 9*1491) := by
  change v341 x*W 1491=_
  rw [low18,←BitVec.ofNat_mul]
theorem low19 (x : Context) : v344 x=W (partialHeader x 10) := by
  change v342 x+v343 x=W (partialHeader x 9*1491+digitAt x 19)
  rw [product19,digit19,←BitVec.ofNat_add]

private theorem prefix_fold (x : Context) (n : Nat) :
    partialHeader x n=(List.range n).foldl (fun h j => h*Encoding.base (10+j)+digitAt x (10+j)) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [partialHeader,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]

theorem prefix_tree (x : Context) (ps : Positions) (trap : CommitStorage.Trapdoor)
    (ne : 0<ps.card) (mem : Heap x.initial.mem trap ps) (o : Oracle) (k : Generator.Key) (msg : Message)
    (st : CommitStorage.Stored o k msg trap) :
    partialHeader x 10 = Encoding.recordHeader (LeafTree.tree o k msg) x.index := by
  have agree (d : Fin 25) (hd : 0<d.val) : digitAt x d.val =
      Encoding.highDigit (LeafTree.tree o k msg d (Encoding.sibling x.index d)) (Encoding.lows d) :=
    digit_value x.initial.mem trap ps ne mem o k msg st x.index d hd
  rw [prefix_fold,Encoding.recordHeader]
  have onRange (xs : List Nat) (h : ∀ j ∈ xs, j<10) (a : Nat) :
      xs.foldl (fun cur j => cur*Encoding.base (10+j)+digitAt x (10+j)) a =
      xs.foldl (fun cur j => cur*Encoding.base (10+j)+
        Encoding.highDigit (LeafTree.tree o k msg (10+j) (Encoding.sibling x.index (10+j))) (Encoding.lows (10+j))) a := by
    induction xs generalizing a with
    | nil => rfl
    | cons j js ih =>
      have small := h j (List.mem_cons_self)
      have same : digitAt x (10+j)=_ := agree (⟨10+j,by omega⟩ : Fin 25) (by change 0<10+j;omega)
      simp only [List.foldl_cons,same]
      exact ih (fun n hn => h n (List.mem_cons_of_mem _ hn)) _
  exact onRange _ (fun j hj => List.mem_range.mp hj) _

theorem smallDigit (x : Context) (d : Nat) (h : 10≤d ∧ d≤19) : digitAt x d<2048 := by
  have aux (v : Word) (k n : Nat) (h : k≤n+11) :
      (v.toNat%2^k) >>> n<2048 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    have more := Nat.pow_le_pow_right (n:=2) (by decide) h
    rw [Nat.pow_add,Nat.mul_comm] at more
    exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le more
  apply aux
  obtain ⟨lower,upper⟩ := h
  interval_cases d <;> decide

theorem small13 (x : Context) : partialHeader x 4<2^64 := by
  have a := smallDigit x 10 (by decide)
  have b := smallDigit x 11 (by decide)
  have c := smallDigit x 12 (by decide)
  have d := smallDigit x 13 (by decide)
  simp only [partialHeader,Nat.zero_mul,Nat.zero_add,Nat.add_zero]
  change ((digitAt x 10*1325+digitAt x 11)*1325+digitAt x 12)*1677+digitAt x 13<2^64
  omega

end CommitGolfCandidate.Reconstruction.OpeningHeader
