import CommitGolfCandidate.Layout2Tables

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf
set_option maxHeartbeats 900000

/-- Destination dword to source dword in the 184-byte rearranged prefix.
Forward (false) receives a V1 destination and reads a physical quartet source. -/
def wordAt (back : Bool) (q d : Nat) : Nat :=
  if back then
    if d < 7 then 16+d
    else
      let slot := (d-7)/4 ^^^ q
      let mate := (slot+3)%4
      4*mate+(d-7)%4
  else if d < 16 then 7+4*((d/4+1)%4 ^^^ q)+d%4
  else d-16

theorem word_inverse : ∀ b : Bool, ∀ q : Fin 4, ∀ d : Fin 23,
    wordAt b q d < 23 ∧ wordAt (!b) q (wordAt b q d) = d.val := by decide +kernel

/-- Physical record base is the aligned floor of the nominal 534-byte stride.
The rearranged interval begins 10, 12, 14 or 16 bytes into the nominal cell. -/
def window (j : Nat) := 16-(534*j)%8

theorem window_base (j : Nat) : 534*j+window j=8*((534*j)/8)+16 := by
  unfold window;omega

theorem phase_base (j : Nat) : 8*((534*j)/8)=2136*(j/4)+phaseBase (j%4) := by
  unfold phaseBase;split_ifs <;> omega

def within (back : Bool) (q : Fin 4) (w x : Nat) : Nat :=
  if w ≤ x ∧ x < w+184 then
    w+8*wordAt back q ((x-w)/8)+(x-w)%8
  else x

theorem within_facts (b : Bool) (q : Fin 4) (w x : Nat) (bound : w≤16) (inside : x<534) :
    within b q w x < 534 ∧ within (!b) q w (within b q w x)=x := by
  by_cases hit : w≤x ∧ x<w+184
  · let d : Fin 23 := ⟨(x-w)/8,by omega⟩
    obtain ⟨fits,inv⟩ := word_inverse b q d
    let y := w+8*wordAt b q d+(x-w)%8
    have lo : w≤y := by dsimp [y];omega
    have hi : y<w+184 := by dsimp [y];omega
    have head : within b q w x=y := by simp [within,hit,y,d]
    have chunk : (y-w)/8=wordAt b q d := by dsimp [y];omega
    have lane : (y-w)%8=(x-w)%8 := by dsimp [y];omega
    rw [head]
    refine ⟨by omega,?_⟩
    rw [within,if_pos ⟨lo,hi⟩,chunk,lane,inv]
    dsimp [d];omega
  · simp [within,hit,inside]

abbrev Selectors := Nat → Fin 4

def index (back : Bool) (k : Nat) (qs : Selectors) (i : Nat) : Nat :=
  if i < 534*k then
    let j:=i/534
    534*j+within back (qs j) (window j) (i%534)
  else i

theorem index_facts (b : Bool) (k : Nat) (qs : Selectors) (i : Nat) :
    (i<534*k → index b k qs i<534*k) ∧ index (!b) k qs (index b k qs i)=i := by
  by_cases h : i<534*k
  · let j:=i/534
    let x:=i%534
    let y:=within b (qs j) (window j) x
    obtain ⟨bound,inv⟩ := within_facts b (qs j) (window j) x (by unfold window;omega) (by dsimp [x];omega)
    change y<534 at bound
    have e : index b k qs i=534*j+y := by simp [index,h,j,y,x]
    have valid : 534*j+y<534*k := by dsimp [j];omega
    rw [e]
    refine ⟨fun _=>valid,?_⟩
    rw [index,if_pos valid,show (534*j+y)/534=j by omega,show (534*j+y)%534=y by omega]
    change 534*j+within (!b) (qs j) (window j) y=i
    rw [inv];dsimp [j,x];omega
  · simp [index,h]

def transform (back : Bool) (k : Nat) (qs : Selectors) (P : Proof) : Proof :=
  if 534*k≤P.length then List.ofFn (fun i : Fin P.length => P[index back k qs i]?.getD 0)
  else P

@[simp] theorem length_transform (b k qs P) : (transform b k qs P).length=P.length := by
  unfold transform;split <;> simp

theorem read_transform (b k qs P i) (complete : 534*k≤P.length) (inside : i<P.length) :
    (transform b k qs P)[i]?.getD 0 = P[index b k qs i]?.getD 0 := by
  rw [List.getElem?_eq_getElem (by simpa using inside : i<(transform b k qs P).length)]
  simp [transform,complete]

theorem transform_inverse (b k qs P) : transform (!b) k qs (transform b k qs P)=P := by
  by_cases complete : 534*k≤P.length
  · apply List.ext_getElem (by simp)
    intro i _ hi
    have valid : index (!b) k qs i<P.length := by
      by_cases inside : i<534*k
      · exact ((index_facts (!b) k qs i).1 inside).trans_le complete
      · simpa [index,inside] using hi
    have lhs := read_transform (!b) k qs (transform b k qs P) i (by simpa using complete) (by simpa using hi)
    rw [read_transform b k qs P _ complete valid] at lhs
    have inv := (index_facts (!b) k qs i).2
    simp only [Bool.not_not] at inv
    rw [inv] at lhs
    simpa [hi,show i<(transform (!b) k qs (transform b k qs P)).length by simpa using hi] using lhs
  · simp [transform,complete]

def selectors (p : Positions) : Selectors := fun i =>
  ⟨((p.sort (· ≤ ·))[i]?.getD (⟨0,by decide⟩ : Index)).val%4, Nat.mod_lt _ (by decide)⟩

def decoder (p : Positions) (P : Proof) := convert decTables p.card (transform false p.card (selectors p) P)
def encoder (p : Positions) (P : Proof) := transform true p.card (selectors p) (convert encTables p.card P)

@[simp] theorem encoder_length (p P) : (encoder p P).length=P.length := by simp [encoder]
@[simp] theorem decoder_length (p P) : (decoder p P).length=P.length := by simp [decoder]

theorem decode_encode (p P) (complete : 534*p.card≤P.length) : decoder p (encoder p P)=P := by
  unfold decoder encoder
  rw [show transform false p.card (selectors p) (transform true p.card (selectors p) (convert encTables p.card P))
    =convert encTables p.card P from transform_inverse true ..]
  exact convert_dec_enc _ _ complete

theorem encode_decode (p P) (complete : 534*p.card≤P.length) : encoder p (decoder p P)=P := by
  unfold encoder decoder
  rw [convert_enc_dec _ _ (by simpa using complete)]
  exact transform_inverse false ..

theorem suffix (b k qs P i) (past : 534*k ≤ i) (inside : i<P.length) :
    (transform b k qs P)[i]?.getD 0=P[i]?.getD 0 := by
  rw [read_transform b k qs P i (by omega) inside,index,if_neg (by omega)]

end CommitGolfCandidate.Layout2.Quartet
