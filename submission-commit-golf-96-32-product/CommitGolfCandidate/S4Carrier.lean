import CommitGolf.Statements

set_option Elab.async false

namespace CommitGolfCandidate.S4.Carry
open CommitGolf
set_option maxRecDepth 8192

def carrier (c : Nat) := if c<1152 then 510*(c/9)+269+30*(c%9) else 65309+30*(c-1152)
def candidate (a : Nat) := if a<65280 then 9*(a/510)+(a%510-269)/30 else 1152+(a-65309)/30
def used (a : Nat) := candidate a<1309 ∧ carrier (candidate a)=a
instance (a : Nat) : Decidable (used a) := inferInstanceAs (Decidable (_ ∧ _))
theorem location (c : Nat) (hc : c<1309) :
    candidate (carrier c)=c ∧ carrier c<70080 := by
  by_cases b : c<1152
  · simp only [carrier,if_pos b,candidate]
    rw [if_pos (by omega)]
    constructor <;> omega
  · simp only [carrier,if_neg b,candidate]
    rw [if_neg (by omega)]
    constructor <;> omega

theorem usedCarrier (c : Nat) (hc : c<1309) : used (carrier c) := by
  unfold used;rw [(location c hc).1];exact ⟨hc,rfl⟩

def group (k p : Nat) := 119*(k/30)+4*(k%30)+p
def source (c : Nat) := 30*(c/119)+(c%119)/4
def part (c : Nat) := c%119%4
def pieces (k : Nat) := if k%30=29 then 3 else 4
theorem groupSpec (k p : Nat) (hk : k<330) (hp : p<pieces k) :
    group k p<1309 ∧ source (group k p)=k ∧ part (group k p)=p := by
  have bound : p<4:=by unfold pieces at hp;split at hp <;> omega
  have closed : ∀ i : Fin 330,∀ k : Fin 4,k.val<pieces i.val →
      group i.val k.val<1309 ∧ source (group i.val k.val)=i.val ∧ part (group i.val k.val)=k.val := by decide
  exact closed ⟨k,hk⟩ ⟨p,bound⟩ hp

def read (xs : Proof) (j : Nat) : Byte := xs[j]?.getD 0
def chunk (v : Byte) (p : Nat) : Byte := (v >>> (2*p)) &&& 3
def overlay (v hi : Byte) := (v &&& 63) ||| (hi <<< 6)
def lower (v : Byte) := v &&& 63
def upper (v : Byte) := v >>> 6
def packedAt (f : Nat → Byte) (a : Nat) : Byte :=
  if used a then let c:=candidate a; overlay (f a) (chunk (f (70080+source c)) (part c))
  else f a
def packed (xs : Proof) : Proof := (List.range 70080).map (packedAt (read xs))
def restored (f : Nat → Byte) (k : Nat) : Byte :=
  let g p:=upper (f (carrier (group k p)))
  g 0 ||| (g 1 <<< 2) ||| (g 2 <<< 4) ||| (if k%30=29 then (0 : Byte) else g 3 <<< 6)
def wideAt (f : Nat → Byte) (a : Nat) : Byte :=
  if a<70080 then if used a then lower (f a) else f a else restored f (a-70080)
def wide (xs : Proof) : Proof := (List.range 70410).map (wideAt (read xs))
theorem packed_length (xs : Proof) : (packed xs).length=70080 := by simp [packed]
theorem wide_length (xs : Proof) : (wide xs).length=70410 := by simp [wide]

theorem read_range (f : Nat → Byte) (i n : Nat) (h : i<n) :
    read ((List.range n).map f) i=f i := by
  simp only [read,List.getElem?_map,List.getElem?_range h,Option.map_some,Option.getD_some]
theorem packed_byte (xs : Proof) (a : Nat) (h : a<70080) :
    read (packed xs) a=packedAt (read xs) a := read_range _ _ _ h
theorem wide_byte (xs : Proof) (a : Nat) (h : a<70410) :
    read (wide xs) a=wideAt (read xs) a := read_range _ _ _ h

private theorem lower_overlay (a b : Byte) : lower (overlay a b)=lower a := by unfold lower overlay;apply BitVec.eq_of_getLsbD_eq <;> intro bit bounded <;> interval_cases bit <;> simp (config := {decide := true})
private theorem upper_overlay (a b : Byte) : upper (overlay a b)=b &&& 3 := by unfold upper overlay;apply BitVec.eq_of_getLsbD_eq <;> intro bit bounded <;> interval_cases bit <;> simp (config := {decide := true})
private theorem chunk_low (a : Byte) (i : Nat) : chunk a i &&& 3=chunk a i := by
  simp [chunk,BitVec.and_assoc]
private theorem assemble : ∀ a : Byte,chunk a 0 ||| (chunk a 1 <<< 2) ||| (chunk a 2 <<< 4) ||| (chunk a 3 <<< 6)=a := by decide
private theorem assembleFinal : ∀ a : Byte,lower a=a →
    chunk a 0 ||| (chunk a 1 <<< 2) ||| (chunk a 2 <<< 4) ||| 0=a := by decide

structure Canonical (f : Nat→Byte) : Prop where
  spare : ∀ c<1309,lower (f (carrier c))=f (carrier c)
  finalByte : ∀ k<330,k%30=29 → lower (f (70080+k))=f (70080+k)

theorem fragment (f : Nat→Byte) (k p : Nat) (hk : k<330) (hp : p<pieces k) :
    upper (packedAt f (carrier (group k p)))=chunk (f (70080+k)) p := by
  obtain ⟨hc,hs,ht⟩:=groupSpec k p hk hp
  simp only [packedAt,if_pos (usedCarrier _ hc),(location _ hc).1,hs,ht,upper_overlay,chunk_low]

theorem restore_pack (xs : Proof) (can : Canonical (read xs)) (k : Nat) (hk : k<330) :
    restored (read (packed xs)) k=read xs (70080+k) := by
  have atPart (p : Nat) (hp : p<pieces k) :
      upper (read (packed xs) (carrier (group k p)))=chunk (read xs (70080+k)) p := by
    rw [packed_byte _ _ (location _ (groupSpec _ _ hk hp).1).2,fragment _ _ _ hk hp]
  unfold restored
  dsimp only
  by_cases last : k%30=29
  · simp only [if_pos last];rw [atPart 0 (by simp [pieces,last]),atPart 1 (by simp [pieces,last]),atPart 2 (by simp [pieces,last])]
    exact assembleFinal _ (can.finalByte k hk last)
  · simp only [if_neg last];rw [atPart 0 (by simp [pieces,last]),atPart 1 (by simp [pieces,last]),atPart 2 (by simp [pieces,last]),atPart 3 (by simp [pieces,last])]
    exact assemble _

theorem byte_inverse (xs : Proof) (can : Canonical (read xs)) (a : Nat) (h : a<70410) :
    read (wide (packed xs)) a=read xs a := by
  rw [wide_byte _ _ h,wideAt];split
  · rename_i inside;rw [packed_byte _ _ inside,packedAt]
    by_cases yes : used a
    · rw [if_pos yes,if_pos yes,lower_overlay]
      exact yes.2 ▸ can.spare _ yes.1
    · rw [if_neg yes,if_neg yes]
  · rename_i after;rw [restore_pack xs can _ (by omega),show 70080+(a-70080)=a by omega]

theorem inverse (xs : Proof) (len : xs.length=70410) (can : Canonical (read xs)) :
    wide (packed xs)=xs := by
  apply List.ext_getElem
  · rw [wide_length,len]
  · intro i hl hr
    have e:=byte_inverse xs can i (by rw [←len];exact hr)
    simpa only [read,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,Option.getD_some] using e

end CommitGolfCandidate.S4.Carry
