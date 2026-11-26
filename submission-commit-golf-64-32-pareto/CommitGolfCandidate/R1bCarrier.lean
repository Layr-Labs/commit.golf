import CommitGolf.Statements

namespace CommitGolfCandidate.R1b.Carry
open CommitGolf
set_option maxRecDepth 8192

def carrier (c : Nat) := if c<1280 then 500*(c/10)+229+30*(c%10) else 64029+30*(c-1280)
def candidate (a : Nat) := if a<64000 then 10*(a/500)+(a%500-229)/30 else 1280+(a-64029)/30
def used (a : Nat) := candidate a<1396 ∧ carrier (candidate a)=a
instance (a : Nat) : Decidable (used a) := inferInstanceAs (Decidable (_ ∧ _))
theorem location (c : Nat) (hc : c<1396) :
    candidate (carrier c)=c ∧ carrier c<67488 := by
  have bounded : ∀ i : Fin 1396, candidate (carrier i.val) = i.val ∧ carrier i.val < 67488 := by decide
  exact bounded ⟨c,hc⟩

theorem usedCarrier (c : Nat) (hc : c<1396) : used (carrier c) := by
  unfold used;rw [(location c hc).1];exact ⟨hc,rfl⟩

def group (k p : Nat) := 119*((k+8)/30)+4*((k+8)%30)+p-32
def source (c : Nat) := 30*((c+32)/119)+((c+32)%119)/4-8
def part (c : Nat) := (c+32)%119%4
def pieces (k : Nat) := if (k+8)%30=29 then 3 else 4
theorem groupSpec (k p : Nat) (hk : k<352) (hp : p<pieces k) :
    group k p<1396 ∧ source (group k p)=k ∧ part (group k p)=p := by
  have bound : p<4:=by unfold pieces at hp;split at hp <;> omega
  have closed : ∀ i : Fin 352,∀ k : Fin 4,k.val<pieces i.val →
      group i.val k.val<1396 ∧ source (group i.val k.val)=i.val ∧ part (group i.val k.val)=k.val := by decide
  exact closed ⟨k,hk⟩ ⟨p,bound⟩ hp

def read (xs : Proof) (j : Nat) : Byte := xs[j]?.getD 0
def chunk (v : Byte) (p : Nat) : Byte := (v >>> (2*p)) &&& 3
def overlay (v hi : Byte) := (v &&& 63) ||| (hi <<< 6)
def lower (v : Byte) := v &&& 63
def upper (v : Byte) := v >>> 6
def packedAt (f : Nat → Byte) (a : Nat) : Byte :=
  if used a then let c:=candidate a; overlay (f a) (chunk (f (67488+source c)) (part c))
  else f a
def packed (xs : Proof) : Proof := (List.range 67488).map (packedAt (read xs))
def restored (f : Nat → Byte) (k : Nat) : Byte :=
  let g p:=upper (f (carrier (group k p)))
  g 0 ||| (g 1 <<< 2) ||| (g 2 <<< 4) ||| (if (k+8)%30=29 then (0 : Byte) else g 3 <<< 6)
def wideAt (f : Nat → Byte) (a : Nat) : Byte :=
  if a<67488 then if used a then lower (f a) else f a else restored f (a-67488)
def wide (xs : Proof) : Proof := (List.range 67840).map (wideAt (read xs))
theorem packed_length (xs : Proof) : (packed xs).length=67488 := by simp [packed]
theorem wide_length (xs : Proof) : (wide xs).length=67840 := by simp [wide]

theorem read_range (f : Nat → Byte) (i n : Nat) (h : i<n) :
    read ((List.range n).map f) i=f i := by
  simp only [read,List.getElem?_map,List.getElem?_range h,Option.map_some,Option.getD_some]
theorem packed_byte (xs : Proof) (a : Nat) (h : a<67488) :
    read (packed xs) a=packedAt (read xs) a := read_range _ _ _ h
theorem wide_byte (xs : Proof) (a : Nat) (h : a<67840) :
    read (wide xs) a=wideAt (read xs) a := read_range _ _ _ h

private theorem lower_overlay (a b : Byte) : lower (overlay a b)=lower a := by unfold lower overlay;apply BitVec.eq_of_getLsbD_eq <;> intro bit bounded <;> interval_cases bit <;> simp (config := {decide := true})
private theorem upper_overlay (a b : Byte) : upper (overlay a b)=b &&& 3 := by unfold upper overlay;apply BitVec.eq_of_getLsbD_eq <;> intro bit bounded <;> interval_cases bit <;> simp (config := {decide := true})
private theorem chunk_low (a : Byte) (i : Nat) : chunk a i &&& 3=chunk a i := by
  simp [chunk,BitVec.and_assoc]
private theorem assemble : ∀ a : Byte,chunk a 0 ||| (chunk a 1 <<< 2) ||| (chunk a 2 <<< 4) ||| (chunk a 3 <<< 6)=a := by decide
private theorem assembleFinal : ∀ a : Byte,lower a=a →
    chunk a 0 ||| (chunk a 1 <<< 2) ||| (chunk a 2 <<< 4) ||| 0=a := by decide

structure Canonical (f : Nat→Byte) : Prop where
  spare : ∀ c<1396,lower (f (carrier c))=f (carrier c)
  finalByte : ∀ k<352,(k+8)%30=29 → lower (f (67488+k))=f (67488+k)

theorem fragment (f : Nat→Byte) (k p : Nat) (hk : k<352) (hp : p<pieces k) :
    upper (packedAt f (carrier (group k p)))=chunk (f (67488+k)) p := by
  obtain ⟨hc,hs,ht⟩:=groupSpec k p hk hp
  simp only [packedAt,if_pos (usedCarrier _ hc),(location _ hc).1,hs,ht,upper_overlay,chunk_low]

theorem restore_pack (xs : Proof) (can : Canonical (read xs)) (k : Nat) (hk : k<352) :
    restored (read (packed xs)) k=read xs (67488+k) := by
  have atPart (p : Nat) (hp : p<pieces k) :
      upper (read (packed xs) (carrier (group k p)))=chunk (read xs (67488+k)) p := by
    rw [packed_byte _ _ (location _ (groupSpec _ _ hk hp).1).2,fragment _ _ _ hk hp]
  unfold restored
  dsimp only
  by_cases last : (k+8)%30=29
  · simp only [if_pos last];rw [atPart 0 (by simp [pieces,last]),atPart 1 (by simp [pieces,last]),atPart 2 (by simp [pieces,last])]
    exact assembleFinal _ (can.finalByte k hk last)
  · simp only [if_neg last];rw [atPart 0 (by simp [pieces,last]),atPart 1 (by simp [pieces,last]),atPart 2 (by simp [pieces,last]),atPart 3 (by simp [pieces,last])]
    exact assemble _

theorem byte_inverse (xs : Proof) (can : Canonical (read xs)) (a : Nat) (h : a<67840) :
    read (wide (packed xs)) a=read xs a := by
  rw [wide_byte _ _ h,wideAt];split
  · rename_i inside;rw [packed_byte _ _ inside,packedAt]
    by_cases yes : used a
    · rw [if_pos yes,if_pos yes,lower_overlay]
      exact yes.2 ▸ can.spare _ yes.1
    · rw [if_neg yes,if_neg yes]
  · rename_i after;rw [restore_pack xs can _ (by omega),show 67488+(a-67488)=a by omega]

theorem inverse (xs : Proof) (len : xs.length=67840) (can : Canonical (read xs)) :
    wide (packed xs)=xs := by
  apply List.ext_getElem
  · rw [wide_length,len]
  · intro i hl hr
    have e:=byte_inverse xs can i (by rw [←len];exact hr)
    simpa only [read,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,Option.getD_some] using e


/-- The full codec zero-pads up to 128 frontier digests. The extra byte of the
short wire carries the actual number of frontier digests for the wide checker. -/
def batchEncode (xs : Proof) : Proof :=
  if xs.length ≤ 67488 then xs else packed xs ++ [BitVec.ofNat 8 ((xs.length-64000)/30)]

def batchDecode (xs : Proof) : Proof :=
  if xs.length = 67489 then
    (wide xs).take (64000+30*(read xs 67488).toNat)
  else xs

theorem canonical_roundtrip (xs : Proof) (f : Nat) (hf : f≤128)
    (len : xs.length=64000+30*f) (can : Canonical (read xs)) :
    batchDecode (batchEncode xs)=xs := by
  unfold batchEncode
  split
  · rename_i h
    rw [batchDecode,if_neg (by omega)]
  · rename_i h
    have size := packed_length xs
    let tag := BitVec.ofNat 8 ((xs.length-64000)/30)
    have tagNat : tag.toNat=f := by
      dsimp [tag]
      rw [len,show (64000+30*f-64000)/30=f by omega,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    let ys := packed xs ++ [tag]
    have ylen : ys.length=67489 := by simp [ys,size]
    have last : read ys 67488=tag := by
      simp [ys,read,List.getElem?_append,size]
    change batchDecode ys=xs
    rw [batchDecode,if_pos ylen,last,tagNat,←len]
    apply List.ext_getElem
    · simp [wide_length];omega
    · intro i hi hx
      have small : i<67840 := by omega
      have eqf (j : Nat) (hj : j<67488) : read ys j=read (packed xs) j := by
        simp [ys,read,List.getElem?_append,size,hj]
      have same : wideAt (read ys) i=wideAt (read (packed xs)) i := by
        unfold wideAt
        split
        · rename_i h';rw [eqf i h']
        · rename_i h'
          unfold restored
          have p (j : Nat) (bound : j<pieces (i-67488)) :
              upper (read ys (carrier (group (i-67488) j))) =
              upper (read (packed xs) (carrier (group (i-67488) j))) := by
            rw [eqf _ (location _ (groupSpec _ _ (by omega) bound).1).2]
          dsimp only
          by_cases final : ((i-67488+8)%30)=29
          · simp only [final,if_true];rw [p 0 (by simp [pieces,final]),p 1 (by simp [pieces,final]),p 2 (by simp [pieces,final])]
          · simp only [final,if_false];rw [p 0 (by simp [pieces,final]),p 1 (by simp [pieces,final]),p 2 (by simp [pieces,final]),p 3 (by simp [pieces,final])]
      have eq := byte_inverse xs can i small
      rw [wide_byte _ _ small,←same,←wide_byte _ _ small] at eq
      simpa only [List.getElem_take, read, List.getElem?_eq_getElem hx,
        List.getElem?_eq_getElem (show i<(wide ys).length by rw [wide_length];omega), Option.getD_some] using eq

theorem encoded_bound (xs : Proof) : (batchEncode xs).length≤67489 := by
  unfold batchEncode
  split
  · omega
  · simp [packed_length]

end CommitGolfCandidate.R1b.Carry
