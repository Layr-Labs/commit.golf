import CommitGolfCandidate.S4Carrier
namespace CommitGolfCandidate.S4.Carry
open CommitGolf
def prev (c : Nat) := if c=0 then 0 else carrier (c-1)
def delta (c : Nat) := carrier c-prev c
set_option maxRecDepth 10000 in
private theorem gaps : ∀ c : Fin 1309,prev c≤carrier c ∧ delta c≤270 := by decide
theorem walk (c : Nat) (b : c<1309) : prev c+delta c=carrier c ∧ delta c≤270 :=
  ⟨Nat.add_sub_of_le (gaps ⟨c,b⟩).1,(gaps ⟨c,b⟩).2⟩

theorem group_next (k : Nat) : group k (pieces k)=group (k+1) 0 := by
  unfold group pieces;split <;> omega

def prefixValue (f : Nat→Byte) (k : Nat) : Nat→Byte
  | 0=>0
  | p+1=>prefixValue f k p ||| (upper (f (carrier (group k p))) <<< (2*p))
theorem assembled (f : Nat→Byte) (k : Nat) : prefixValue f k (pieces k)=restored f k := by
  by_cases b:k%30=29 <;> simp [pieces,b,prefixValue,restored]

def fieldValue (dec : Bool) (f : Nat→Byte) (c : Nat) :=
  if dec then lower (f (carrier c)) else overlay (f (carrier c)) (chunk (f (70080+source c)) (part c))

/-- Values in the proof after processing c carriers and completing k omitted bytes. -/
def state (dec : Bool) (f : Nat→Byte) (k c a : Nat) : Byte :=
  if used a ∧ candidate a<c then fieldValue dec f (candidate a)
  else if dec=true ∧ 70080≤a ∧ a<70080+k then restored f (a-70080) else f a

theorem start (dec : Bool) (f : Nat→Byte) (a : Nat) : state dec f 0 0 a=f a := by
  unfold state;simp

theorem untouched (dec : Bool) (f : Nat→Byte) (k c : Nat) (hc : c<1309) :
    state dec f k c (carrier c)=f (carrier c) := by
  obtain ⟨idx,lo⟩:=location c hc
  simp [state,idx,show ¬70080≤carrier c by omega]

theorem readTail (f : Nat→Byte) (k c : Nat) : state false f k c (70080+k)=f (70080+k) := by
  have no : ¬used (70080+k):=by
    intro h;have bd:=(location _ h.1).2;rw [h.2] at bd;omega
  simp [state,no]

theorem writeField (dec : Bool) (f : Nat→Byte) (k c a : Nat) (b : c<1309) :
    state dec f k (c+1) a=if a=carrier c then fieldValue dec f c else state dec f k c a := by
  by_cases yes : a=carrier c
  · subst a;simp only [state,usedCarrier c b,(location c b).1,Nat.lt_succ_self,true_and,ite_true]
  · rw [if_neg yes];unfold state
    by_cases usedA : used a
    · have ne : candidate a≠c:=by intro e;exact yes (usedA.2.symm.trans (congrArg carrier e))
      have same : candidate a<c+1 ↔ candidate a<c:=by omega
      simp only [usedA,true_and,same]
    · simp [usedA]

theorem completeByte (dec : Bool) (f : Nat→Byte) (k c a : Nat) :
    state dec f (k+1) c a=if dec=true ∧ a=70080+k then restored f k else state dec f k c a := by
  unfold state
  by_cases tail : a=70080+k
  · subst a;have no : ¬used (70080+k):=by
      intro h;have bd:=(location _ h.1).2;rw [h.2] at bd;omega
    cases dec <;> simp [no]
  · have agree : a<70080+(k+1) ↔ a<70080+k:=by omega
    simp only [tail,and_false,ite_false,agree]

theorem encoded (f : Nat→Byte) (a : Nat) : state false f 330 1309 a=packedAt f a := by
  by_cases yes : used a
  · simp [state,packedAt,yes,yes.1,fieldValue,yes.2]
  · simp [state,packedAt,yes]

theorem decoded (f : Nat→Byte) (a : Nat) (ha : a<70410) : state true f 330 1309 a=wideAt f a := by
  by_cases yes : used a
  · have bd:= (location _ yes.1).2;rw [yes.2] at bd
    simp [state,wideAt,yes,yes.1,bd,fieldValue,yes.2]
  · by_cases inside : a<70080
    · simp [state,wideAt,yes,inside,show ¬70080≤a by omega]
    · simp [state,wideAt,yes,inside,show 70080≤a by omega,ha]

end CommitGolfCandidate.S4.Carry
