import CommitGolfCandidate.TruncWireFrame
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 400000

def wBase (record : Bool) (r : Nat) := if record then 536*r else 68608+32*r
def sBase (record : Bool) (r : Nat) := if record then 510*r else 65280+30*r
def sourceStart (b record : Bool) (r : Nat) := if b then sBase record r else wBase record r
def destStart (b record : Bool) (r : Nat) := if b then wBase record r else sBase record r
def boundary (b record : Bool) (r j : Nat) := destStart b record r+(if b then wide record-2*j else 2*j)

theorem wWithin (recFlag : Bool) (r : Nat) (h : r<128) :
    wBase recFlag r+wide recFlag≤72704 ∧ wBase recFlag r%2=0 := by
  cases recFlag <;> simp [wBase,wide] <;> omega
theorem sWithin (recFlag : Bool) (r : Nat) (h : r<128) :
    sBase recFlag r+short recFlag≤69120 ∧ sBase recFlag r%2=0 := by
  cases recFlag <;> simp [sBase,short] <;> omega

theorem narrowAt (f : Bool) (r x : Nat) (hr : r<128) (hx : x<short f) :
    narrowIndex (sBase f r+x)=wBase f r+localWide f x := by
  cases f
  · exact blockNarrow 1 r x hr hx
  · exact blockNarrow 0 r x hr hx
theorem wideAt (f : Bool) (r x : Nat) (hr : r<128) (hx : x<wide f) :
    wideIndex (wBase f r+x)=(localShort f x).map (sBase f r+·) := by
  cases f
  · exact blockWide 1 r x hr hx
  · exact blockWide 0 r x hr hx

structure LocalFacts (b f : Bool) (j : Nat) : Prop where
  target : (item b f j).dest+2≤ if b then wide f else short f
  even : (item b f j).dest%2=0
  source : ∀ a∈(item b f j).source,a+2≤(if b then short f else wide f) ∧ a%2=0 ∧
    (if b then a≤(item b f j).dest else (item b f j).dest≤a)
  mapping : ∀ k<2,(if b then localShort f ((item b f j).dest+k) else some (localWide f ((item b f j).dest+k))) =
    (item b f j).source.map (·+k)

private def localTest (b f : Bool) (j : Nat) : Bool :=
  let m:=item b f j
  decide (m.dest+2≤(if b then wide f else short f) ∧ m.dest%2=0) &&
    (m.source.all fun a=>decide (a+2≤(if b then short f else wide f) ∧ a%2=0 ∧
      (if b then a≤m.dest else m.dest≤a))) &&
    ([0,1].all fun k=> decide ((if b then localShort f (m.dest+k) else some (localWide f (m.dest+k))) =
      m.source.map (·+k)))

theorem localFacts (b f : Bool) (j : Nat) (hj : j<count b f) : LocalFacts b f j := by
  have tab : ∀ x y : Bool, ((List.range (count x y)).all (localTest x y))=true := by decide
  have yes:=List.all_eq_true.mp (tab b f) j (List.mem_range.mpr hj)
  simp only [localTest,Bool.and_eq_true,decide_eq_true_eq,List.all_cons,List.all_nil,Bool.and_true] at yes
  refine ⟨yes.1.1.1,yes.1.1.2,?_,?_⟩
  · intro a ha
    have eq : (item b f j).source=some a := ha
    have ok:=yes.1.2;rw [eq] at ok;simpa using ok
  · intro k hk;interval_cases k
    · simpa using yes.2.1
    · simpa using yes.2.2

theorem absoluteFacts (b f : Bool) (r j : Nat) (hr : r<128) (hj : j<count b f) :
    let m:=item b f j
    let dst:=destStart b f r+m.dest
    let src:=m.source.map (sourceStart b f r+·)
    dst+2≤(if b then 72704 else 69120) ∧ dst%2=0 ∧
    (∀ a∈src,a+2≤72704 ∧ a%2=0 ∧ (if b then a≤dst else dst≤a)) ∧
    (∀ k<2,srcIndex b (dst+k)=src.map (·+k)) := by
  dsimp only
  have prop:=localFacts b f j hj
  have w:=wWithin f r hr;have s:=sWithin f r hr
  have baseOrder : sBase f r≤wBase f r := by cases f <;> simp [sBase,wBase] <;> omega
  cases b
  · have a:=prop.target;have e:=prop.even
    simp only [Bool.false_eq_true,ite_false,destStart,sourceStart,srcIndex] at a ⊢
    refine ⟨by omega,by omega,?_,?_⟩
    · intro n member
      cases h : (item false f j).source with
      | none => simp [h] at member
      | some x =>
        have ok:=prop.source x h
        change n∈(item false f j).source.map (wBase f r+·) at member
        simp [h] at member;subst n
        simp only [Bool.false_eq_true,ite_false] at ok;omega
    · intro k hk
      rw [Nat.add_assoc,narrowAt f r _ hr (by omega)]
      have map:=prop.mapping k hk
      change some (localWide f ((item false f j).dest+k))=_ at map
      cases h : (item false f j).source <;> simp [h] at map ⊢ <;> omega
  · have a:=prop.target;have e:=prop.even
    simp only [ite_true,destStart,sourceStart,srcIndex] at a ⊢
    refine ⟨by omega,by omega,?_,?_⟩
    · intro n member
      cases h : (item true f j).source with
      | none => simp [h] at member
      | some x =>
        have ok:=prop.source x h
        simp [h] at member;subst n
        simp only [ite_true] at ok;omega
    · intro k hk
      rw [Nat.add_assoc,wideAt f r _ hr (by omega)]
      have map:=prop.mapping k hk
      change localShort f ((item true f j).dest+k)=_ at map
      rw [map]
      cases (item true f j).source <;> simp [Nat.add_assoc]
end CommitGolfCandidate.Trunc.Wire
