import CommitGolf.Statements
set_option Elab.async false
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
def localWide (record : Bool) (i : Nat) :=
  if record && decide (120≤ i) then 120+32*((i-120)/30)+(i-120)%30 else i
def localShort (record : Bool) (i : Nat) : Option Nat :=
  if record then
    if i<120 then some i else
      if (i-120)%32<30 then some (120+30*((i-120)/32)+(i-120)%32) else none
  else if i<30 then some i else none
def narrowIndex (i : Nat) :=
  if i<65280 then 536*(i/510)+localWide true (i%510)
  else 68608+32*((i-65280)/30)+localWide false ((i-65280)%30)
def wideIndex (i : Nat) : Option Nat :=
  if i<68608 then (localShort true (i%536)).map (510*(i/536)+·)
  else (localShort false ((i-68608)%32)).map (65280+30*((i-68608)/32)+·)

def pack (wide : Proof) : Proof := (List.range 69120).map fun i=>wide[narrowIndex i]?.getD 0
def unpack (short : Proof) : Proof := (List.range 72704).map fun i=>
  ((wideIndex i).bind (fun j=>short[j]?)).getD 0

@[simp] theorem pack_length (p : Proof) : (pack p).length=69120 := by simp [pack]
@[simp] theorem unpack_length (p : Proof) : (unpack p).length=72704 := by simp [unpack]

theorem localBounds (r : Bool) (i : Nat) (hi : i<(if r then 510 else 30)) :
    i≤localWide r i ∧ localWide r i<(if r then 536 else 32) ∧ localShort r (localWide r i)=some i := by
  cases r
  · exact (show ∀ j : Fin 30, j.val≤localWide false j.val ∧ localWide false j.val<32 ∧
        localShort false (localWide false j.val)=some j.val by decide) ⟨i,hi⟩
  · exact (show ∀ j : Fin 510, j.val≤localWide true j.val ∧ localWide true j.val<536 ∧
        localShort true (localWide true j.val)=some j.val by decide) ⟨i,hi⟩

theorem blockNarrow (r k i : Nat) (inside : k<128) (lo : i<(if r=0 then 510 else 30)) :
    narrowIndex ((if r=0 then 510*k else 65280+30*k)+i)=
      (if r=0 then 536*k else 68608+32*k)+localWide (decide (r=0)) i := by
  by_cases e : r=0
  · simp only [e,ite_true,decide_true] at lo ⊢
    rw [narrowIndex,if_pos (by omega),show (510*k+i)/510=k by omega,show (510*k+i)%510=i by omega]
  · simp only [e,ite_false,decide_false] at lo ⊢
    rw [narrowIndex,if_neg (by omega),show (65280+30*k+i-65280)/30=k by omega,
      show (65280+30*k+i-65280)%30=i by omega]

theorem blockWide (r k i : Nat) (inside : k<128) (lo : i<(if r=0 then 536 else 32)) :
    wideIndex ((if r=0 then 536*k else 68608+32*k)+i)=
      (localShort (decide (r=0)) i).map ((if r=0 then 510*k else 65280+30*k)+·) := by
  by_cases e : r=0
  · simp only [e,ite_true,decide_true] at lo ⊢
    rw [wideIndex,if_pos (by omega),show (536*k+i)/536=k by omega,show (536*k+i)%536=i by omega]
  · simp only [e,ite_false,decide_false] at lo ⊢
    rw [wideIndex,if_neg (by omega),show (68608+32*k+i-68608)/32=k by omega,
      show (68608+32*k+i-68608)%32=i by omega]

theorem widen_narrow (i : Nat) (hi : i<69120) :
    narrowIndex i < 72704 ∧ wideIndex (narrowIndex i)=some i := by
  by_cases recs : i<65280
  · let k:=i/510;let b:=i%510
    have hk : k<128 := by dsimp [k];omega
    have hb : b<510 := Nat.mod_lt _ (by decide)
    have pos : 510*k+b=i := by dsimp [k,b];omega
    have limit:=localBounds true b hb
    have wide : narrowIndex i=536*k+localWide true b := pos ▸ blockNarrow 0 k b hk hb
    rw [wide]
    refine ⟨by have h : localWide true b<536:=limit.2.1;omega,?_⟩
    have eqn:=blockWide 0 k (localWide true b) hk limit.2.1
    change wideIndex (536*k+localWide true b)=(localShort true (localWide true b)).map ((510*k)+·) at eqn
    rw [eqn,limit.2.2];exact congrArg some pos
  · let k:=(i-65280)/30;let b:=(i-65280)%30
    have hk : k<128 := by dsimp [k];omega
    have hb : b<30 := Nat.mod_lt _ (by decide)
    have pos : 65280+30*k+b=i := by dsimp [k,b];omega
    have limit:=localBounds false b hb
    have wide : narrowIndex i=68608+32*k+localWide false b := pos ▸ blockNarrow 1 k b hk hb
    rw [wide]
    refine ⟨by have h : localWide false b<32:=limit.2.1;omega,?_⟩
    have eqn:=blockWide 1 k (localWide false b) hk limit.2.1
    change wideIndex (68608+32*k+localWide false b)=(localShort false (localWide false b)).map ((65280+30*k)+·) at eqn
    rw [eqn,limit.2.2];exact congrArg some pos

end CommitGolfCandidate.Trunc
