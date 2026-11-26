import CommitGolf.Statements
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
def localWide (record : Bool) (i : Nat) :=
  if record && decide (112≤ i) then 112+32*((i-112)/30)+(i-112)%30 else i
def localShort (record : Bool) (i : Nat) : Option Nat :=
  if record then
    if i<112 then some i else
      if (i-112)%32<30 then some (112+30*((i-112)/32)+(i-112)%32) else none
  else if i<30 then some i else none
def narrowIndex (i : Nat) :=
  if i<64256 then 528*(i/502)+localWide true (i%502)
  else 67584+32*((i-64256)/30)+localWide false ((i-64256)%30)
def wideIndex (i : Nat) : Option Nat :=
  if i<67584 then (localShort true (i%528)).map (502*(i/528)+·)
  else (localShort false ((i-67584)%32)).map (64256+30*((i-67584)/32)+·)

def pack (wide : Proof) : Proof := (List.range 68096).map fun i=>wide[narrowIndex i]?.getD 0
def unpack (short : Proof) : Proof := (List.range 71680).map fun i=>
  ((wideIndex i).bind (fun j=>short[j]?)).getD 0

@[simp] theorem pack_length (p : Proof) : (pack p).length=68096 := by simp [pack]
@[simp] theorem unpack_length (p : Proof) : (unpack p).length=71680 := by simp [unpack]

theorem localBounds (r : Bool) (i : Nat) (hi : i<(if r then 502 else 30)) :
    i≤localWide r i ∧ localWide r i<(if r then 528 else 32) ∧ localShort r (localWide r i)=some i := by
  cases r
  · exact (show ∀ j : Fin 30, j.val≤localWide false j.val ∧ localWide false j.val<32 ∧
        localShort false (localWide false j.val)=some j.val by decide) ⟨i,hi⟩
  · exact (show ∀ j : Fin 502, j.val≤localWide true j.val ∧ localWide true j.val<528 ∧
        localShort true (localWide true j.val)=some j.val by decide) ⟨i,hi⟩

theorem blockNarrow (r k i : Nat) (inside : k<128) (lo : i<(if r=0 then 502 else 30)) :
    narrowIndex ((if r=0 then 502*k else 64256+30*k)+i)=
      (if r=0 then 528*k else 67584+32*k)+localWide (decide (r=0)) i := by
  by_cases e : r=0
  · simp only [e,ite_true,decide_true] at lo ⊢
    rw [narrowIndex,if_pos (by omega),show (502*k+i)/502=k by omega,show (502*k+i)%502=i by omega]
  · simp only [e,ite_false,decide_false] at lo ⊢
    rw [narrowIndex,if_neg (by omega),show (64256+30*k+i-64256)/30=k by omega,
      show (64256+30*k+i-64256)%30=i by omega]

theorem blockWide (r k i : Nat) (inside : k<128) (lo : i<(if r=0 then 528 else 32)) :
    wideIndex ((if r=0 then 528*k else 67584+32*k)+i)=
      (localShort (decide (r=0)) i).map ((if r=0 then 502*k else 64256+30*k)+·) := by
  by_cases e : r=0
  · simp only [e,ite_true,decide_true] at lo ⊢
    rw [wideIndex,if_pos (by omega),show (528*k+i)/528=k by omega,show (528*k+i)%528=i by omega]
  · simp only [e,ite_false,decide_false] at lo ⊢
    rw [wideIndex,if_neg (by omega),show (67584+32*k+i-67584)/32=k by omega,
      show (67584+32*k+i-67584)%32=i by omega]

theorem widen_narrow (i : Nat) (hi : i<68096) :
    narrowIndex i < 71680 ∧ wideIndex (narrowIndex i)=some i := by
  by_cases recs : i<64256
  · let k:=i/502;let b:=i%502
    have hk : k<128 := by dsimp [k];omega
    have hb : b<502 := Nat.mod_lt _ (by decide)
    have pos : 502*k+b=i := by dsimp [k,b];omega
    have limit:=localBounds true b hb
    have wide : narrowIndex i=528*k+localWide true b := pos ▸ blockNarrow 0 k b hk hb
    rw [wide]
    refine ⟨by have h : localWide true b<528:=limit.2.1;omega,?_⟩
    have eqn:=blockWide 0 k (localWide true b) hk limit.2.1
    change wideIndex (528*k+localWide true b)=(localShort true (localWide true b)).map ((502*k)+·) at eqn
    rw [eqn,limit.2.2];exact congrArg some pos
  · let k:=(i-64256)/30;let b:=(i-64256)%30
    have hk : k<128 := by dsimp [k];omega
    have hb : b<30 := Nat.mod_lt _ (by decide)
    have pos : 64256+30*k+b=i := by dsimp [k,b];omega
    have limit:=localBounds false b hb
    have wide : narrowIndex i=67584+32*k+localWide false b := pos ▸ blockNarrow 1 k b hk hb
    rw [wide]
    refine ⟨by have h : localWide false b<32:=limit.2.1;omega,?_⟩
    have eqn:=blockWide 1 k (localWide false b) hk limit.2.1
    change wideIndex (67584+32*k+localWide false b)=(localShort false (localWide false b)).map ((64256+30*k)+·) at eqn
    rw [eqn,limit.2.2];exact congrArg some pos

end CommitGolfCandidate.Trunc
