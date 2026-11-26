import CommitGolf.Artifact
import Mathlib.Tactic
namespace CommitGolfCandidate.R4.ROM
open CommitGolf ArtifactEncoding

def aligned : {n : Nat} → Packed n → Bool
  | _, .chunk n _ => decide (n≤64)
  | _, @Packed.join l _ a b => decide (l%64=0) && aligned a && aligned b

def blockAt : {n : Nat} → Packed n → Nat → Nat
  | _, .chunk _ payload, _ => payload
  | _, @Packed.join l _ a b, k => if 64*k<l then blockAt a k else blockAt b (k-l/64)

theorem readBlock {n : Nat} (p : Packed n) (ok : aligned p) (i : Fin n) :
    p.get 32 i = BitVec.ofNat 32 (blockAt p (i.val/64) >>> (32*(i.val%64))) := by
  induction p with
  | chunk n payload =>
    have small : n≤64 := of_decide_eq_true ok
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt small)]
    rfl
  | @join l r a b left right =>
    simp only [aligned,Bool.and_eq_true_iff,decide_eq_true_eq] at ok
    by_cases before : i.val<l
    · rw [get_join_left _ _ _ _ before,blockAt,if_pos (by omega)]
      exact left ok.1.2 ⟨i,before⟩
    · rw [get_join_right _ _ _ _ before,blockAt,if_neg (by omega)]
      have e:=right ok.2 ⟨i.val-l,by have:=i.isLt;omega⟩
      simpa only [Fin.val_mk,show (i.val-l)/64=i.val/64-l/64 by omega,show (i.val-l)%64=i.val%64 by omega] using e

def payload (k : Nat) := blockAt Artifact.commitCode k
theorem codeAligned : aligned Artifact.commitCode := by decide +kernel
def extract (b j : Nat) := BitVec.ofNat 32 (payload b >>> (32*j))

-- A 64-word physical chunk has the same payload as one of the representative chunks.
-- Keep the two partial endpoint chunks, which may also contain unrelated instructions.
def tag (s e w b : Nat) := if b=s/64 then 0 else if b=e/64 then 1 else 2+(b-(s/64+1))%w
def representative (s e t : Nat) := if t=0 then s/64 else if t=1 then e/64 else s/64+1+(t-2)
def bankChunks (s e w : Nat) := ∀ k : Fin (e/64-s/64+1),
    let b:=s/64+k.val
    payload b=payload (representative s e (tag s e w b))
def bankWords (s e w : Nat) (word : Nat→BitVec 32) := ∀ t : Fin (w+2),∀ j : Fin 64,
    let i:=representative s e t.val*64+j.val
    s ≤ i → i≤e → extract (representative s e t.val) j.val=word ((i-s)%w)
instance (s e w : Nat) : Decidable (bankChunks s e w) := inferInstanceAs (Decidable (∀ k : Fin _, _))
instance (s e w : Nat) (f : Nat→BitVec 32) : Decidable (bankWords s e w f) := inferInstanceAs (Decidable (∀ t : Fin _, ∀ j : Fin 64, _))
def allowed (w : Nat) := w=2 ∨ w=3 ∨ w=6 ∨ w=8 ∨ w=12

theorem bankRead {s e w : Nat} {word : Nat→BitVec 32} (ww : allowed w)
    (same : bankChunks s e w) (values : bankWords s e w word) (i : Nat) (lo : s ≤ i) (hi : i≤e)
    (valid : i<262123) : Artifact.commitCode.get 32 ⟨i,valid⟩=word ((i-s)%w) := by
  let b:=i/64
  let t:=tag s e w b
  let rep:=representative s e t
  have fit : t<w+2:=by
    have z : 0<w:=by rcases ww with h|h|h|h|h <;> omega
    have h:=Nat.mod_lt (b-(s/64+1)) z
    dsimp only [t,tag];split_ifs <;> omega
  have rel : b≤e/64 ∧ s/64≤b:=by dsimp [b];omega
  have eqv:=same ⟨b-s/64,by omega⟩
  change payload (s/64+(b-s/64))=_ at eqv
  rw [show s/64+(b-s/64)=b by omega] at eqv
  let j:=i%64
  have bounds : s≤rep*64+j ∧ rep*64+j≤e ∧ (rep*64+j-s)%w=(i-s)%w := by
    dsimp only [rep,t,tag,representative,b,j]
    by_cases first : i/64=s/64
    · rw [if_pos first];simp only [ite_true];rw [show s/64*64+i%64=i by omega];exact ⟨lo,hi,rfl⟩
    by_cases last : i/64=e/64
    · rw [if_neg first,if_pos last];simp only [show ¬(1:Nat)=0 by decide,ite_false,ite_true];rw [show e/64*64+i%64=i by omega]; exact ⟨lo,hi,rfl⟩
    have z : 0<w:=by rcases ww with h|h|h|h|h <;> omega
    have less : (i/64-(s/64+1))%w ≤ i/64-(s/64+1):=Nat.mod_le _ _
    simp only [if_neg first,if_neg last]
    rw [if_neg (by omega),if_neg (by omega)]
    rcases ww with h|h|h|h|h <;> subst w <;> omega
  have got:=values ⟨t,fit⟩ ⟨j,Nat.mod_lt _ (by decide)⟩ bounds.1 bounds.2.1
  change extract rep j=word ((rep*64+j-s)%w) at got
  rw [bounds.2.2] at got
  rw [readBlock _ codeAligned];change extract b j=_;unfold extract;rw [eqv];exact got
end CommitGolfCandidate.R4.ROM
