import CommitGolfCandidate.NonceChainLayout
import CommitGolfCandidate.CounterSaltGame

namespace CommitGolfCandidate.Permutation.CounterSalt
open CommitGolf
open NonceChain (Word1600 Key Nonce Block)
set_option exponentiation.threshold 2048
set_option maxRecDepth 8000

abbrev groups : Nat := 1527808
/-- K1 (paired in-place salts): rank 0 (A leaf) takes reply bytes 0..16, rank 1 (C leaf) bytes
184..200, ranks 2..10 bytes `16 (j-1) .. 16 j`; bytes 160..184 stay hidden (the key slot). -/
def bitOffset (j : Fin 11) : Nat := if j.val=0 then 0 else if j.val=1 then 1472 else 128*(j.val-1)

def parts (w : Word1600) : Block × Key :=
  (fun j => w.extractLsb' (bitOffset j) 128, w.extractLsb' 1280 192)

private theorem parts_injective : Function.Injective parts := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases low : i < 1280
  · let j : Fin 11 := ⟨if i < 128 then 0 else i/128+1,by split <;> omega⟩
    have bit := congrArg (fun p : Block × Key => (p.1 j).getLsbD (i%128)) eq
    change (a.extractLsb' (bitOffset j) 128).getLsbD (i%128) =
      (b.extractLsb' (bitOffset j) 128).getLsbD (i%128) at bit
    have off : bitOffset j=128*(i/128) := by
      by_cases small : i < 128
      · simp [bitOffset,j,small]
      · simp [bitOffset,j,small]
    simpa only [off,BitVec.getLsbD_extractLsb',Nat.mod_lt i (by decide : 0<128),
      decide_true,Bool.true_and,Nat.div_add_mod] using bit
  · by_cases mid : i < 1472
    · have bit := congrArg (fun p : Block × Key => p.2.getLsbD (i-1280)) eq
      change (a.extractLsb' 1280 192).getLsbD (i-1280) =
        (b.extractLsb' 1280 192).getLsbD (i-1280) at bit
      simpa only [BitVec.getLsbD_extractLsb',show i-1280<192 by omega,decide_true,
        Bool.true_and,show 1280+(i-1280)=i by omega] using bit
    · have bit := congrArg (fun p : Block × Key => (p.1 1).getLsbD (i-1472)) eq
      change (a.extractLsb' 1472 128).getLsbD (i-1472) =
        (b.extractLsb' 1472 128).getLsbD (i-1472) at bit
      simpa only [BitVec.getLsbD_extractLsb',show i-1472<128 by omega,decide_true,
        Bool.true_and,show 1472+(i-1472)=i by omega] using bit

noncomputable def splitReply : Word1600 ≃ Block × Key :=
  Equiv.ofBijective parts ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨parts_injective,Fintype.card_congr NonceChain.blockEquiv⟩)

def firstLeaf (j : Fin groups) := 4096*(j.val/373)+11*(j.val%373)
/-- K1: the counter is the base address of the group's C leaf, the second leaf of the group. -/
def ctr (j : Fin groups) := BitVec.ofNat 64 (4096+256*(firstLeaf j+1))
def input (j : Fin groups) (k : Key) : Word1600 := (0#1344) ++ (k ++ ctr j)

theorem key_injective (i : Fin groups) : Function.Injective (input i) := by
  intro a b h
  have e := congrArg (fun w : Word1600 => w.extractLsb' 64 192) h
  simpa [input,BitVec.extractLsb'_append_eq_of_add_le (by decide : 64+192≤256),
    BitVec.extractLsb'_append_eq_of_le (by decide : 64≤64)] using e

theorem counter_distinct (k : Key) : Function.Injective (fun j => input j k) := by
  intro a b h
  have e := congrArg (fun w : Word1600 => w.extractLsb' 0 64) h
  have c : ctr a=ctr b := by
    have low (j : Fin groups) : (input j k).extractLsb' 0 64 = ctr j := by
      unfold input
      rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256)]
      exact BitVec.extractLsb'_append_eq_right
    exact (low a).symm.trans (e.trans (low b))
  have bound (j : Fin groups) : 4096+256*(firstLeaf j+1)<2^64 := by
    have sz : j.val < 1527808 := j.isLt
    unfold firstLeaf
    omega
  have en := congrArg BitVec.toNat c
  simp only [ctr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (bound a),Nat.mod_eq_of_lt (bound b)] at en
  unfold firstLeaf at en
  apply Fin.ext
  omega

def coord (i : Index) : Fin groups × Fin 11 :=
  (⟨373*(i.val/4096)+(i.val%4096)/11, by have hi : i.val<16777216 := i.isLt; unfold groups;omega⟩,
   ⟨(i.val%4096)%11, Nat.mod_lt _ (by decide)⟩)

def nonceAt (p : Fin groups → Block) (i : Index) := p (coord i).1 (coord i).2

private theorem coord_injective : Function.Injective coord := by
  intro a b eq
  have fst := congrArg (fun p : Fin groups × Fin 11 => p.1.val) eq
  have snd := congrArg (fun p : Fin groups × Fin 11 => p.2.val) eq
  dsimp only [coord] at fst snd
  have low (i : Index) : (i.val%4096)/11 < 373 := by omega
  have group : a.val/4096=b.val/4096 := by omega
  have major : (a.val%4096)/11=(b.val%4096)/11 := by omega
  apply Fin.ext
  omega

/-- Restricting an independent rectangular tape to the used, distinct coordinates
retains its uniform product distribution. -/
theorem iid_marginal (f : (Index → Nonce) → ℝ) :
    NonceChain.mean f = NonceChain.mean (fun p : Fin groups → Block => f (nonceAt p)) := by
  classical
  let rest := {j : Fin groups × Fin 11 // j ∉ Set.range coord}
  let picked := Equiv.ofInjective coord coord_injective
  let reindex := picked.symm.arrowCongr (Equiv.refl Nonce)
  let sub := Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range coord) (fun _ => Nonce)
  let e : (Fin groups → Block) ≃ (Index → Nonce) × (rest → Nonce) :=
    ((Equiv.curry (Fin groups) (Fin 11) Nonce).symm.trans sub).trans
      (Equiv.prodCongr reindex (Equiv.refl _))
  have prod := NonceChain.mean_prod (fun r (_ : rest → Nonce) => f r)
  simp only [NonceChain.mean,avg_const Finset.univ_nonempty] at prod
  exact prod.symm.trans (NonceChain.mean_equiv e (fun z => f z.1)).symm

noncomputable def salts (π : Equiv.Perm Word1600) (k : Key) :=
  nonceAt fun j => (splitReply (π (input j k))).1

theorem budget (t : Nat) :
    let q := t+2*LENGTH+t
    ((t : ℝ)+1)/2^121 + 2*((groups:ℝ)*((2*q+groups:ℝ)/2^192)) ≤ ((t:ℝ)+1)/2^120 := by
  norm_num [groups,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

end CommitGolfCandidate.Permutation.CounterSalt
