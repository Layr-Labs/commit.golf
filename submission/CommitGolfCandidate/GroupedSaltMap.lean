import CommitGolfCandidate.GroupedPacket
import CommitGolfCandidate.CounterSaltWindows

/-!
# Pair-heads salt map (shared by the commit proofs and the opener proofs)

Leaf `i`'s salt is the 16-byte slot `(coord i).2` of the generator reply for counter `msgWord (2·saltHead i + 1)`
(the odd entry of the salt's head pair). `localLoop` is the opener's salt-loop arithmetic (opening words 739-776):
pair `p = n/2`, `r = p mod 11`, head pair `hp = p − r` (r < 5) or `p − (r − 5)`, `k` = position in the group,
byte offset `184·par` in place (k = 0), else `32k + 16·par − 16`, except offset 160 → previous head, offset 144.
`local_loop_coord` proves it equals `CounterSalt.localCoord` (head, slot byte) on every slot of a body.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSalt)
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.CounterSalt (coord firstLeaf input localCoord hpl local_head_lt local_slot_lt)
set_option maxRecDepth 18000

/-- Byte offset of salt slot `s` in a generator reply (`Counter.slice`: slot 0 = words 23,24, slot s = words 2(s-1)). -/
def sliceByte (s : Nat) : Nat := if s=0 then 184 else 16*(s-1)

/-- Global head pair of the reply holding leaf `i`'s salt. -/
def saltHead (i : Nat) : Nat := 2048*(i/4096)+hpl (localCoord (i%4096)).1

/-- The opener's salt-loop arithmetic on a body slot `n < 4096`: (head pair inside the body, byte offset). -/
def localLoop (n : Nat) : Nat × Nat :=
  let p := n/2
  let par := n%2
  let r := p%11
  let k := if r<5 then r else r-5
  let hp := p-k
  if k=0 then (hp,184*par)
  else if 32*k+16*par-16=160 then (hp-5,144)
  else (hp,32*k+16*par-16)

/-- The opener's salt-loop result for a global leaf `i`. -/
def loopMap (i : Nat) : Nat × Nat := (2048*(i/4096)+(localLoop (i%4096)).1,(localLoop (i%4096)).2)

theorem local_loop_coord : ∀ n : Fin 4096,
    localLoop n.val=(hpl (localCoord n.val).1,sliceByte (localCoord n.val).2) := by
  decide +kernel

theorem loop_map_eq (i : Nat) (hi : i<16777216) : loopMap i=(saltHead i,sliceByte (coord ⟨i,hi⟩).2.val) := by
  have h := local_loop_coord ⟨i%4096,by omega⟩
  simp only at h
  unfold loopMap saltHead coord
  rw [h]

/-- The counter of leaf `i`'s reply is the odd leaf of its salt's head pair. -/
theorem first_leaf_coord (idx : Index) : firstLeaf (coord idx).1=2*saltHead idx.val+1 := by
  have b := local_head_lt (idx.val%4096) (by omega)
  have hi : idx.val<16777216 := idx.isLt
  unfold firstLeaf saltHead coord
  dsimp only
  rw [show (373*(idx.val/4096)+(localCoord (idx.val%4096)).1)/373=idx.val/4096 by omega,
    show (373*(idx.val/4096)+(localCoord (idx.val%4096)).1)%373=(localCoord (idx.val%4096)).1 by omega]
  omega

def keyBlock (key : BitVec 192) (j : Nat) : Word := key.extractLsb' (64*(j-1)) 64

def KeyIntact (m : Memory) (key : BitVec 192) := ∀ j, 0<j → j<25 → m (qSalt 0+j)=keyBlock key j

def groupReply (o : Oracle) (k : BitVec 192) (i : Index) := o.permutation (input (coord i).1 k)

theorem input_word (idx : Index) (key : BitVec 192) (j : Fin 25) :
    replyWords (input (coord idx).1 key) j =
      (if j.val=0 then wordAddress (msgWord (2*saltHead idx.val+1)) else keyBlock key j.val) := by
  unfold input replyWords
  have h := j.isLt
  by_cases zero : j.val=0
  · simp only [zero,ite_true,Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256),
      BitVec.extractLsb'_append_eq_right]
    unfold Permutation.CounterSalt.ctr
    rw [first_leaf_coord];unfold wordAddress msgWord;congr 1 <;> omega
  · rw [if_neg zero]
    by_cases low : j.val<4
    · rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64*j.val+64≤256),
          BitVec.extractLsb'_append_eq_of_le (by omega : 64≤64*j.val)]
      unfold keyBlock;congr 1 <;> omega
    · rw [BitVec.extractLsb'_append_eq_of_le (by omega : 256≤64*j.val)]
      unfold keyBlock
      apply BitVec.eq_of_getLsbD_eq;intro k hk
      simp [hk,show 192≤64*(j.val-1)+k by omega]

/-- Leaf `i`'s salt words are the slot `(coord i).2` of its group reply. -/
theorem salt_slice (o : Oracle) (k : BitVec 192) (i : Index) :
    saltWords (Permutation.CounterSalt.salts o.permutation k i)=Counter.slice (replyWords (groupReply o k i)) (coord i).2 :=
  (Counter.slice_eq (groupReply o k i) (coord i).2).symm

theorem reply_pack (v : BitVec 1600) : packBuffer (replyWords v)=v := by
  apply BitVec.eq_of_getLsbD_eq;intro k hk
  let j : Fin 25 := ⟨k/64,by omega⟩
  have h:=congrArg (fun w : BitVec 64 => w.getLsbD (k%64)) (packed_word (replyWords v) j)
  have b : k%64<64 := by omega
  unfold replyWords at h
  dsimp only [j] at h
  change ((packBuffer _).extractLsb' (64*(k/64)) 64).getLsbD (k%64) =
    (v.extractLsb' (64*(k/64)) 64).getLsbD (k%64) at h
  unfold replyWords
  simpa only [BitVec.getLsbD_extractLsb',b,decide_true,Bool.true_and,Nat.div_add_mod] using h

end TwoPermutationPrototype.Grouped
