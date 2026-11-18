import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationLeaf

/-!
# Quartet blocks, group replies and the state the body hands to the upper stage

Quartet `q` owns the 1024-byte block `B_q` (word `cellFirst + 128 q`): bytes `72..200` hold the four
leaf digests `d0..d3` (`leafWord`). An even quartet `q = 2u` keeps its group reply `reply_E` at
`[B_q + 168, B_q + 368)` (it overwrites `d3`), the odd quartet `q + 1` keeps `reply_O` at
`[B_q + 368, B_q + 568)` (spare bytes of the even block). The two group nodes
`reply_E[168..200)` and `reply_O[0..32)` therefore sit next to each other at
`s_u = B_{2u} + 336` (`unitBase u`): `[s_u, s_u + 64)` is the input of the level-21 parent `u`.

`TailReady` is what the body leaves in memory for the upper stage: every group reply and every
surviving leaf digest in place, and the 24-byte key in the key block.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- Byte address of the trapdoor (`x9` during the commit; the heap node `n` is at `trapdoorBase + 32 n`). -/
def trapdoorBase : Nat := 4294971424
/-- Word index of block `B_0` (trapdoor + 32 L). -/
def cellFirst : Nat := 603980292
/-- Word index of the first leaf digest word of leaf `i` (`B_{i/4} + 72 + 32 (i%4)`). -/
def leafWord (i : Nat) : Nat := cellFirst + 128*(i/4) + 9 + 4*(i%4)
/-- Distance between consecutive unit bases, in 64-bit words (two blocks). -/
def unitStride : Nat := 256
/-- Word index of `s_0 = B_0 + 336`. -/
def unitFirst : Nat := cellFirst + 42
/-- Word index of the base `s_u` of unit `u` (the quartets `2u`, `2u+1`). -/
def unitBase (u : Nat) : Nat := unitFirst + unitStride*u
/-- First word of the 200-byte reply of quartet group `g`: `s - 168` (even), `s + 32` (odd). -/
def groupReplyWord (g : Nat) : Nat := if g%2=0 then unitBase (g/2) - 21 else unitBase (g/2) + 4
/-- Word index of the first key word (the key block's words 1..3; word 0 is the generator counter). -/
def keyWord : Nat := 1140851205

/-- Leaf digests the group call of an even quartet overwrites (`d3`, slot `3` of an even quartet). -/
def overwritten (i : Nat) : Prop := (i/4)%2=0 ∧ i%4=3

structure TailReady (o : Oracle) (d : DigestTape) (key : BitVec 192) (m : Memory) : Prop where
  replies : ∀ g < 4194304, (window m (groupReplyWord g) : Words 25) =
    replyWords (o.permutation (quartetEncode (Quartet.quartetPayload d g)))
  leaves : ∀ i < 16777216, ¬ overwritten i → ∀ k < 4,
    m (leafWord i+k) = (Quartet.leafAt d i).extractLsb' (64*k) 64
  key : ∀ j : Fin 3, m (keyWord + j.val) = key.extractLsb' (64*j.val) 64

/-- Byte offset of group `g`'s reply inside the trapdoor. -/
def groupReplyOffset (g : Nat) : Nat := 8*groupReplyWord g - trapdoorBase

/-- The reply of quartet group `g` as stored in a trapdoor. -/
def trapdoorGroupReply {n : Nat} (td : BitVec n) (g : Nat) : BitVec 1600 :=
  td.extractLsb' (8*groupReplyOffset g) 1600

end TwoPermutationPrototype.Grouped
