import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationLeaf

/-!
# Quartet blocks, group replies and the state the body hands to the upper stage

Odd-quartet layout. Even quartet `2u` owns the block `B_{2u}` (word `cellFirst + 256 u`), odd quartet `2u+1` the
block `B_{2u} - 200` bytes (word `cellFirst + 256 u - 25`, see `Grouped.qSource`). Each quartet's group call writes
its 200-byte reply over its own block from `a2`: even reply `reply_E` at `[B + 168, B + 368)`, odd reply `reply_O`
at `[B - 32, B + 168)`. The group nodes are `reply_O[168..200)` (at `B + 136`) and `reply_E[0..32)` (at `B + 168`),
so `s_u = B_{2u} + 136` (`unitBase u`) starts the 64-byte input `node_odd ‖ node_even` of the level-21 parent `u`.

`TailReady` is what the body leaves in memory for the upper stage: every group reply in place and the 24-byte key
in the key block (the leaf digest slots are overwritten; the opener reads leaf digests from inverse-rebuilt blocks).
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
/-- Word index of `s_0 = B_0 + 136`. -/
def unitFirst : Nat := cellFirst + 17
/-- Word index of the base `s_u` of unit `u` (the quartets `2u`, `2u+1`). -/
def unitBase (u : Nat) : Nat := unitFirst + unitStride*u
/-- First word of the 200-byte reply of quartet group `g`: `s + 32` (even), `s - 168` (odd). -/
def groupReplyWord (g : Nat) : Nat := if g%2=0 then unitBase (g/2) + 4 else unitBase (g/2) - 21
/-- Word index of the first key word (the key block's words 1..3; word 0 is the generator counter). -/
def keyWord : Nat := 1140851205

structure TailReady (o : Oracle) (d : DigestTape) (key : BitVec 192) (m : Memory) : Prop where
  replies : ∀ g < 4194304, (window m (groupReplyWord g) : Words 25) =
    replyWords (o.permutation (quartetEncode (Quartet.quartetPayload d g)))
  key : ∀ j : Fin 3, m (keyWord + j.val) = key.extractLsb' (64*j.val) 64

/-- Byte offset of group `g`'s reply inside the trapdoor. -/
def groupReplyOffset (g : Nat) : Nat := 8*groupReplyWord g - trapdoorBase

/-- The reply of quartet group `g` as stored in a trapdoor. -/
def trapdoorGroupReply {n : Nat} (td : BitVec n) (g : Nat) : BitVec 1600 :=
  td.extractLsb' (8*groupReplyOffset g) 1600

end TwoPermutationPrototype.Grouped
