import CommitGolfCandidate.QuadCommitInput
import CommitGolfCandidate.QuadCommitWindows

/-! The high trapdoor area survives both tree passes: leaf digests, salts and zero prefixes. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_support splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] image writeBits checkEvaluation Leaves.groups Leaves.group Leaves.batch

structure Retained (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape) : Prop where
  leaf : ∀ (i : Index) (k : Fin 4), memoryView s (leafWord i.val+k.val)=(digests i).extractLsb' (64*k.val) 64
  nonce : ∀ (i : Index) (k : Fin 2), memoryView s (saltWord i.val+k.val)=(salts i).extractLsb' (64*k.val) 64
  zeros : ∀ g < 2^22, ∀ k : Fin 9, memoryView s (groupWord g+k.val)=0

theorem retained_above (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts)
    (frame : ∀ word, groupWord 0≤word → word<2^33 → memoryView t word=memoryView s word) :
    Retained t digests salts := by
  constructor
  · intro i k
    rw [frame _ (by unfold leafWord groupWord;omega) (by have hi : i.val<2^24 := i.isLt;have := k.isLt;unfold leafWord groupWord;omega)]
    exact r.leaf i k
  · intro i k
    rw [frame _ (by unfold saltWord groupWord;omega) (by have hi : i.val<2^24 := i.isLt;have := k.isLt;unfold saltWord;omega)]
    exact r.nonce i k
  · intro g hg k
    rw [frame _ (by unfold groupWord;omega) (by have := k.isLt;unfold groupWord;omega)]
    exact r.zeros g hg k

theorem retained_same_mem (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts) (h : t.mem=s.mem) : Retained t digests salts :=
  retained_above s t digests salts r (fun _ _ _ => congrFun h _)

theorem retained_from_prefix (oracle : Oracle) (before : Memory) (s : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (inv : Leaves.PinnedLeafPrefix oracle before s (2^24))
    (leaf : ∀ i : Index, outputDigest (Leaves.pinnedFinalReply oracle before i.val)=digests i)
    (nonce : ∀ i : Index, (window before (saltWord i.val) : Words 2)=saltWords (salts i))
    (zeros : ∀ g < 2^22, ∀ k : Fin 9, before (groupWord g+k.val)=0) :
    Retained s digests salts := by
  constructor
  · intro i k
    have raw := congrFun (inv.digests i.val i.isLt) k
    change memoryView s (leafWord i.val+k.val)=_ at raw
    rw [raw,low_digest_word,leaf i]
  · intro i k
    have raw := congrFun ((inv.salts i.val i.isLt).trans (nonce i)) k
    exact raw
  · intro g hg k
    have raw := congrFun (inv.zeros g hg) k
    exact raw.trans (zeros g hg k)

def leafState (oracle : Oracle) (initial : MachineState) {bits : Nat} (packed : BitVec bits) :=
  (checkEvaluation oracle (Leaves.groups 4096 0 (readyState initial packed))).1

theorem retained_quad_input (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts) (g : Nat) (hg : g<2^22) :
    readBuffer s (8*groupWord g) 200=quadInput (quadGroupLeaves digests g) := by
  apply quad_buffer_eq s g _ (r.zeros g hg)
  intro slot k
  have bound : 4*g+slot.val<LENGTH := by change _<16777216;have := slot.isLt;omega
  rw [quadGroupLeaves,dif_pos bound]
  exact r.leaf ⟨4*g+slot.val,bound⟩ k

theorem retained_leaf_buffer (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts) (i : Index) : readBuffer s (8*leafWord i.val) 32=digests i := by
  apply aligned_buffer_eq s _ 32 (by decide)
  intro k hk;exact r.leaf i ⟨k,hk⟩

theorem retained_salt_buffer (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts) (i : Index) : readBuffer s (8*saltWord i.val) 16=salts i := by
  apply aligned_buffer_eq s _ 16 (by decide)
  intro k hk;exact r.nonce i ⟨k,hk⟩

end TwoPermutationPrototype.Quad.Commit
