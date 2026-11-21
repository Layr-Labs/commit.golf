import CommitGolfCandidate.QuadCommitInput
import CommitGolfCandidate.QuadCommitWindows

/-! The high trapdoor area survives the tree passes: leaf digests, salts, zero prefixes and
(after the level-1 pass) the level-1 nodes in their quad-group slots. -/
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
  quadZeros : ∀ h < 2^20, ∀ k : Fin 9, memoryView s (quad2GroupWord h+k.val)=0
  quad3Zeros : ∀ m < 2^18, ∀ k : Fin 9, memoryView s (quad3GroupWord m+k.val)=0

/-- The level-2 pass writes only level-2 slots below the leaf groups. -/
theorem retained_mid (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts)
    (frame : ∀ word, groupWord 0≤word → word<2^33 → memoryView t word=memoryView s word)
    (prefixes : ∀ m < 2^18, ∀ k : Fin 9, memoryView t (quad3GroupWord m+k.val)=memoryView s (quad3GroupWord m+k.val)) :
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
  · intro h hh k
    rw [frame _ (by unfold quad2GroupWord groupWord;omega) (by have := k.isLt;unfold quad2GroupWord;omega)]
    exact r.quadZeros h hh k
  · intro m hm k
    rw [prefixes m hm k]
    exact r.quad3Zeros m hm k

theorem retained_above (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts)
    (frame : ∀ word, quad3GroupWord 0≤word → word<2^33 → memoryView t word=memoryView s word) :
    Retained t digests salts :=
  retained_mid s t digests salts r (fun word lo hi => frame word (by unfold groupWord at lo;unfold quad3GroupWord;omega) hi)
    (fun m hm k => frame _ (by unfold quad3GroupWord;omega) (by have := k.isLt;unfold quad3GroupWord;omega))

/-- The level-1 pass writes only quad-group slots: everything below quad group 0 and the
quad-group zero prefixes survive. -/
theorem retained_below (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts)
    (frame : ∀ word, quad3GroupWord 0≤word → word<quad2GroupWord 0 → memoryView t word=memoryView s word)
    (prefixes : ∀ h < 2^20, ∀ k : Fin 9, memoryView t (quad2GroupWord h+k.val)=memoryView s (quad2GroupWord h+k.val)) :
    Retained t digests salts := by
  constructor
  · intro i k
    rw [frame _ (by unfold leafWord groupWord quad3GroupWord;omega) (by have hi : i.val<2^24 := i.isLt;have := k.isLt;unfold leafWord groupWord quad2GroupWord;omega)]
    exact r.leaf i k
  · intro i k
    rw [frame _ (by unfold saltWord quad3GroupWord;omega) (by have hi : i.val<2^24 := i.isLt;have := k.isLt;unfold saltWord quad2GroupWord;omega)]
    exact r.nonce i k
  · intro g hg k
    rw [frame _ (by unfold groupWord quad3GroupWord;omega) (by have := k.isLt;unfold groupWord quad2GroupWord;omega)]
    exact r.zeros g hg k
  · intro h hh k
    rw [prefixes h hh k]
    exact r.quadZeros h hh k
  · intro m hm k
    rw [frame _ (by unfold quad3GroupWord;omega) (by have := k.isLt;unfold quad3GroupWord quad2GroupWord;omega)]
    exact r.quad3Zeros m hm k

/-- After the level-1 pass: the retained area plus the four words of every level-1 node. -/
structure Retained2 (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) : Prop extends Retained s digests salts where
  quad : ∀ g < 2^22, ∀ k : Fin 4, memoryView s (quadSlotWord g+k.val)=(quads g).extractLsb' (64*k.val) 64

theorem retained2_mid (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (r : Retained2 s digests salts quads)
    (frame : ∀ word, groupWord 0≤word → word<2^33 → memoryView t word=memoryView s word)
    (prefixes : ∀ m < 2^18, ∀ k : Fin 9, memoryView t (quad3GroupWord m+k.val)=memoryView s (quad3GroupWord m+k.val)) :
    Retained2 t digests salts quads := by
  refine ⟨retained_mid s t digests salts r.toRetained frame prefixes,?_⟩
  intro g hg k
  rw [frame _ (by unfold quadSlotWord quad2GroupWord groupWord;omega)
    (by have := k.isLt;unfold quadSlotWord quad2GroupWord;omega)]
  exact r.quad g hg k

theorem retained2_above (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (r : Retained2 s digests salts quads)
    (frame : ∀ word, quad3GroupWord 0≤word → word<2^33 → memoryView t word=memoryView s word) :
    Retained2 t digests salts quads :=
  retained2_mid s t digests salts quads r (fun word lo hi => frame word (by unfold groupWord at lo;unfold quad3GroupWord;omega) hi)
    (fun m hm k => frame _ (by unfold quad3GroupWord;omega) (by have := k.isLt;unfold quad3GroupWord;omega))

theorem retained2_same_mem (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (r : Retained2 s digests salts quads) (h : t.mem=s.mem) :
    Retained2 t digests salts quads :=
  retained2_above s t digests salts quads r (fun _ _ _ => congrFun h _)

theorem retained2_quad_buffer (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (r : Retained2 s digests salts quads) (g : Nat) (hg : g<2^22) :
    readBuffer s (8*quadSlotWord g) 32=quads g := by
  apply aligned_buffer_eq s _ 32 (by decide)
  intro k hk;exact r.quad g hg ⟨k,hk⟩

theorem retained2_quad2_input (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (r : Retained2 s digests salts quads) (h : Nat) (hh : h<2^20) :
    readBuffer s (8*quad2GroupWord h) 200=quadInput (fun k => quads (4*h+k.val)) := by
  apply quad2_buffer_eq s h _ (r.quadZeros h hh)
  intro slot k
  exact r.quad (4*h+slot.val) (by have := slot.isLt;omega) k

/-- After the level-2 pass: also the four words of every level-2 node. -/
structure Retained3 (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) : Prop extends Retained2 s digests salts quads where
  quad2 : ∀ h < 2^20, ∀ k : Fin 4, memoryView s (quad3SlotWord h+k.val)=(quad2s h).extractLsb' (64*k.val) 64

theorem retained3_above (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) (r : Retained3 s digests salts quads quad2s)
    (frame : ∀ word, quad3GroupWord 0≤word → word<2^33 → memoryView t word=memoryView s word) :
    Retained3 t digests salts quads quad2s := by
  refine ⟨retained2_above s t digests salts quads r.toRetained2 frame,?_⟩
  intro h hh k
  rw [frame _ (by unfold quad3SlotWord quad3GroupWord;omega)
    (by have := k.isLt;unfold quad3SlotWord quad3GroupWord;omega)]
  exact r.quad2 h hh k

theorem retained3_same_mem (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) (r : Retained3 s digests salts quads quad2s) (h : t.mem=s.mem) :
    Retained3 t digests salts quads quad2s :=
  retained3_above s t digests salts quads quad2s r (fun _ _ _ => congrFun h _)

theorem retained3_quad2_buffer (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) (r : Retained3 s digests salts quads quad2s) (h : Nat) (hh : h<2^20) :
    readBuffer s (8*quad3SlotWord h) 32=quad2s h := by
  apply aligned_buffer_eq s _ 32 (by decide)
  intro k hk;exact r.quad2 h hh ⟨k,hk⟩

theorem retained3_quad3_input (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) (r : Retained3 s digests salts quads quad2s) (m : Nat) (hm : m<2^18) :
    readBuffer s (8*quad3GroupWord m) 200=quadInput (fun k => quad2s (4*m+k.val)) := by
  apply quad3_buffer_eq s m _ (r.quad3Zeros m hm)
  intro slot k
  exact r.quad2 (4*m+slot.val) (by have := slot.isLt;omega) k

theorem retained_same_mem (s t : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (r : Retained s digests salts) (h : t.mem=s.mem) : Retained t digests salts :=
  retained_above s t digests salts r (fun _ _ _ => congrFun h _)

theorem retained_from_prefix (oracle : Oracle) (before : Memory) (s : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (inv : Leaves.PinnedLeafPrefix oracle before s (2^24))
    (leaf : ∀ i : Index, outputDigest (Leaves.pinnedFinalReply oracle before i.val)=digests i)
    (nonce : ∀ i : Index, (window before (saltWord i.val) : Words 2)=saltWords (salts i))
    (zeros : ∀ g < 2^22, ∀ k : Fin 9, before (groupWord g+k.val)=0)
    (quadZeros : ∀ h < 2^20, ∀ k : Fin 9, before (quad2GroupWord h+k.val)=0)
    (quad3Zeros : ∀ m < 2^18, ∀ k : Fin 9, before (quad3GroupWord m+k.val)=0) :
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
  · intro h hh k
    have raw := congrFun (inv.quadZeros h hh) k
    exact raw.trans (quadZeros h hh k)
  · intro m hm k
    have raw := congrFun (inv.quad3Zeros m hm) k
    exact raw.trans (quad3Zeros m hm k)

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
