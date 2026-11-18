import CommitGolfCandidate.QuadCommitRetained
import CommitGolfCandidate.QuadCommitQuadControl

namespace TwoPermutationPrototype.Quad.Commit.Quads
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_public_bind check_evaluation_bind check_evaluation_pure
  read_buffer_memory_congr write_bits_digest write_bits_read_outside)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
attribute [local irreducible] image writeBits checkEvaluation trace groups after nextPC

structure Content (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (count : Nat) : Prop extends Retained s digests salts where
  nodes : ∀ g < count, ∀ k : Fin 4, memoryView s (quadSlotWord g+k.val)=(quads g).extractLsb' (64*k.val) 64

theorem content_setPC (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads : Nat → BitVec 256) (count : Nat) (pc : Word) (r : Content s digests salts quads count) :
    Content (s.setPC pc) digests salts quads count :=
  ⟨retained_same_mem s (s.setPC pc) digests salts r.toRetained rfl,r.nodes⟩

theorem after_outside (s : MachineState) (g : Nat) (bound : g<2^22) (reply : BitVec 1600)
    (word : Nat) (away : word<quadSlotWord g ∨ quadSlotWord g+25≤word) (hi : word<2^33) :
    memoryView (after s g reply) word=memoryView s word := by
  unfold after
  change memoryView (writeBits s (wordAddress (quadSlotWord g)) reply) word=_
  rw [permutation_write_memory s _ word reply (by unfold quadSlotWord quad2GroupWord;omega) hi]
  unfold writeWindow
  rw [dif_neg (by change ¬(_≤word ∧ word<_+25);omega)]

theorem content_step (oracle : Oracle) (s : MachineState) (g : Nat) (bound : g<2^22)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads : Nat → BitVec 256)
    (quad : ∀ h < 2^22, quads h=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (r : Content s digests salts quads g) :
    Content (after s g (oracle.permutation (packBuffer (window (memoryView s) (groupWord g)))) )
      digests salts quads (g+1) := by
  let reply := oracle.permutation (packBuffer (window (memoryView s) (groupWord g)))
  have below := quad_slot_after_zero_prefix g
  refine ⟨retained_below s _ digests salts r.toRetained ?_ ?_,?_⟩
  · intro word lo hi
    exact after_outside s g bound reply word (by unfold quad2GroupWord at *;omega) (by unfold quad2GroupWord at hi;omega)
  · intro h hh k
    have separate := quad_slot_zero_prefix_separate g h
    exact after_outside s g bound reply _ (by have := k.isLt;omega) (by have := k.isLt;unfold quad2GroupWord;omega)
  · intro h hh k
    by_cases same : h=g
    · subst h
      have mem : (after s g reply).mem=(writeBits s (wordAddress (quadSlotWord g)) reply).mem := by unfold after;rfl
      have written := write_bits_digest (bits := 1600) s (8*quadSlotWord g) 0 reply (by decide)
        (by decide)
      simp only [Nat.mul_zero,Nat.add_zero] at written
      have buffer : readBuffer (after s g reply) (8*quadSlotWord g) 32=quads g := by
        rw [read_buffer_memory_congr _ _ mem]
        apply written.trans
        rw [quad g bound]
        unfold reply quadFunction
        rw [←read_permutation_window,retained_quad_input s digests salts r.toRetained g bound]
        rfl
      exact buffer_digest_words _ _ _ buffer k
    · have earlier : h<g := by omega
      have separate := quad_slot_separate h g earlier
      rw [after_outside s g bound reply _ (by have := k.isLt;omega) (by have := k.isLt;unfold quadSlotWord quad2GroupWord;omega)]
      exact r.nodes h earlier k

theorem sequence_content (oracle : Oracle) (s : MachineState) (count g : Nat) (limit : count+g≤2^22)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads : Nat → BitVec 256)
    (quad : ∀ h < 2^22, quads h=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (r : Content s digests salts quads g) :
    Content (checkEvaluation oracle (trace count g s)).1 digests salts quads (count+g) := by
  induction count generalizing s g with
  | zero => simpa only [trace,check_evaluation_pure,Nat.add_zero,Nat.zero_add] using r
  | succ k ih =>
    rw [trace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (groupWord g))))))) :
        OracleComp World (BitVec 1600)) =
      (oracle.permutation (packBuffer (window (memoryView s) (groupWord g))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    have step := content_step oracle s g (by omega) digests salts quads quad r
    have tail := ih _ (g+1) (by omega) step
    convert tail using 1 <;> omega

theorem groups_content (oracle : Oracle) (s : MachineState) (count g : Nat) (limit : g+16384*count≤2^22)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads : Nat → BitVec 256)
    (quad : ∀ h < 2^22, quads h=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (r : Content s digests salts quads g) :
    Content (checkEvaluation oracle (groups count g s)).1 digests salts quads (g+16384*count) := by
  induction count generalizing s g with
  | zero => simpa only [groups,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using r
  | succ k ih =>
    rw [groups,check_evaluation_bind]
    have body := sequence_content oracle s 16384 g (by omega) digests salts quads quad r
    let mid := (checkEvaluation oracle (trace 16384 g s)).1
    have next := content_setPC mid digests salts quads (16384+g) (nextPC (g+16384)) body
    rw [show g+16384*(k+1)=(g+16384)+16384*k by omega]
    apply ih (mid.setPC (nextPC (g+16384))) (g+16384) (by omega)
    rwa [Nat.add_comm 16384 g] at next

theorem counted_trace (oracle : Oracle) (s : MachineState) (count g : Nat) :
    RunPublic oracle (trace count g s) count := by
  induction count generalizing s g with
  | zero =>
    simp only [trace]
    exact run_pure_public ..
  | succ k ih =>
    rw [trace,show k+1=1+k by omega]
    exact run_bind_public _ _ _ 1 k (run_query_public ..) (fun _ => ih _ _)

theorem counted_groups (oracle : Oracle) (s : MachineState) (count g : Nat) :
    RunPublic oracle (groups count g s) (16384*count) := by
  induction count generalizing s g with
  | zero =>
    simp only [groups,Nat.mul_zero]
    exact run_pure_public ..
  | succ k ih =>
    rw [groups,show 16384*(k+1)=16384+16384*k by omega]
    exact run_bind_public _ _ _ 16384 _ (counted_trace ..) (fun _ => ih _ _)

end TwoPermutationPrototype.Quad.Commit.Quads
