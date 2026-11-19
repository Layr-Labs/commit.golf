import CommitGolfCandidate.QuadCommitQuadMeaning
import CommitGolfCandidate.QuadCommitQuad2Control

/-! Memory meaning of the level-2 pass: the slot of level-2 node `h` holds the quad of level-1
group `h`; level-2 replies end below the leaf groups and never touch level-2 zero prefixes. -/

namespace TwoPermutationPrototype.Quad.Commit.Quad2s
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_public_bind check_evaluation_bind check_evaluation_pure
  read_buffer_memory_congr write_bits_digest write_bits_read_outside)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
attribute [local irreducible] image writeBits checkEvaluation trace groups after nextPC

structure Content (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) (count : Nat) : Prop extends Retained2 s digests salts quads where
  nodes : ∀ g < count, ∀ k : Fin 4, memoryView s (quad3SlotWord g+k.val)=(quad2s g).extractLsb' (64*k.val) 64

theorem content_setPC (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s : Nat → BitVec 256) (count : Nat) (pc : Word) (r : Content s digests salts quads quad2s count) :
    Content (s.setPC pc) digests salts quads quad2s count :=
  ⟨retained2_same_mem s (s.setPC pc) digests salts quads r.toRetained2 rfl,r.nodes⟩

theorem after_outside (s : MachineState) (g : Nat) (bound : g<2^20) (reply : BitVec 1600)
    (word : Nat) (away : word<quad3SlotWord g ∨ quad3SlotWord g+25≤word) (hi : word<2^33) :
    memoryView (after s g reply) word=memoryView s word := by
  unfold after
  change memoryView (writeBits s (wordAddress (quad3SlotWord g)) reply) word=_
  rw [permutation_write_memory s _ word reply (by unfold quad3SlotWord quad3GroupWord;omega) hi]
  unfold writeWindow
  rw [dif_neg (by change ¬(_≤word ∧ word<_+25);omega)]

theorem content_step (oracle : Oracle) (s : MachineState) (g : Nat) (bound : g<2^20)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s : Nat → BitVec 256)
    (quad : ∀ h < 2^20, quad2s h=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (r : Content s digests salts quads quad2s g) :
    Content (after s g (oracle.permutation (packBuffer (window (memoryView s) (quad2GroupWord g)))) )
      digests salts quads quad2s (g+1) := by
  let reply := oracle.permutation (packBuffer (window (memoryView s) (quad2GroupWord g)))
  have below := quad3_slot_write_below g (by rw [length_value];omega)
  refine ⟨retained2_mid s _ digests salts quads r.toRetained2 ?_ ?_,?_⟩
  · intro word lo hi
    exact after_outside s g bound reply word (by omega) hi
  · intro m hm k
    have separate := quad3_slot_zero_prefix_separate g m
    exact after_outside s g bound reply _ (by have := k.isLt;omega) (by have := k.isLt;unfold quad3GroupWord;omega)
  · intro h hh k
    by_cases same : h=g
    · subst h
      have mem : (after s g reply).mem=(writeBits s (wordAddress (quad3SlotWord g)) reply).mem := by unfold after;rfl
      have written := write_bits_digest (bits := 1600) s (8*quad3SlotWord g) 0 reply (by decide)
        (by decide)
      simp only [Nat.mul_zero,Nat.add_zero] at written
      have buffer : readBuffer (after s g reply) (8*quad3SlotWord g) 32=quad2s g := by
        rw [read_buffer_memory_congr _ _ mem]
        apply written.trans
        rw [quad g bound]
        unfold reply quadFunction
        rw [←read_permutation_window,retained2_quad2_input s digests salts quads r.toRetained2 g bound]
        rfl
      exact buffer_digest_words _ _ _ buffer k
    · have earlier : h<g := by omega
      have separate := quad3_slot_separate h g earlier
      rw [after_outside s g bound reply _ (by have := k.isLt;omega) (by have := k.isLt;unfold quad3SlotWord quad3GroupWord;omega)]
      exact r.nodes h earlier k

theorem sequence_content (oracle : Oracle) (s : MachineState) (count g : Nat) (limit : count+g≤2^20)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s : Nat → BitVec 256)
    (quad : ∀ h < 2^20, quad2s h=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (r : Content s digests salts quads quad2s g) :
    Content (checkEvaluation oracle (trace count g s)).1 digests salts quads quad2s (count+g) := by
  induction count generalizing s g with
  | zero => simpa only [trace,check_evaluation_pure,Nat.add_zero,Nat.zero_add] using r
  | succ k ih =>
    rw [trace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (quad2GroupWord g))))))) :
        OracleComp World (BitVec 1600)) =
      (oracle.permutation (packBuffer (window (memoryView s) (quad2GroupWord g))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    have step := content_step oracle s g (by omega) digests salts quads quad2s quad r
    have tail := ih _ (g+1) (by omega) step
    convert tail using 1 <;> omega

theorem groups_content (oracle : Oracle) (s : MachineState) (count g : Nat) (limit : g+16384*count≤2^20)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s : Nat → BitVec 256)
    (quad : ∀ h < 2^20, quad2s h=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (r : Content s digests salts quads quad2s g) :
    Content (checkEvaluation oracle (groups count g s)).1 digests salts quads quad2s (g+16384*count) := by
  induction count generalizing s g with
  | zero => simpa only [groups,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using r
  | succ k ih =>
    rw [groups,check_evaluation_bind]
    have body := sequence_content oracle s 16384 g (by omega) digests salts quads quad2s quad r
    let mid := (checkEvaluation oracle (trace 16384 g s)).1
    have next := content_setPC mid digests salts quads quad2s (16384+g) (nextPC (g+16384)) body
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

end TwoPermutationPrototype.Quad.Commit.Quad2s
