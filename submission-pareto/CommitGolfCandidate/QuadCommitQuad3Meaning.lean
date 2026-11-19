import CommitGolfCandidate.QuadCommitQuad2Meaning
import CommitGolfCandidate.QuadCommitQuad3Control

/-! Memory meaning of the level-3 pass: heap node `2^18 + m` holds the quad of level-2 group `m`,
and the retained area (including all level-1 and level-2 nodes) survives, since every write ends
below the level-2 groups. -/
namespace TwoPermutationPrototype.Quad.Commit.Quad3s
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_public_bind check_evaluation_bind check_evaluation_pure
  read_buffer_memory_congr write_bits_digest write_bits_read_outside)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
attribute [local irreducible] image writeBits checkEvaluation trace groups after nextPC

structure Content (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s heap : Nat → BitVec 256) (count : Nat) : Prop extends Retained3 s digests salts quads quad2s where
  nodes : ∀ h < count, readBuffer s (8*heapWord (2^18+h)) 32=heap (2^18+h)

theorem content_setPC (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s heap : Nat → BitVec 256) (count : Nat) (pc : Word) (r : Content s digests salts quads quad2s heap count) :
    Content (s.setPC pc) digests salts quads quad2s heap count :=
  ⟨retained3_same_mem s (s.setPC pc) digests salts quads quad2s r.toRetained3 rfl,r.nodes⟩

theorem after_far (s : MachineState) (g : Nat) (bound : g<2^18) (reply : BitVec 1600)
    (word : Nat) (lo : quad3GroupWord 0≤word) (hi : word<2^33) :
    memoryView (after s g reply) word=memoryView s word := by
  have endWrite : heapWord (2^18+g)+25≤quad3GroupWord 0 := by unfold heapWord quad3GroupWord;omega
  unfold after
  change memoryView (writeBits s (wordAddress (heapWord (2^18+g))) reply) word=_
  rw [permutation_write_memory s _ word reply (by unfold heapWord;omega) hi]
  unfold writeWindow
  rw [dif_neg (by change ¬(_≤word ∧ word<_+25);omega)]

theorem content_step (oracle : Oracle) (s : MachineState) (g : Nat) (bound : g<2^18)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s heap : Nat → BitVec 256)
    (quad : ∀ h < 2^18, heap (2^18+h)=quadFunction oracle.permutation (fun k => quad2s (4*h+k.val)))
    (r : Content s digests salts quads quad2s heap g) :
    Content (after s g (oracle.permutation (packBuffer (window (memoryView s) (quad3GroupWord g)))) )
      digests salts quads quad2s heap (g+1) := by
  let reply := oracle.permutation (packBuffer (window (memoryView s) (quad3GroupWord g)))
  refine ⟨retained3_above s _ digests salts quads quad2s r.toRetained3 (after_far s g bound reply),?_⟩
  intro h hh
  have mem : (after s g reply).mem=(writeBits s (wordAddress (heapWord (2^18+g))) reply).mem := by unfold after;rfl
  rw [read_buffer_memory_congr _ _ mem]
  by_cases same : h=g
  · subst h
    have written := write_bits_digest (bits := 1600) s (8*heapWord (2^18+g)) 0 reply (by decide)
      (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at written
    apply written.trans
    rw [quad g bound]
    unfold reply quadFunction
    rw [←read_permutation_window,retained3_quad3_input s digests salts quads quad2s r.toRetained3 g bound]
    rfl
  · have earlier : h<g := by omega
    apply Eq.trans _ (r.nodes h earlier)
    apply write_bits_read_outside (bits := 1600) s reply (8*heapWord (2^18+g)) (8*heapWord (2^18+h)) 32
      (by unfold heapWord;omega) (by unfold heapWord;omega)
    left;unfold heapWord;omega

theorem sequence_content (oracle : Oracle) (s : MachineState) (count g : Nat) (limit : count+g≤2^18)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s heap : Nat → BitVec 256)
    (quad : ∀ h < 2^18, heap (2^18+h)=quadFunction oracle.permutation (fun k => quad2s (4*h+k.val)))
    (r : Content s digests salts quads quad2s heap g) :
    Content (checkEvaluation oracle (trace count g s)).1 digests salts quads quad2s heap (count+g) := by
  induction count generalizing s g with
  | zero => simpa only [trace,check_evaluation_pure,Nat.add_zero,Nat.zero_add] using r
  | succ k ih =>
    rw [trace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (quad3GroupWord g))))))) :
        OracleComp World (BitVec 1600)) =
      (oracle.permutation (packBuffer (window (memoryView s) (quad3GroupWord g))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    have step := content_step oracle s g (by omega) digests salts quads quad2s heap quad r
    have tail := ih _ (g+1) (by omega) step
    convert tail using 1 <;> omega

theorem groups_content (oracle : Oracle) (s : MachineState) (count g : Nat) (limit : g+16384*count≤2^18)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s heap : Nat → BitVec 256)
    (quad : ∀ h < 2^18, heap (2^18+h)=quadFunction oracle.permutation (fun k => quad2s (4*h+k.val)))
    (r : Content s digests salts quads quad2s heap g) :
    Content (checkEvaluation oracle (groups count g s)).1 digests salts quads quad2s heap (g+16384*count) := by
  induction count generalizing s g with
  | zero => simpa only [groups,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using r
  | succ k ih =>
    rw [groups,check_evaluation_bind]
    have body := sequence_content oracle s 16384 g (by omega) digests salts quads quad2s heap quad r
    let mid := (checkEvaluation oracle (trace 16384 g s)).1
    have next := content_setPC mid digests salts quads quad2s heap (16384+g) (nextPC (g+16384)) body
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

end TwoPermutationPrototype.Quad.Commit.Quad3s
