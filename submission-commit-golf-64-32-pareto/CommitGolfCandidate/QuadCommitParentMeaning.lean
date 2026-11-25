import CommitGolfCandidate.QuadCommitQuad2Meaning
import CommitGolfCandidate.TwoPermutationPackedParentMask
import CommitGolfCandidate.TwoPermutationPackedParentMeaning

namespace TwoPermutationPrototype.Quad.Commit.Parents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_public_bind check_evaluation_bind check_evaluation_pure
  read_buffer_memory_congr write_bits_digest write_bits_read_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] image writeBits checkEvaluation packedParentsTrace packedParentGroups

structure Content (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads heap : Nat → BitVec 256) (remaining : Nat) : Prop extends Retained2 s digests salts quads where
  nodes : ∀ n, remaining<n → n<2^21 → nodeDigest s n=heap n

theorem content_setPC (s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads heap : Nat → BitVec 256) (remaining : Nat) (pc : Word) (r : Content s digests salts quads heap remaining) :
    Content (s.setPC pc) digests salts quads heap remaining :=
  ⟨retained2_same_mem s (s.setPC pc) digests salts quads r.toRetained2 rfl,r.nodes⟩

theorem content_step (oracle : Oracle) (s : MachineState) (quads heap : Nat → BitVec 256)
    (digests : DigestTape) (salts : CompleteSaltTape) (n : Nat) (inside : n+1<2^20)
    (tree : ∀ j, 0<j → j<2^20 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))))
    (prior : Content s digests salts quads heap (n+1)) (regs : ParentRegs s (n+1)) :
    Content (packedParentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) digests salts quads heap n := by
  let cur := n+1
  let raw : BitVec 256 := oracle.compression (parentInput s cur)
  let reply := projectReply raw
  have memory : (packedParentAfter s cur raw).mem=(parentWritten s cur reply).mem :=
    packed_parent_memory s cur raw regs (by exact Nat.lt_trans inside (by decide))
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by dsimp [treeWord,cur];omega
  refine ⟨retained2_above s _ digests salts quads prior.toRetained2 ?_,?_⟩
  · intro word lo hi
    rw [←read_word,read_buffer_memory_congr _ _ memory]
    change readBuffer (writeBits s (wordAddress (treeWord cur)) reply) (8*word) 8=memoryView s word
    rw [←read_word s word]
    apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*word) 8 writeRange
      (by omega)
    right;dsimp [treeWord,cur];unfold groupWord at lo;omega
  · intro j larger small
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply) memory]
    by_cases last : j=cur
    · subst j
      have written := write_bits_digest (bits := 256) s (8*treeWord cur) 0 reply (by decide) (by decide)
      simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at written
      apply written.trans
      unfold reply raw
      rw [child_pair,prior.nodes (2*cur+1) (by dsimp [cur];omega) (by dsimp [cur];omega),
        prior.nodes (2*cur) (by dsimp [cur];omega) (by dsimp [cur];omega),tree cur (by dsimp [cur];omega) inside]
    · have diff : cur<j := by dsimp [cur] at *;omega
      apply Eq.trans _ (prior.nodes j diff small)
      apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*treeWord j) 32 writeRange
      · unfold treeWord;omega
      · right;unfold treeWord;omega

theorem sequence_content (oracle : Oracle) (state : MachineState) (quads heap : Nat → BitVec 256)
    (digests : DigestTape) (salts : CompleteSaltTape) (remaining count : Nat) (inside : remaining+count<2^20)
    (tree : ∀ j, 0<j → j<2^20 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))))
    (prior : Content state digests salts quads heap (remaining+count)) (regs : ParentRegs state (remaining+count)) :
    let result := (checkEvaluation oracle (packedParentsTrace remaining count state)).1
    Content result digests salts quads heap remaining ∧ ParentRegs result remaining := by
  induction count generalizing state with
  | zero => simpa only [packedParentsTrace,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [packedParentsTrace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInput state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · exact content_step oracle state quads heap digests salts (remaining+count) (by omega) tree prior regs
    · exact packed_next_parent_regs state (remaining+count) _ regs

theorem groups_content (oracle : Oracle) (base : Word) (span count : Nat) (state : MachineState)
    (quads heap : Nat → BitVec 256) (digests : DigestTape) (salts : CompleteSaltTape) (inside : span*count<2^20)
    (tree : ∀ j, 0<j → j<2^20 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))))
    (prior : Content state digests salts quads heap (span*count)) (regs : ParentRegs state (span*count)) :
    Content (checkEvaluation oracle (packedParentGroups base span count state)).1 digests salts quads heap 0 := by
  induction count generalizing state with
  | zero => simpa only [packedParentGroups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ count ih =>
    rw [Nat.mul_succ] at inside prior regs
    have body := sequence_content oracle state quads heap digests salts (span*count) span inside tree prior regs
    rw [packedParentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact content_setPC _ digests salts quads heap (span*count) _ body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap⟩

end TwoPermutationPrototype.Quad.Commit.Parents
