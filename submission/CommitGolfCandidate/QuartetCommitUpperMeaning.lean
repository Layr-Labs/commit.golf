import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64
open CommitGolfCandidate (read_buffer_memory_congr checkEvaluation check_evaluation_bind check_evaluation_pure write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
attribute [local irreducible] readBuffer writeBits checkEvaluation

structure UpperContent (s : MachineState) (heap : Nat → BitVec 256) (before : Memory) (remaining : Nat) : Prop where
  nodes : ∀ n, remaining<n → n<8388608 → nodeDigest s n=heap n
  high : ∀ w, qSource 0≤w → w<2^33 → memoryView s w=before w

private theorem upper_setpc (s : MachineState) (pc : Word) (heap : Nat → BitVec 256) (before : Memory)
    (n : Nat) (r : UpperContent s heap before n) : UpperContent (s.setPC pc) heap before n := by
  refine ⟨?_,r.high⟩
  intro j lo hi
  rw [nodeDigest,read_buffer_memory_congr _ s (show (s.setPC pc).mem=s.mem from rfl)]
  exact r.nodes j lo hi

theorem upper_content_step (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (n : Nat) (inside : n+1<4194304)
    (tree : ∀ j, 0<j → j<4194304 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))))
    (prior : UpperContent s heap before (n+1)) (regs : ParentRegs s (n+1)) :
    UpperContent (packedParentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) heap before n := by
  let cur := n+1
  let raw : BitVec 256 := oracle.compression (parentInput s cur)
  let reply := projectReply raw
  have memory : (packedParentAfter s cur raw).mem=(parentWritten s cur reply).mem :=
    packed_parent_memory s cur raw regs (by change cur<16777216;dsimp [cur];omega)
  have intBound : n+1<2^24 := by omega
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by dsimp [treeWord,cur];omega
  constructor
  · intro j larger small
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      memory]
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
  · intro w lo hi
    rw [←read_word,read_buffer_memory_congr _ (parentWritten s cur reply) memory]
    have sep := write_bits_read_outside (bits:=256) s reply (8*treeWord cur) (8*w) 8 writeRange
      (by omega) (by right; unfold treeWord qSource at *;dsimp [cur];split_ifs at * <;> omega)
    exact sep.trans ((read_word s w).trans (prior.high w lo hi))

theorem upper_sequence_semantics (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (remaining count : Nat) (inside : remaining+count<4194304)
    (tree : ∀ node, 0<node → node<4194304 →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : UpperContent state heap before (remaining+count))
    (regs : ParentRegs state (remaining+count)) :
    let result := (checkEvaluation oracle (packedParentsTrace remaining count state)).1
    UpperContent result heap before remaining ∧ ParentRegs result remaining := by
  induction count generalizing state with
  | zero =>
    simpa only [packedParentsTrace,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [packedParentsTrace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInput state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · exact upper_content_step oracle state heap before (remaining+count) (by omega) tree prior regs
    · exact packed_next_parent_regs state (remaining+count) _ regs

theorem upper_groups_semantics (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (before : Memory)
    (inside : span*groups < 4194304)
    (tree : ∀ node, 0 < node → node < 4194304 →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : UpperContent state heap before (span*groups)) (regs : ParentRegs state (span*groups)) :
    UpperContent (checkEvaluation oracle (packedParentGroups base span groups state)).1 heap before 0 := by
  induction groups generalizing state with
  | zero => simpa only [packedParentGroups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ] at inside prior regs
    have body  := upper_sequence_semantics oracle state heap before (span*groups) span inside tree prior regs
    rw [packedParentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact upper_setpc _ _ _ _ _ body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap⟩

end TwoPermutationPrototype.QuartetCommit
