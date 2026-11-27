import CommitGolfCandidate.TwoPermutationHybridPhase
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation parentsTrace packedParentsTrace packedParentGroups hybridLowerFor hybridUpper hybridParentPhase readBuffer R1bParents.trace

private theorem full_node_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (n : Nat) (inside : n+1<LENGTH)
    (tree : heap (n+1)=oracle.compression (heap (2*(n+1)+1) ++ heap (2*(n+1))))
    (prior : ParentContent s heap salts (n+1)) :
    ParentContent (parentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) heap salts n := by
  let cur := n+1
  let reply : BitVec 256 := oracle.compression (parentInput s cur)
  have intBound : n+1<2^24 := inside
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by dsimp [treeWord,cur];omega
  constructor
  · intro j larger small
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      (show (parentAfter s cur reply).mem=(parentWritten s cur reply).mem from rfl)]
    by_cases last : j=cur
    · subst j
      have written := write_bits_digest (bits := 256) s (8*treeWord cur) 0 reply (by decide) (by decide)
      simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at written
      apply written.trans
      unfold reply
      rw [child_pair,prior.nodes (2*cur+1) (by dsimp [cur];omega) (by dsimp [cur];omega),
        prior.nodes (2*cur) (by dsimp [cur];omega) (by dsimp [cur];omega),show heap cur=_ from tree]
    · have diff : cur<j := by dsimp [cur] at *;omega
      apply Eq.trans _ (prior.nodes j diff small)
      apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*treeWord j) 32 writeRange
      · change j<2*2^24 at small;unfold treeWord;omega
      · right;unfold treeWord;omega
  · intro i
    apply Eq.trans _ (prior.nonces i)
    unfold nonceBuffer
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      (show (parentAfter s cur reply).mem=(parentWritten s cur reply).mem from rfl)]
    apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*leafSalt i.val) 16 writeRange
    · have small : i.val<2^24 := i.isLt;unfold leafSalt;omega
    · right;dsimp [treeWord,leafSalt,cur];omega

private theorem full_range_content (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (remaining count : Nat) (inside : remaining+count<LENGTH)
    (lower : hybridCut ≤ remaining)
    (tree : ∀ node, hybridCut<node → node<LENGTH →
      heap node=oracle.compression (heap (2*node+1) ++ heap (2*node)))
    (prior : ParentContent state heap salts (remaining+count))
    (regs : ParentRegs state (remaining+count)) :
    let result := (checkEvaluation oracle (parentsTrace remaining count state)).1
    ParentContent result heap salts remaining ∧ ParentRegs result remaining := by
  induction count generalizing state with
  | zero =>
    simpa only [parentsTrace,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [parentsTrace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInput state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · exact full_node_content oracle state heap salts (remaining+count) (by omega) (tree _ (by omega) (by omega)) prior
    · exact next_parent_regs state (remaining+count) _ regs

theorem hybrid_lower_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (span n : Nat) (bound : hybridCut+span*n<LENGTH)
    (tree : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (prior : ParentContent s heap salts (hybridCut+span*n)) (regs : ParentRegs s (hybridCut+span*n)) :
    let out := (checkEvaluation oracle (hybridLowerFor span n s)).1
    ParentContent out heap salts hybridCut ∧ ParentRegs out hybridCut := by
  induction n generalizing s with
  | zero => simpa only [hybridLowerFor,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using And.intro prior regs
  | succ n ih =>
    have amount : hybridCut+span*(n+1)=hybridCut+span*n+span := by rw [Nat.mul_succ,Nat.add_assoc]
    rw [amount] at prior regs bound
    have step := full_range_content oracle s heap salts (hybridCut+span*n) span bound (by omega) tree prior regs
    rw [hybridLowerFor,check_evaluation_bind]
    apply ih _ (by omega)
    · exact content_setpc _ _ _ _ _ step.1
    · exact ⟨step.2.source,step.2.target,step.2.selector,step.2.size,step.2.primitive,step.2.heap⟩

theorem new_node_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (n : Nat) (inside : n+1<LENGTH)
    (tree : heap (n+1)=R1bParents.retained (n+1) (oracle.compression (heap (2*(n+1)+1) ++ heap (2*(n+1)))))
    (prior : ParentContent s heap salts (n+1)) (r : R1bParents.Ready s (n+1)) :
    ParentContent (R1bParents.nextState s (n+1) (oracle.compression (parentInput s (n+1)))) heap salts n := by
  let cur := n+1
  let raw : BitVec 256 := oracle.compression (parentInput s cur)
  let reply := R1bParents.retained cur raw
  have memory : (R1bParents.nextState s cur raw).mem=(parentWritten s cur reply).mem  := by
    change (R1bParents.laneState s cur raw).mem=(parentWritten s cur reply).mem
    unfold R1bParents.laneState
    by_cases lo : cur<524288
    · rw [if_pos lo]
      change _=(parentWritten s cur (R1bParents.retained cur raw)).mem
      rw [R1bParents.retained,if_pos lo]
      exact R1bParents.narrowed_mem s cur raw (by omega) r.toParentRegs r.mask
    · rw [if_neg lo]
      change _=(parentWritten s cur (R1bParents.retained cur raw)).mem
      rw [R1bParents.retained,if_neg lo]
      exact packed_parent_memory s cur raw r.toParentRegs inside
  have intBound : n+1<2^24 := inside
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
        prior.nodes (2*cur) (by dsimp [cur];omega) (by dsimp [cur];omega),show heap cur=_ from tree]
    · have diff : cur<j := by dsimp [cur] at *;omega
      apply Eq.trans _ (prior.nodes j diff small)
      apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*treeWord j) 32 writeRange
      · change j<2*2^24 at small;unfold treeWord;omega
      · right;unfold treeWord;omega
  · intro i
    apply Eq.trans _ (prior.nonces i)
    unfold nonceBuffer
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      memory]
    apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*leafSalt i.val) 16 writeRange
    · have small : i.val<2^24 := i.isLt;unfold leafSalt;omega
    · right;dsimp [treeWord,leafSalt,cur];omega


end TwoPermutationPrototype.RV64
