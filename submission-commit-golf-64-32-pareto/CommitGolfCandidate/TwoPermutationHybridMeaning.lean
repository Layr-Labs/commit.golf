import CommitGolfCandidate.TwoPermutationHybridPhase
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation parentsTrace packedParentsTrace packedParentGroups hybridLowerFor hybridUpper hybridParentPhase readBuffer

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

private theorem packed_node_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (n : Nat) (inside : n+1<LENGTH)
    (tree : heap (n+1)=projectReply (oracle.compression (heap (2*(n+1)+1) ++ heap (2*(n+1)))))
    (prior : ParentContent s heap salts (n+1)) (regs : ParentRegs s (n+1)) :
    ParentContent (packedParentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) heap salts n := by
  let cur := n+1
  let raw : BitVec 256 := oracle.compression (parentInput s cur)
  let reply := projectReply raw
  have memory : (packedParentAfter s cur raw).mem=(parentWritten s cur reply).mem :=
    packed_parent_memory s cur raw regs inside
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

private theorem packed_range_content (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (remaining count : Nat) (inside : remaining+count<LENGTH)
    (upper : remaining+count≤hybridCut)
    (tree : ∀ node, 0<node → node≤hybridCut →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : ParentContent state heap salts (remaining+count))
    (regs : ParentRegs state (remaining+count)) :
    let result := (checkEvaluation oracle (packedParentsTrace remaining count state)).1
    ParentContent result heap salts remaining ∧ ParentRegs result remaining := by
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
    apply ih _ (by omega) (by omega)
    · exact packed_node_content oracle state heap salts (remaining+count) (by omega) (tree _ (by omega) (by omega)) prior regs
    · exact packed_next_parent_regs state (remaining+count) _ regs

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

private theorem upper_groups_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (span n : Nat) (upper : span*n≤hybridCut)
    (tree : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=projectReply (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent s heap salts (span*n)) (regs : ParentRegs s (span*n)) :
    ParentContent (checkEvaluation oracle (packedParentGroups 610808 span n s)).1 heap salts 0 := by
  induction n generalizing s with
  | zero => simpa only [packedParentGroups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ n ih =>
    rw [Nat.mul_succ] at upper prior regs
    have room : span*n+span<LENGTH := by change _<16777216;change _≤65535 at upper;omega
    have step := packed_range_content oracle s heap salts (span*n) span room upper tree prior regs
    rw [packedParentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact content_setpc _ _ _ _ _ step.1
    · exact ⟨step.2.source,step.2.target,step.2.selector,step.2.size,step.2.primitive,step.2.heap⟩

private theorem phase_with_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (span n width batches prefixCount : Nat)
    (endBound : hybridCut+span*n<LENGTH) (cut : width*batches+prefixCount=hybridCut)
    (raw : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=projectReply (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent s heap salts (hybridCut+span*n)) (regs : ParentRegs s (hybridCut+span*n)) :
    ParentContent (checkEvaluation oracle (hybridLowerFor span n (hybridStart s) >>= fun low =>
      packedParentsTrace (width*batches) prefixCount (low.setPC 886808) >>= fun mid =>
        packedParentGroups 610808 width batches (mid.setPC 610808))).1 heap salts 0 := by
  have initial : ParentContent (hybridStart s) heap salts (hybridCut+span*n) := by
    constructor
    · intro j lo hi;unfold nodeDigest;rw [read_buffer_memory_congr _ s (show (hybridStart s).mem=s.mem from rfl)]
      exact prior.nodes _ lo hi
    · intro j;unfold nonceBuffer;rw [read_buffer_memory_congr _ s (show (hybridStart s).mem=s.mem from rfl)]
      exact prior.nonces j
  have lower := hybrid_lower_content oracle (hybridStart s) heap salts span n endBound raw initial (hybrid_start_regs s _ regs)
  let mid := (checkEvaluation oracle (hybridLowerFor span n (hybridStart s))).1
  have nr : ParentRegs (mid.setPC 886808) hybridCut :=
    ⟨lower.2.source,lower.2.target,lower.2.selector,lower.2.size,lower.2.primitive,lower.2.heap⟩
  have part := packed_range_content oracle (mid.setPC 886808) heap salts (width*batches) prefixCount
    (by rw [cut];decide) (by omega) masked (by rw [cut];exact content_setpc mid 886808 _ _ _ lower.1) (by rw [cut];exact nr)
  let middle :=  (checkEvaluation oracle (packedParentsTrace (width*batches) prefixCount (mid.setPC 886808))).1
  have rr : ParentRegs (middle.setPC 610808) (width*batches) :=
    ⟨part.2.source,part.2.target,part.2.selector,part.2.size,part.2.primitive,part.2.heap⟩
  have full := upper_groups_content oracle (middle.setPC 610808) heap salts width batches (by omega) masked
    (content_setpc middle 610808 heap salts (width*batches) part.1) rr
  have high := content_bound oracle (packedParentsTrace (width*batches) prefixCount (mid.setPC 886808))
    (fun t => packedParentGroups 610808 width batches (t.setPC 610808)) heap salts 0 full
  exact content_bound oracle (hybridLowerFor span n (hybridStart s))
    (fun low => packedParentsTrace (width*batches) prefixCount (low.setPC 886808) >>= fun mid =>
      packedParentGroups 610808 width batches (mid.setPC 610808)) heap salts 0 high

theorem hybrid_parent_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128)
    (raw : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=projectReply (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent s heap salts (2^24-1)) (regs : ParentRegs s (2^24-1)) :
    ParentContent (checkEvaluation oracle (hybridParentPhase s)).1 heap salts 0 := by
  unfold hybridParentPhase hybridUpper
  exact phase_with_content oracle s heap salts fullSpan 510 27595 2 10345 (by decide) (by decide) raw masked prior regs

theorem counted_lower (oracle : Oracle) (s : MachineState) (n : Nat) :
    RunPublic oracle (hybridLower n s) (fullSpan*n) := by
  induction n generalizing s with
  | zero => simpa only [hybridLower,hybridLowerFor,Nat.mul_zero] using run_pure_public oracle s
  | succ n ih =>
    rw [hybridLower,hybridLowerFor,show fullSpan*(n+1)=fullSpan+fullSpan*n by rw [Nat.mul_succ,Nat.add_comm]]
    exact run_bind_public oracle _ _ fullSpan (fullSpan*n) (counted_parents ..) (fun out => ih _)

theorem counted_hybrid_phase (oracle : Oracle) (state : MachineState) :
    RunPublic oracle (hybridParentPhase state) 16777215 := by
  unfold hybridParentPhase
  apply run_bind_public _ _ _ 16711680 65535 (counted_lower oracle _ 510)
  intro out
  unfold hybridUpper
  exact run_bind_public _ _ _ 10345 (27595*2) (counted_packed_parents ..) (fun mid => counted_packed_groups ..)

end TwoPermutationPrototype.RV64
