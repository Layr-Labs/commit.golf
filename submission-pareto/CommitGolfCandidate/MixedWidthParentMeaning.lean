import CommitGolfCandidate.MixedWidthParentControl
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
import CommitGolfCandidate.TwoPermutationMixedTranscript
import CommitGolfCandidate.TwoPermutationCounted

/-! Range-local parent semantics. The full-width phase only assumes full-width
parents above its stopping boundary; the projected phase only assumes projected
parents below its ceiling. Neither theorem assumes a globally uniform tree. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind check_evaluation_support
  write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation leavesTrace parentsTrace parentBatches readBuffer
  finalReply fullLeafDigests readyState fullParents parentBatch

theorem full_parent_content_step_at (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
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
        prior.nodes (2*cur) (by dsimp [cur];omega) (by dsimp [cur];omega),tree]
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

theorem packed_parent_content_step_at (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
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
        prior.nodes (2*cur) (by dsimp [cur];omega) (by dsimp [cur];omega),tree]
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

theorem full_sequence_content_range (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (boundary remaining count : Nat)
    (lower : boundary ≤ remaining) (inside : remaining+count<LENGTH)
    (tree : ∀ node, boundary<node → node<LENGTH →
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
    · exact full_parent_content_step_at oracle state heap salts (remaining+count) (by omega)
        (tree _ (by omega) (by omega)) prior
    · exact next_parent_regs state (remaining+count) _ regs

theorem full_groups_content_range (oracle : Oracle) (base : Word) (span boundary groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128)
    (inside : boundary+span*groups<LENGTH)
    (tree : ∀ node, boundary<node → node<LENGTH →
      heap node=oracle.compression (heap (2*node+1) ++ heap (2*node)))
    (prior : ParentContent state heap salts (boundary+span*groups))
    (regs : ParentRegs state (boundary+span*groups)) :
    ParentContent (checkEvaluation oracle (FullWidth.parentGroups base span boundary groups state)).1
      heap salts boundary := by
  induction groups generalizing state with
  | zero =>
    simpa only [FullWidth.parentGroups,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using prior
  | succ groups ih =>
    simp only [Nat.mul_succ, ← Nat.add_assoc] at inside prior regs
    have body := full_sequence_content_range oracle state heap salts boundary (boundary+span*groups)
      span (by omega) (by omega) tree prior regs
    rw [FullWidth.parentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact content_setpc _ _ heap salts (boundary+span*groups) body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap⟩

theorem projected_sequence_content_range (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (ceiling remaining count : Nat)
    (limit : ceiling≤LENGTH) (inside : remaining+count<ceiling)
    (tree : ∀ node, 0<node → node<ceiling →
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
    apply ih _ (by omega)
    · exact packed_parent_content_step_at oracle state heap salts (remaining+count) (by omega)
        (tree _ (by omega) (by omega)) prior regs
    · exact packed_next_parent_regs state (remaining+count) _ regs

theorem projected_groups_content_range (oracle : Oracle) (base : Word) (span groups ceiling : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128)
    (limit : ceiling≤LENGTH) (inside : span*groups<ceiling)
    (tree : ∀ node, 0<node → node<ceiling →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : ParentContent state heap salts (span*groups)) (regs : ParentRegs state (span*groups)) :
    ParentContent (checkEvaluation oracle (packedParentGroups base span groups state)).1 heap salts 0 := by
  induction groups generalizing state with
  | zero => simpa only [packedParentGroups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ] at inside prior regs
    have body := projected_sequence_content_range oracle state heap salts ceiling (span*groups) span
      limit inside tree prior regs
    rw [packedParentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact content_setpc _ _ heap salts (span*groups) body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap⟩

theorem mixed_heap_full_parent (compress : Compression) (leaves : DigestTape) (node : Nat)
    (large : 2^22≤node) (inside : node<LENGTH) :
    mixedTranscriptHeap compress leaves node = compress
      (mixedTranscriptHeap compress leaves (2*node+1) ++ mixedTranscriptHeap compress leaves (2*node)) := by
  have positive : 0 < node := lt_of_lt_of_le (show 0 < (2 : Nat)^22 by decide) large
  let answer : BitVec 256 := compress
    (mixedTranscriptHeap compress leaves (2*node+1) ++ mixedTranscriptHeap compress leaves (2*node))
  have parent : mixedTranscriptHeap compress leaves node = projectMixed node answer :=
    mixed_heap_parent compress leaves node positive inside
  exact parent.trans (projectMixed_full node answer large)

theorem mixed_heap_short_parent (compress : Compression) (leaves : DigestTape) (node : Nat)
    (positive : 0<node) (small : node<2^22) :
    mixedTranscriptHeap compress leaves node = projectReply (compress
      (mixedTranscriptHeap compress leaves (2*node+1) ++ mixedTranscriptHeap compress leaves (2*node))) := by
  have inside : node<LENGTH := by change node<16777216; norm_num at small; omega
  let answer : BitVec 256 := compress
    (mixedTranscriptHeap compress leaves (2*node+1) ++ mixedTranscriptHeap compress leaves (2*node))
  have parent : mixedTranscriptHeap compress leaves node = projectMixed node answer :=
    mixed_heap_parent compress leaves node positive inside
  exact parent.trans ((projectMixed_projected node answer small).trans
    (show CommitGolfCandidate.ShortTree.padLow answer = projectReply answer from rfl))

theorem counted_full_width_groups (oracle : Oracle) (base : Word) (span boundary groups : Nat)
    (state : MachineState) :
    RunPublic oracle (FullWidth.parentGroups base span boundary groups state) (span*groups) := by
  induction groups generalizing state with
  | zero => exact run_pure_public oracle state
  | succ groups ih =>
    rw [FullWidth.parentGroups,
      show span*(groups+1)=span+span*groups by rw [Nat.mul_succ,Nat.add_comm]]
    exact run_bind_public oracle _ _ span (span*groups) (counted_parents ..) (fun out => ih _)

/-- The proposed two phases meet at node2^22−1, with no hole or overlap. -/
theorem mixed_parent_phases_content (oracle : Oracle) (state : MachineState)
    (leaves : DigestTape) (salts : Index → BitVec 128)
    (prior : ParentContent state (mixedTranscriptHeap oracle.compression leaves) salts (2^24-1))
    (regs : ParentRegs state (2^24-1)) (pc : state.pc=184768) :
    let full := (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 4194303 384 state)).1
    ParentContent (checkEvaluation oracle (packedParentGroups 577992 15709 267 full)).1
      (mixedTranscriptHeap oracle.compression leaves) salts 0 := by
  let heap := mixedTranscriptHeap oracle.compression leaves
  let full := (checkEvaluation oracle (FullWidth.parentGroups 184768 32768 4194303 384 state)).1
  have fullContent : ParentContent full heap salts 4194303 :=
    full_groups_content_range oracle 184768 32768 4194303 384 state heap salts (by decide)
      (fun node large inside => mixed_heap_full_parent _ _ node (by norm_num; omega) inside)
      prior regs
  have fullRegs : ParentRegs full 4194303 :=
    (FullWidth.groups_post 184768 32768 4194303 384 state (by decide) (fun _ => pc) regs
      (check_evaluation_support oracle (FullWidth.parentGroups 184768 32768 4194303 384 state))).1
  exact projected_groups_content_range oracle 577992 15709 267 (2^22) full heap salts
    (by decide) (by decide) (fun node positive small => mixed_heap_short_parent _ _ node positive small)
    fullContent fullRegs

end TwoPermutationPrototype.RV64
