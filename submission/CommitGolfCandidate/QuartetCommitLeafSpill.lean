import CommitGolfCandidate.QuartetCommitLeafGroups
import CommitGolfCandidate.TwoPermutationPinnedCommitSpec
import CommitGolfCandidate.TwoPermutationCounted
namespace TwoPermutationPrototype.RV64.QuartetLeaves
open TwoPermutationPrototype.QuartetCommit
open TwoPermutationPrototype.RV64.PackedLeaves (pinnedWords rawPrefix pinnedWrites stamp pinned_digest_words pinned_word_outside)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
def pinnedFinalReply (oracle : Oracle) (mem : Memory) (i : Nat) : BitVec 1600 :=
  let msg := window mem (leafStart i+5)
  let salt := window mem (qSalt i)
  let a := oracle.permutation (packBuffer (rawPrefix msg))
  oracle.permutation (packBuffer (pinnedWords (secondTag i) salt (replyWords a) msg))

structure PinnedLeafPrefix (oracle : Oracle) (before : Memory) (s : MachineState) (count : Nat) : Prop where
  digests : ∀ i < count, (window (memoryView s) (qLeaf i) : Words 4) =
    lowDigest (replyWords (pinnedFinalReply oracle before i))
  messages : ∀ i, count ≤ i → i < 2^24 → (window (memoryView s) (leafStart i+5) : Words 32) =
    window before (leafStart i+5)
  salts : ∀ i < 2^24, (window (memoryView s) (qSalt i) : Words 2) = window before (qSalt i)

  padding : ∀ g<4194304, ∀ k<9, memoryView s (qSource g+k)=0

theorem empty_prefix (oracle : Oracle) (s : MachineState) (pad : ∀ g<4194304, ∀ k<9, memoryView s (qSource g+k)=0) :
    PinnedLeafPrefix oracle (memoryView s) s 0 := ⟨fun _ h => False.elim (by omega),fun _ _ _ => rfl,fun _ _ => rfl,pad⟩

theorem production_leaf_spill (s : MachineState) (g : Nat) (slot : Fin 4096) (bound : g < 2^12)
    (r : Regs s g slot.val) (a b : BitVec 1600) :
    let i := 4096*g+slot.val
    let mem := memoryView (finishedLeaf s slot (leafStart i) (qLeaf i) a b)
    (window mem (qLeaf i) = lowDigest (replyWords b)) ∧
    (∀ (j : Nat), j < i → ∀ k < 4, mem (qLeaf j+k) = memoryView s (qLeaf j+k)) ∧
    (∀ (j : Nat), i < j → j < 2^24 → ∀ k < 32, mem (leafStart j+5+k) = memoryView s (leafStart j+5+k)) ∧
    (∀ (j : Nat), j < 2^24 → ∀ k < 2, mem (qSalt j+k) = memoryView s (qSalt j+k)) ∧
    (∀ g<4194304, ∀ k<9, mem (qSource g+k)=memoryView s (qSource g+k)) := by
  dsimp only
  let i := 4096*g+slot.val
  have n : i<16777216 := by dsimp [i];have := slot.isLt;omega
  have ready := ready_slot s g slot bound r
  change LeafReady s slot (leafStart i) i (qLeaf i) _ at ready
  have same := fun word (limit : word<2^33) => finished_leaf_memory _ _ _ _ _ _ word ready a b limit
  obtain ⟨digest,prior,pad,msg,salt⟩ := leaf_spill_frame (memoryView s) i n (secondTag i) (nonceWords s slot) a b
  refine ⟨?_,?_,?_,?_,?_⟩
  · funext k
    exact (same (qLeaf i+k.val) (by unfold qLeaf qSource;have := k.isLt;omega)).trans (congrFun digest k)
  · intro j hj k hk;exact (same _ (by unfold qLeaf qSource;omega)).trans (prior j hj k hk)
  · intro j hj nj k hk;exact (same _ (by unfold leafStart;omega)).trans (msg j hj nj k hk)
  · intro j hj k hk;exact (same _ (by unfold qSalt;omega)).trans (salt j hj k hk)
  · intro j hj k hk;exact (same _ (by unfold qSource;omega)).trans (pad j hj k hk)

private theorem pinned_tag_matches (i : Index) : pinnedPositionTag i=secondTag i.val := by
  unfold pinnedPositionTag secondTag firstTag
  change BitVec.ofNat 64 (4152 + 256*i.val) = BitVec.ofNat 64 (4056+256*i.val)+BitVec.ofNat 64 96
  rw [←BitVec.ofNat_add]
  congr 1 <;> omega

theorem pinned_typed_words (i : Index) (n : Words 2) (r : Words 25) (m : Words 32) :
    pinnedSecondInput i n r m = pinnedWords (secondTag i.val) n r m := by
  unfold pinnedSecondInput pinnedWords
  rw [pinned_tag_matches]

theorem production_fixed_leaf (oracle : Oracle) (s : MachineState) (g : Nat) (slot : Fin 4096)
    (bound : g < 2^12) (r : Regs s g slot.val) :
    let idx : Index := ⟨4096*g+slot.val,by unfold LENGTH LOG_LENGTH;have := slot.isLt;omega⟩
    let message := window (memoryView s) (leafStart idx.val+5)
    let first := pinnedFirstRow oracle.permutation message
    let second := pinnedSecondRow oracle.permutation idx (nonceWords s slot) first.2 message
    CommitGolfCandidate.checkEvaluation oracle (leafTrace s slot (leafStart idx.val) idx.val (qLeaf idx.val)) =
      (finishedLeaf s slot (leafStart idx.val) (qLeaf idx.val) first.2 second.2,2) := by
  dsimp only
  simp only [leafTrace,CommitGolfCandidate.check_evaluation_public_bind,CommitGolfCandidate.check_evaluation_pure]
  simp only [pinnedFirstRow,pinnedSecondRow,pinned_typed_words]
  rfl

theorem nonce_memory_window (s : MachineState) (g : Nat) (slot : Fin 4096) (r : Regs s g slot.val) :
    nonceWords s slot = window (memoryView s) (qSalt (4096*g+slot.val)) := by
  funext k
  fin_cases k <;> simp only [nonceWords,window,memoryView,r.salts,centered_add] <;> dsimp <;>
    congr 1 <;> simp only [wordAddress,← BitVec.ofNat_add] <;> congr 1 <;> simp only [nonceBase,qSalt] <;> omega

theorem production_prefix_step (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (u : Fin 4096)
    (bound : g < 2^12) (r : Regs s g u.val) (inv : PinnedLeafPrefix oracle before s (4096*g+u.val)) :
    let i := 4096*g+u.val
    let next := (checkEvaluation oracle (leafTrace s u (leafStart i) i (qLeaf i))).1
    PinnedLeafPrefix oracle before next (i+1) := by
  let i := 4096*g+u.val
  have inside : i < 2^24 := by dsimp [i]; have := u.isLt; omega
  let idx : Index := ⟨i, by exact inside⟩
  let msg := (window (memoryView s) (leafStart i+5) : Words 32)
  let a := (pinnedFirstRow oracle.permutation msg).2
  let b := (pinnedSecondRow oracle.permutation idx (nonceWords s u) a msg).2
  have response : b = pinnedFinalReply oracle before i := by
    dsimp only [b,a,pinnedSecondRow,pinnedFirstRow]
    rw [pinned_typed_words]
    change oracle.permutation (packBuffer (pinnedWords (secondTag i) (nonceWords s u) (replyWords (oracle.permutation (packBuffer (rawPrefix msg)))) msg)) = _
    rw [nonce_memory_window s g u r, inv.salts i inside]
    dsimp only [msg]
    rw [inv.messages i (by omega) inside]
    rfl
  have step := production_fixed_leaf oracle s g u bound r
  have spill := production_leaf_spill s g u bound r a b
  change checkEvaluation oracle (leafTrace s u (leafStart i) i (qLeaf i)) =
    (finishedLeaf s u (leafStart i) (qLeaf i) a b,2) at step
  dsimp only
  rw [step]
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj
    by_cases last : j = i
    · subst j
      exact spill.1.trans (congrArg (fun x => lowDigest (replyWords x)) response)
    · have h : j < i := by change j < i+1 at hj; omega
      apply Eq.trans _ (inv.digests j h)
      funext k
      exact spill.2.1 j h k.val k.isLt
  · intro j later limit
    apply Eq.trans _ (inv.messages j (by change i+1 ≤ j at later; omega) limit)
    funext k
    exact spill.2.2.1 j (by change i+1 ≤ j at later; omega) limit k.val k.isLt
  · intro j limit
    apply Eq.trans _ (inv.salts j limit)
    funext k
    exact spill.2.2.2.1 j limit k.val k.isLt
  · intro j hj k hk
    exact (spill.2.2.2.2 j hj k hk).trans (inv.padding j hj k hk)

end TwoPermutationPrototype.RV64.QuartetLeaves
