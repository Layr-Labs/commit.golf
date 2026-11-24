import CommitGolfCandidate.ChainedParentContentRun
import CommitGolfCandidate.TwoPermutationPackedLeafSpill
import CommitGolfCandidate.TwoPermutationPackedZeroContent

/-! Content induction for the unchanged delivered leaves, independent of legacy packed parents. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype.RV64.PackedLeaves
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation groups group batch

theorem leaf_same_memory (oracle : Oracle) (before : Memory) (s t : MachineState) (pos : Nat)
    (same : t.mem = s.mem) (prior : PinnedLeafPrefix oracle before s pos) : PinnedLeafPrefix oracle before t pos := by
  have mem : memoryView t = memoryView s := by funext word; change t.mem _ = s.mem _; rw [same]
  refine ⟨?_,?_,?_⟩
  · intro i hi; rw [mem]; exact prior.digests i hi
  · intro i lo hi; rw [mem]; exact prior.messages i lo hi
  · intro i hi; rw [mem]; exact prior.salts i hi

theorem leaf_prefix_unit (oracle : Oracle) (before : Memory) (s : MachineState) (g u : Nat)
    (bound : g < 2^12) (inside : u < 4096) (r : Regs s g u) (prior : PinnedLeafPrefix oracle before s (4096*g+u)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (unitTrace s g u)).1 (4096*g+u+1) := by
  have slot : (posSlot u).val = u := Nat.mod_eq_of_lt inside
  have start : PinnedLeafPrefix oracle before s (4096*g+(posSlot u).val) := by rw [slot]; exact prior
  have regs : Regs s g (posSlot u).val := by rw [slot]; exact r
  have raw := production_prefix_step oracle before s g (posSlot u) bound regs start
  simp only [slot] at raw
  simp only [unitTrace,check_evaluation_bind,check_evaluation_pure]
  exact leaf_same_memory _ _ _ _ _ (rebase_mem _ u) raw

theorem leaf_prefix_group (oracle : Oracle) (before : Memory) (s : MachineState) (g count u : Nat)
    (bound : g < 2^12) (inside : u+count ≤ 4096) (r : Regs s g u) (prior : PinnedLeafPrefix oracle before s (4096*g+u)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (group g count u s)).1 (4096*g+u+count) := by
  induction count generalizing s u with
  | zero => simpa only [group,check_evaluation_pure,Nat.add_zero] using prior
  | succ k ih =>
    simp only [group,check_evaluation_bind]
    have next := leaf_prefix_unit oracle before s g u bound (by omega) r prior
    have regs := unit_post s g u bound (by omega) r (check_evaluation_support oracle (unitTrace s g u))
    rw [show 4096*g+u+(k+1) = 4096*g+(u+1)+k by omega]
    exact ih _ (u+1) (by omega) regs (by simpa only [←Nat.add_assoc] using next)

theorem leaf_prefix_batch (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (bound : g < 2^12)
    (r : Regs s g 0) (prior : PinnedLeafPrefix oracle before s (4096*g)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (batch g s)).1 (4096*(g+1)) := by
  have carry (p : OracleComp World MachineState) (pc : Word) (count : Nat)
      (h : PinnedLeafPrefix oracle before (checkEvaluation oracle p).1 count) :
      PinnedLeafPrefix oracle before (checkEvaluation oracle (p >>= fun z => pure (z.setPC pc))).1 count := by
    simp only [check_evaluation_bind,check_evaluation_pure]
    exact leaf_same_memory _ _ (checkEvaluation oracle p).1 _ _ rfl h
  unfold batch
  apply carry
  rw [show 4096*(g+1) = 4096*g+0+4096 by omega]
  exact leaf_prefix_group oracle before s g 4096 0 bound (by decide) r prior

theorem leaf_prefix_groups (oracle : Oracle) (before : Memory) (s : MachineState) (count g : Nat)
    (limit : g+count = 2^12) (r : 0 < count → Regs s g 0) (prior : PinnedLeafPrefix oracle before s (4096*g)) :
    PinnedLeafPrefix oracle before (checkEvaluation oracle (groups count g s)).1 (4096*(g+count)) := by
  induction count generalizing s g with
  | zero => simpa only [groups,check_evaluation_pure,Nat.add_zero] using prior
  | succ k ih =>
    simp only [groups,check_evaluation_bind]
    have valid := r (by omega)
    have next := leaf_prefix_batch oracle before s g (by omega) valid prior
    have endReg := (batch_post s g (by omega) valid (check_evaluation_support oracle (batch g s))).1
    rw [show g+(k+1) = g+1+k by omega]
    exact ih _ (g+1) (by omega) (fun more => endReg (by omega)) next

noncomputable def pinnedLeafNodes (oracle : Oracle) (ready : MachineState) (node : Nat) : BitVec 238 :=
  BitVec.ofNat 238 (outputDigest (pinnedFinalReply oracle (memoryView ready) (node-LENGTH))).toNat

theorem evaluation_map_property (oracle : Oracle) (program : OracleComp World MachineState)
    (f : MachineState → MachineState) (property : MachineState → Prop)
    (holds : property (f (checkEvaluation oracle program).1)) :
    property (checkEvaluation oracle (program >>= fun out => pure (f out))).1 := by
  rw [check_evaluation_bind]
  simpa only [check_evaluation_pure] using holds

theorem leaf_prefix_content (oracle : Oracle) (ready : MachineState) (regs : Chain.BodyRegs ready)
    (salts : Index → BitVec 128)
    (original : ∀ i : Index, (window (memoryView ready) (leafSalt i.val) : TwoPermutationPrototype.Words 2) = saltWords (salts i)) :
    Fast.RawLeaves (checkEvaluation oracle (leafPrefixTrace ready)).1
      (referenceHeap oracle (pinnedLeafNodes oracle ready)) ∧
      ∀ i : Index, readBuffer (checkEvaluation oracle (leafPrefixTrace ready)).1 (8*leafSalt i.val) 16 = salts i := by
  apply evaluation_map_property oracle (executableLeaves.trace ready) skipEntry
    (fun state => Fast.RawLeaves state (referenceHeap oracle (pinnedLeafNodes oracle ready)) ∧
      ∀ i : Index, readBuffer state (8*leafSalt i.val) 16 = salts i)
  let leaves := (checkEvaluation oracle (executableLeaves.trace ready)).1
  have fin := executableLeaves.finished ready regs leaves (check_evaluation_support oracle (executableLeaves.trace ready))
  have pinned : PinnedLeafPrefix oracle (memoryView ready) leaves (2^24) :=
    leaf_prefix_groups oracle (memoryView ready) ready (2^12) 0 (by decide) (fun _ => chain_regs ready regs)
      (empty_pinned_leaf_prefix oracle ready)
  have ref (i : Index) :
      (referenceHeap oracle (pinnedLeafNodes oracle ready) (LENGTH+i.val)).setWidth 256 =
        BitVec.ofNat 256 ((outputDigest (pinnedFinalReply oracle (memoryView ready) i.val)).toNat % 2^238) := by
    rw [reference_heap_leaf oracle _ _ (by have := i.isLt; change 2^24 ≤ 2^24+i.val; omega)
      (by have hi := i.isLt; change i.val < 2^24 at hi; change 2^24+i.val < 2^25; omega)]
    unfold pinnedLeafNodes
    rw [Nat.add_sub_cancel_left]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  have mem : (skipEntry leaves).mem = leaves.mem :=
    (skip_entry_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop).2.2.2.2
  have view (w : Nat) : memoryView (skipEntry leaves) w = memoryView leaves w := by
    rw [TwoPermutationPrototype.RV64.PackedLeaves.memory_view_mem,
      TwoPermutationPrototype.RV64.PackedLeaves.memory_view_mem,mem]
  refine ⟨?_,?_⟩
  · intro node lo hi
    have valid : node-LENGTH < LENGTH := by change node-2^24 < 2^24; omega
    let i : Index := ⟨node-LENGTH,valid⟩
    have idx : node = LENGTH+i.val := by change node = 2^24+(node-2^24); omega
    have raw : heapDigest (skipEntry leaves) node = outputDigest (pinnedFinalReply oracle (memoryView ready) i.val) := by
      unfold heapDigest
      have addr : heapBase+32*node = 8*leafDest i.val := by
        unfold heapBase leafDest;change _ = 8*(516+36*2^24+4*(node-2^24));omega
      rw [addr]
      apply aligned_buffer_eq (skipEntry leaves) _ 32 (by decide)
      intro k hk
      have value := congrFun (pinned.digests i.val i.isLt) (⟨k,hk⟩ : Fin 4)
      change memoryView leaves (leafDest i.val+k)=_ at value
      rw [low_digest_word _ (⟨k,hk⟩ : Fin 4)] at value
      rw [view];exact value
    have fl : ∀ v : Output, finalValue Fast.leafH v = BitVec.ofNat 256 (v.toNat % 2^238) := fun v => rfl
    rw [raw,fl,idx,ref i]
  · intro i
    apply aligned_buffer_eq (skipEntry leaves) _ 16 (by decide)
    intro k hk
    have v := congrFun ((pinned.salts i.val i.isLt).trans (original i)) (⟨k,hk⟩ : Fin 2)
    rw [view];exact v

end CommitGolfCandidate.Chained.Native
