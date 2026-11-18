import CommitGolfCandidate.TwoPermutationWideLeafSpill
import CommitGolfCandidate.TwoPermutationWideLeafInput
import CommitGolfCandidate.TwoPermutationWideMeaning
import CommitGolfCandidate.TwoPermutationWideLeafLatch

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support splitBlocks read_buffer_memory_congr)

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation leavesTrace fullParents rootPrefix parentSetup readyState

theorem same_mem_prefix (oracle : Oracle) (before : Memory) (s t : MachineState) (pos : Nat) (h : t.mem=s.mem)
    (prev : LeafPrefix oracle before s pos) : LeafPrefix oracle before t pos := by
  have mem : memoryView t=memoryView s := by funext word;change t.mem _=s.mem _;rw [h]
  refine ⟨?_,?_,?_⟩
  · intro i hi;rw [mem];exact prev.digests i hi
  · intro i lo hi;rw [mem];exact prev.messages i lo hi
  · intro i hi;rw [mem];exact prev.salts i hi

theorem prefix_unit (oracle : Oracle) (before : Memory) (s : MachineState) (g u : Nat)
    (bound : g<2^16) (inside : u<256) (r : Regs s g u) (prev : LeafPrefix oracle before s (256*g+u)) :
    LeafPrefix oracle before (checkEvaluation oracle (unitTrace s g u)).1 (256*g+u+1) := by
  have eq : (posSlot u).val=u := Nat.mod_eq_of_lt inside
  have start : LeafPrefix oracle before s (256*g+(posSlot u).val) := by rw [eq];exact prev
  have ru : Regs s g (posSlot u).val := by rw [eq];exact r
  have raw := production_prefix_step oracle before s g (posSlot u) bound ru start
  simp only [eq] at raw
  simp only [unitTrace,check_evaluation_bind,check_evaluation_pure]
  exact same_mem_prefix _ _ _ _ _ (rebase_mem _ u) raw

theorem prefix_group (oracle : Oracle) (before : Memory) (s : MachineState) (g cnt u : Nat)
    (bound : g<2^16) (inside : u+cnt≤256) (r : Regs s g u) (prev : LeafPrefix oracle before s (256*g+u)) :
    LeafPrefix oracle before (checkEvaluation oracle (group g cnt u s)).1 (256*g+u+cnt) := by
  induction cnt generalizing s u with
  | zero => simpa only [group,check_evaluation_pure,Nat.add_zero] using prev
  | succ k ih =>
    simp only [group,check_evaluation_bind]
    have next := prefix_unit oracle before s g u bound (by omega) r prev
    have regs := unit_post s g u bound (by omega) r (check_evaluation_support oracle (unitTrace s g u))
    rw [show 256*g+u+(k+1)=256*g+(u+1)+k by omega]
    exact ih _ (u+1) (by omega) regs (by simpa only [←Nat.add_assoc] using next)

theorem prefix_batch (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (bound : g<2^16)
    (r : Regs s g 0) (prev : LeafPrefix oracle before s (256*g)) :
    LeafPrefix oracle before (checkEvaluation oracle (batch g s)).1 (256*(g+1)) := by
  have carry (p : OracleComp World MachineState) (pc : Word) (cnt : Nat)
      (h : LeafPrefix oracle before (checkEvaluation oracle p).1 cnt) :
      LeafPrefix oracle before (checkEvaluation oracle (p >>= fun z => pure (z.setPC pc))).1 cnt := by
    simp only [check_evaluation_bind,check_evaluation_pure]
    exact same_mem_prefix _ _ (checkEvaluation oracle p).1 _ _ rfl h
  unfold batch
  apply carry
  rw [show 256*(g+1)=256*g+0+256 by omega]
  exact prefix_group oracle before s g 256 0 bound (by decide) r prev

theorem prefix_groups (oracle : Oracle) (before : Memory) (s : MachineState) (cnt g : Nat)
    (limit : g+cnt=2^16) (r : 0<cnt → Regs s g 0) (prev : LeafPrefix oracle before s (256*g)) :
    LeafPrefix oracle before (checkEvaluation oracle (groups cnt g s)).1 (256*(g+cnt)) := by
  induction cnt generalizing s g with
  | zero => simpa only [groups,check_evaluation_pure,Nat.add_zero] using prev
  | succ k ih =>
    simp only [groups,check_evaluation_bind]
    have valid := r (by omega)
    have next := prefix_batch oracle before s g (by omega) valid prev
    have endReg := (batch_post s g (by omega) valid (check_evaluation_support oracle (batch g s))).1
    rw [show g+(k+1)=g+1+k by omega]
    exact ih _ (g+1) (by omega) (fun more => endReg (by omega)) next

theorem counted_raw (oracle : Oracle) (s : MachineState) (u : Fin 256) (start i dst : Nat) :
    RunPublic oracle (leafTrace s u start i dst) 2 := by
  unfold leafTrace
  apply run_bind_public _ _ _ 1 1 (run_query_public ..)
  intro a
  apply run_bind_public _ _ _ 1 0 (run_query_public ..)
  intro b;exact run_pure_public ..

theorem counted_unit (oracle : Oracle) (s : MachineState) (g u : Nat) : RunPublic oracle (unitTrace s g u) 2 :=
  run_bind_public _ _ _ 2 0 (counted_raw ..) (fun _ => run_pure_public ..)

theorem counted_group (oracle : Oracle) (s : MachineState) (g cnt u : Nat) : RunPublic oracle (group g cnt u s) (2*cnt) := by
  induction cnt generalizing s u with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega]
    exact run_bind_public _ _ _ 2 _ (counted_unit ..) (fun _ => ih _ _)

theorem counted_batch (oracle : Oracle) (s : MachineState) (g : Nat) : RunPublic oracle (batch g s) 512 :=
  run_bind_public _ _ _ (2*256) 0 (counted_group ..) (fun _ => run_pure_public ..)

theorem counted_groups (oracle : Oracle) (s : MachineState) (cnt g : Nat) : RunPublic oracle (groups cnt g s) (512*cnt) := by
  induction cnt generalizing s g with
  | zero => exact run_pure_public ..
  | succ k ih =>
    rw [show 512*(k+1)=512+512*k by omega]
    exact run_bind_public _ _ _ 512 _ (counted_batch ..) (fun _ => ih _ _)

theorem wide_ready_memory_view (s : MachineState) {bits : Nat} (packed : BitVec bits) :
    memoryView (wideReadyState s packed)=memoryView (readyState s packed) := by
  funext word
  change (wideReadyState s packed).mem _=(readyState s packed).mem _
  rw [wide_ready_state_memory]

theorem wide_reference_leaf (oracle : Oracle) (msg : Message) (packed : BitVec (128*LENGTH)) (i : Index) :
    Overlap.tree oracle msg (splitBlocks 128 LENGTH packed) (LENGTH+i.val)=
      outputDigest (finalReply oracle (memoryView (wideReadyState (Overlap.program.initialState .commit msg) packed)) i.val) := by
  rw [wide_ready_memory_view]
  rw [Overlap.tree,transcript_heap_leaf,Overlap.leafDigests,finalReply,wide_ready_messages Overlap.program rfl msg packed i,
    ready_salts _ packed i]

theorem parent_content_of_leaf_prefix (oracle : Oracle) (before : Memory) (leaves : MachineState)
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (inv : LeafPrefix oracle before leaves (2^24))
    (leaf : ∀ i : Index, heap (LENGTH+i.val)=outputDigest (finalReply oracle before i.val))
    (original_salts : ∀ i : Index, (window before (leafSalt i.val) : Words 2)=saltWords (salts i)) :
    ParentContent (parentSetup leaves 5) heap salts (2^24-1) := by
  constructor
  · intro n lo hi
    have valid : n-LENGTH<LENGTH := by omega
    let i : Index := ⟨n-LENGTH,valid⟩
    have idx : n=LENGTH+i.val := by change n=LENGTH+(n-LENGTH);change 2^24-1<n at lo; have e : LENGTH=2^24:=rfl;omega
    rw [idx,leaf i]
    unfold nodeDigest
    rw [read_buffer_memory_congr _ leaves (show (parentSetup leaves 5).mem=leaves.mem by unfold parentSetup; rfl)]
    have addr : treeWord (LENGTH+i.val)=leafDest i.val := by change 516+32*2^24+4*(2^24+i.val)=_;unfold leafDest;omega
    rw [addr]
    apply aligned_buffer_eq leaves _ 32 (by decide)
    intro k hk
    have value := congrFun (inv.digests i.val i.isLt) (⟨k,hk⟩ : Fin 4)
    change memoryView leaves (leafDest i.val+k)=_ at value
    rw [value]
    exact low_digest_word _ (⟨k,hk⟩ : Fin 4)
  · intro i
    unfold nonceBuffer
    rw [read_buffer_memory_congr _ leaves (show (parentSetup leaves 5).mem=leaves.mem by unfold parentSetup; rfl)]
    apply aligned_buffer_eq leaves _ 16 (by decide)
    intro k hk
    have v := (inv.salts i.val i.isLt).trans (original_salts i)
    exact congrFun v (⟨k,hk⟩ : Fin 2)



attribute [local irreducible] groups group batch

def executableMeaning : WideLeafMeaning executableLeaves where
  counted oracle s := counted_groups oracle s (2^16) 0
  content oracle msg packed := by
    let s := Overlap.program.initialState .commit msg
    let ready := wideReadyState s packed
    have entry : CommitEntry s := ⟨rfl,rfl,rfl,rfl⟩
    have rs := (entry_regs s entry packed).1
    have readySalts (i : Index) : (window (memoryView ready) (leafSalt i.val) : Words 2)=saltWords (splitBlocks 128 LENGTH packed i) := by
      rw [show memoryView ready=memoryView (readyState s packed) from wide_ready_memory_view s packed]
      exact ready_salts s packed i
    exact parent_content_of_leaf_prefix oracle (memoryView ready) _ _ _
      (prefix_groups oracle (memoryView ready) ready (2^16) 0 (by decide) (fun _ => rs) (empty_leaf_prefix oracle ready))
      (wide_reference_leaf oracle msg packed) readySalts

end TwoPermutationPrototype.RV64.WideLeaves
