import CommitGolfCandidate.ChainedHeapMeaning

/-! Semantic node-count induction for every concrete native heap level. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] nodeTrace checkEvaluation readBuffer

theorem HeapContent.frame {s out : MachineState} {heap remaining}
    (prior : HeapContent s heap remaining) (same : ∀ query, out.getMem query = s.getMem query) :
    HeapContent out heap remaining := by
  constructor
  intro node larger small
  exact (read_digest_congr out s _ (by unfold heapBase; omega) (fun i _ => same _)).trans
    (prior.nodes node larger small)

theorem HeapNodeReady.next {s : MachineState} {h : Height} {node : Nat}
    (ready : HeapNodeReady s h node) (out : MachineState)
    (reached : out ∈ support (nodeTrace h s)) (positive : 0 < node) :
    HeapNodeReady out h (node-1) := by
  refine ⟨ready.args.node h reached,?_,?_,
    (node_register s out h reached .x17 (by decide)).trans ready.height,
    (node_register s out h reached .x16 (by decide)).trans ready.mask,by have := ready.small; omega⟩
  · rw [node_source s out h reached,ready.source]
    change cursorAt (heapAddress (2*node)) 64 1 = heapAddress (2*(node-1))
    rw [heap_cursor64 _ _ (by omega)]
    congr 1
    omega
  · rw [node_target s out h reached,ready.target]
    exact heap_cursor32 node 1 (by omega)

theorem HeapLevelReady.content_header {s : MachineState} {h : Height} {count : Nat}
    (ready : HeapLevelReady s h count) : HeapNodeReady (parentLevelPrefix s h 5) h (2*count-1) := by
  have positive := ready.positive
  refine ⟨ready.header.args,?_,?_,level_height s h,level_mask s h,by have := ready.small; omega⟩
  · rw [level_header_register s h .x6 (by decide),ready.source]
    congr 1
    omega
  · rw [level_header_register s h .x7 (by decide),ready.target]

theorem level_content_loop (oracle : Oracle) (heap : Nat → BitVec 238) (h : Height)
    (remaining count : Nat) (s : MachineState) (ready : HeapNodeReady s h (remaining+count))
    (tree : ∀ node, remaining < node → node ≤ remaining+count →
      (heap node).setWidth 256 = parentValue oracle h (heap (2*node)) (heap (2*node+1)))
    (prior : HeapContent s heap (remaining+count)) :
    HeapContent (checkEvaluation oracle (levelTrace h count s)).1 heap remaining := by
  induction count generalizing s with
  | zero => simpa only [levelTrace,check_evaluation_pure,Nat.add_zero] using prior
  | succ count ih =>
    let out := (checkEvaluation oracle (nodeTrace h s)).1
    have reached := check_evaluation_support oracle (nodeTrace h s)
    have positive : 0 < remaining+(count+1) := by omega
    have arithmetic : remaining+(count+1)-1 = remaining+count := by omega
    have next : HeapNodeReady out h (remaining+count) := by
      simpa only [arithmetic] using ready.next out reached positive
    have content : HeapContent out heap (remaining+count) := by
      simpa only [arithmetic] using node_content_step oracle s heap h _ positive ready
        (tree _ (by omega) (by omega)) prior
    rw [levelTrace,check_evaluation_bind]
    exact ih out next (fun node lower upper => tree node lower (by omega)) content

theorem heap_level_content (oracle : Oracle) (heap : Nat → BitVec 238) (h : Height)
    (count : Nat) (s : MachineState) (ready : HeapLevelReady s h count)
    (tree : ∀ node, count ≤ node → node < 2*count →
      (heap node).setWidth 256 = parentValue oracle h (heap (2*node)) (heap (2*node+1)))
    (prior : HeapContent s heap (2*count-1)) :
    HeapContent (checkEvaluation oracle (heapLevelTrace h count s)).1 heap (count-1) := by
  have positive := ready.positive
  have arithmetic : count-1+count = 2*count-1 := by omega
  have first : HeapNodeReady (parentLevelPrefix s h 5) h (count-1+count) := by
    rw [arithmetic]
    exact ready.content_header
  have initial : HeapContent (parentLevelPrefix s h 5) heap (count-1+count) := by
    rw [arithmetic]
    exact prior.frame (level_header_memory s h)
  exact level_content_loop oracle heap h (count-1) count _ first
    (fun node lower upper => tree node (by omega) (by omega)) initial

theorem stage_content (oracle : Oracle) (heap : Nat → BitVec 238) (h : Height)
    (s : MachineState) (ready : HeapLevelReady s h (heightCount h))
    (tree : ∀ node, heightCount h ≤ node → node < 2*heightCount h →
      (heap node).setWidth 256 = parentValue oracle h (heap (2*node)) (heap (2*node+1)))
    (prior : HeapContent s heap (2*heightCount h-1)) :
    HeapContent (checkEvaluation oracle (stageTrace h s)).1 heap (heightCount h-1) := by
  have content := heap_level_content oracle heap h _ s ready tree prior
  simpa only [stageTrace,check_evaluation_bind,check_evaluation_pure] using content.frame
    (shift_memory (checkEvaluation oracle (heapLevelTrace h (heightCount h) s)).1)

end CommitGolfCandidate.Chained.Native
