import CommitGolfCandidate.ChainedCountedCommit

/-! The root copy preserves every cached heap node in the delivered trapdoor. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 4096
attribute [local irreducible] checkEvaluation parentLevels readBuffer

theorem root_heap_word (s : MachineState) (output : s.getReg .x8 = 4294971392)
    (node : Nat) (small : node < 2^25) (word : Fin 4) :
    (chainedRootPrefix s 10).getMem (heapAddress node+BitVec.ofNat 64 (8*word.val)) =
      s.getMem (heapAddress node+BitVec.ofNat 64 (8*word.val)) := by
  rw [root_tail_memory]
  apply root_memory_outside s _ _ 4 (by decide)
  intro j same
  have numeric := congrArg BitVec.toNat same
  rw [heap_word_numeric node word.val small (by have := word.isLt; omega),output] at numeric
  change heapBase+32*node+8*word.val =
    (BitVec.ofNat 64 4294971392+BitVec.ofNat 64 (8*j.val)).toNat at numeric
  have short := j.isLt
  rw [←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 4294971392+8*j.val < 2^64 by omega)] at numeric
  unfold heapBase at numeric
  omega

theorem root_heap_digest (s : MachineState) (output : s.getReg .x8 = 4294971392)
    (node : Nat) (small : node < 2^25) : heapDigest (chainedRootPrefix s 10) node = heapDigest s node := by
  apply output_ext_words
  intro i
  rw [←heap_read_word _ node i.val i.isLt,root_heap_word s output node small i,
    heap_read_word s node i.val i.isLt]

theorem complete_parent_heap_content (oracle : Oracle) (heap : Nat → BitVec 238) (tree : ChainedTree oracle heap)
    (s : MachineState) (pc : s.pc = 186848) (entry : FastEntry s)
    (output : s.getReg .x8 = 4294971392) (prior : Fast.RawLeaves s heap) :
    HeapContent (checkEvaluation oracle (completeParentTrace s)).1 heap 0 := by
  have fc := Fast.fast_levels_content oracle heap tree s pc entry output prior
  rw [show completeParentTrace s = Fast.fastParentTrace s from rfl,Fast.fast_parent_eval]
  constructor
  intro node positive small
  exact (root_heap_digest _ fc.2.2 node small).trans (fc.1.nodes node positive small)

theorem evaluation_bind_property (oracle : Oracle) (program : OracleComp World MachineState)
    (next : MachineState → OracleComp World MachineState) (property : MachineState → Prop)
    (holds : property (checkEvaluation oracle (next (checkEvaluation oracle program).1)).1) :
    property (checkEvaluation oracle (program >>= next)).1 := by
  rw [check_evaluation_bind]
  exact holds

theorem chained_commit_body_heap (oracle : Oracle) (ready : MachineState) (regs : Chain.BodyRegs ready)
    (salts : Index → BitVec 128)
    (original : ∀ i : Index, (window (memoryView ready) (leafSalt i.val) : Words 2) = saltWords (salts i)) :
    HeapContent (checkEvaluation oracle (chainedCommitBody ready)).1
      (referenceHeap oracle (pinnedLeafNodes oracle ready)) 0 := by
  apply evaluation_bind_property oracle (leafPrefixTrace ready) completeParentTrace
    (fun state => HeapContent state (referenceHeap oracle (pinnedLeafNodes oracle ready)) 0)
  let middle := (checkEvaluation oracle (leafPrefixTrace ready)).1
  have reached := check_evaluation_support oracle (leafPrefixTrace ready)
  exact complete_parent_heap_content oracle _ (reference_heap_tree oracle _) middle
    (leaf_prefix_parent_pc ready regs middle reached)
    (leaf_prefix_heap_ready ready regs middle reached) (leaf_prefix_output ready regs middle reached)
    (leaf_prefix_content oracle ready regs salts original).1

end CommitGolfCandidate.Chained.Native
