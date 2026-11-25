import CommitGolfCandidate.QuadCommitExecution
import CommitGolfCandidate.QuadCommitPentaContent
import CommitGolfCandidate.TwoPermutationRootBytes

/-! Memory meaning of the whole tree phase: after the leaves, the cleared level-0 group and the
ten level passes, the trapdoor holds every slot of levels `0 … 10` and the salts; the root node
(the commitment) is the level-11 node. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling Penta
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support
  read_buffer_slice read_buffer_memory_congr write_bits_digest)
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local irreducible] image writeBits checkEvaluation rootPrefix
  readBuffer levels levelTrace loops trace zeroed

theorem level_content {k : Nat} (L : Layout k) (oracle : Oracle) (s : MachineState)
    (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape) (v : Values oracle nodes)
    (e : Entry L.W s) (r : Tree s nodes salts (k+1)) :
    Tree (checkEvaluation oracle (levelTrace L s)).1 nodes salts (k+2) := by
  have hk := L.level
  have count := L.count
  obtain ⟨regs,_⟩ := setup_regs L s e.heap e.selector e.size e.primitive
  have startPC : (setupState L s).pc=nodePC (L.W+9) 0 0 := by
    rw [Penta.setup_pc,e.pc];unfold nodePC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  let t := setupState L s
  have p0 : Partial t nodes salts k 0 :=
    ⟨tree_same_mem s t nodes salts (k+1) r (L.mem s),fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rw [levelTrace]
  simp only [check_evaluation_bind,check_evaluation_pure]
  have pa := loops_content oracle t nodes salts v k (L.W+9) L.S L.q 0 hk (by omega) p0
  rw [Nat.zero_add] at pa
  obtain ⟨ra,pcA,_⟩ := loops_any_post L t regs startPC (check_evaluation_support oracle _)
  have pb := sequence_content oracle _ nodes salts v k L.r (L.S*L.q) hk (by omega) pa
  obtain ⟨rb,_,_⟩ := sequence_post L.T k _ L.r (L.S*L.q) 0 ra pcA (check_evaluation_support oracle _)
  rw [count] at pb rb
  exact zero_content oracle _ nodes salts v k L.z hk pb rb.target L.ragged L.small

theorem levels_post (s : MachineState) (e : Entry 45217 s) {out : MachineState}
    (hit : out ∈ support (levels s)) : Entry 236533 out := by
  rw [levels] at hit
  simp only [mem_support_bind_iff] at hit
  obtain ⟨s1,h1,s2,h2,s3,h3,s4,h4,s5,h5,s6,h6,s7,h7,s8,h8,s9,h9,h10⟩ := hit
  have e1 := entry_post layout1 _ e h1
  have e2 := entry_post layout2 _ e1 h2
  have e3 := entry_post layout3 _ e2 h3
  have e4 := entry_post layout4 _ e3 h4
  have e5 := entry_post layout5 _ e4 h5
  have e6 := entry_post layout6 _ e5 h6
  have e7 := entry_post layout7 _ e6 h7
  have e8 := entry_post layout8 _ e7 h8
  have e9 := entry_post layout9 _ e8 h9
  exact entry_post layout10 _ e9 h10

private theorem eval_ten (oracle : Oracle) (s : MachineState)
    (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : MachineState → OracleComp World MachineState) :
    (checkEvaluation oracle (do
      let s1 ← f1 s; let s2 ← f2 s1; let s3 ← f3 s2; let s4 ← f4 s3; let s5 ← f5 s4
      let s6 ← f6 s5; let s7 ← f7 s6; let s8 ← f8 s7; let s9 ← f9 s8; let s10 ← f10 s9; pure s10)).1 =
      (checkEvaluation oracle (f10 (checkEvaluation oracle (f9 (checkEvaluation oracle (f8 (checkEvaluation oracle
        (f7 (checkEvaluation oracle (f6 (checkEvaluation oracle (f5 (checkEvaluation oracle (f4 (checkEvaluation oracle
        (f3 (checkEvaluation oracle (f2 (checkEvaluation oracle (f1 s)).1)).1)).1)).1)).1)).1)).1)).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

theorem levels_eval (oracle : Oracle) (s : MachineState) :
    (checkEvaluation oracle (levels s)).1 =
      let s1 := (checkEvaluation oracle (levelTrace layout1 s)).1
      let s2 := (checkEvaluation oracle (levelTrace layout2 s1)).1
      let s3 := (checkEvaluation oracle (levelTrace layout3 s2)).1
      let s4 := (checkEvaluation oracle (levelTrace layout4 s3)).1
      let s5 := (checkEvaluation oracle (levelTrace layout5 s4)).1
      let s6 := (checkEvaluation oracle (levelTrace layout6 s5)).1
      let s7 := (checkEvaluation oracle (levelTrace layout7 s6)).1
      let s8 := (checkEvaluation oracle (levelTrace layout8 s7)).1
      let s9 := (checkEvaluation oracle (levelTrace layout9 s8)).1
      (checkEvaluation oracle (levelTrace layout10 s9)).1 := by
  rw [levels]
  exact eval_ten oracle s (levelTrace layout1) (levelTrace layout2) (levelTrace layout3) (levelTrace layout4)
    (levelTrace layout5) (levelTrace layout6) (levelTrace layout7) (levelTrace layout8) (levelTrace layout9)
    (levelTrace layout10)

theorem levels_content (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256)
    (salts : CompleteSaltTape) (v : Values oracle nodes) (e : Entry 45217 s) (r : Tree s nodes salts 1) :
    Tree (checkEvaluation oracle (levels s)).1 nodes salts 11 := by
  rw [levels_eval]
  have t1 := level_content layout1 oracle s nodes salts v e r
  have e1 := entry_post layout1 s e (check_evaluation_support oracle (levelTrace layout1 s))
  have t2 := level_content layout2 oracle _ nodes salts v e1 t1
  have e2 := entry_post layout2 _ e1 (check_evaluation_support oracle (levelTrace layout2 _))
  have t3 := level_content layout3 oracle _ nodes salts v e2 t2
  have e3 := entry_post layout3 _ e2 (check_evaluation_support oracle (levelTrace layout3 _))
  have t4 := level_content layout4 oracle _ nodes salts v e3 t3
  have e4 := entry_post layout4 _ e3 (check_evaluation_support oracle (levelTrace layout4 _))
  have t5 := level_content layout5 oracle _ nodes salts v e4 t4
  have e5 := entry_post layout5 _ e4 (check_evaluation_support oracle (levelTrace layout5 _))
  have t6 := level_content layout6 oracle _ nodes salts v e5 t5
  have e6 := entry_post layout6 _ e5 (check_evaluation_support oracle (levelTrace layout6 _))
  have t7 := level_content layout7 oracle _ nodes salts v e6 t6
  have e7 := entry_post layout7 _ e6 (check_evaluation_support oracle (levelTrace layout7 _))
  have t8 := level_content layout8 oracle _ nodes salts v e7 t7
  have e8 := entry_post layout8 _ e7 (check_evaluation_support oracle (levelTrace layout8 _))
  have t9 := level_content layout9 oracle _ nodes salts v e8 t8
  have e9 := entry_post layout9 _ e8 (check_evaluation_support oracle (levelTrace layout9 _))
  have t10 := level_content layout10 oracle _ nodes salts v e9 t9
  exact t10

/-- Clearing slots 1 … 4 of the last level-0 group completes level 0. -/
theorem leaf_tree (oracle : Oracle) (s : MachineState) (nodes : Nat → Nat → BitVec 256) (salts : CompleteSaltTape)
    (v : Values oracle nodes)
    (digest : ∀ i, i<2^24 → ∀ t : Fin 4, memoryView s (leafWord i+t.val)=(nodes 0 i).extractLsb' (64*t.val) 64)
    (nonce : ∀ (i : Index) (t : Fin 2), memoryView s (saltWord i.val+t.val)=(salts i).extractLsb' (64*t.val) 64)
    (zeros : ∀ k g, k≤10 → g<pentaCount (k+1) → ∀ t : Fin 5, memoryView s (pentaGroupWord k g+t.val)=0)
    (x12 : s.getReg .x12=wordAddress (leafWord (2^24-1))) :
    Tree (zeroed s 32 16 16) nodes salts 1 := by
  let W := leafWord (2^24-1)
  have view : ∀ w, w<2^33 → memoryView (zeroed s 32 16 16) w = if W+4≤w ∧ w<W+4+16 then 0 else memoryView s w := by
    intro w hw
    have := zeroed_memory s 32 16 16 W le_rfl x12 (by decide) (by decide) (by decide) w hw
    simpa using this
  have outside : ∀ w, w<W+4 ∨ W+20≤w → w<2^33 → memoryView (zeroed s 32 16 16) w=memoryView s w := by
    intro w away hw
    rw [view w hw,if_neg (by omega)]
  have wv : W=groupWord 3355443+5 := by decide
  have count1 : pentaCount 1=3355444 := by decide
  refine ⟨?_,?_,?_⟩
  · intro i t
    have below := group_below_salts 0 3355443 (by decide) (by decide) i.val
    have top := salt_top i
    have := t.isLt
    rw [←group_word_level] at below
    unfold groupWord at below wv
    rw [outside _ (Or.inr (by omega)) (by omega)]
    exact nonce i t
  · intro l g hl hg t
    have := t.isLt
    have room := group_top l g hl hg
    have away : pentaGroupWord l g+t.val<W+4 ∨ W+20≤pentaGroupWord l g+t.val := by
      by_cases same : l=0
      · subst same
        left
        rw [wv,count1] at *
        rw [←group_word_level]
        unfold groupWord
        omega
      · have := level_order 0 l 3355443 (by omega) (by omega) (by decide) g
        rw [←group_word_level] at this
        unfold groupWord at this wv
        right;omega
    rw [outside _ away (by omega)]
    exact zeros l g hl hg t
  · intro l i hl hi t
    have := t.isLt
    have l0 : l=0 := by omega
    subst l0
    rw [count1] at hi
    rw [←leaf_word_level]
    by_cases real : i<2^24
    · have below : leafWord i+t.val<W+4 := by
        rw [wv];unfold leafWord groupWord;omega
      rw [outside _ (Or.inl below) (by unfold leafWord groupWord;omega)]
      exact digest i real t
    · have inRegion : W+4≤leafWord i+t.val ∧ leafWord i+t.val<W+4+16 := by
        rw [wv]
        unfold leafWord groupWord
        omega
      rw [view _ (by unfold leafWord groupWord;omega),if_pos inRegion,v.ragged 0 i (by change LENGTH ≤ i;rw [length_value];omega)]
      simp

/-! ### The whole tree phase -/

theorem penta_values (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) :
    Values oracle (pentaPublicNodes oracle message salts) := by
  constructor
  · intro k j inside
    unfold pentaPublicNodes
    rw [penta_node_succ _ _ k j inside]
    rfl
  · intro k j above
    unfold pentaPublicNodes
    cases k with
    | zero =>
      have : LENGTH≤j := above
      rw [pentaNode,dif_neg (by omega)]
    | succ k => rw [pentaNode,if_neg (by omega)]

/-- The serialized commitment and trapdoor, from any tree-phase end state. -/
theorem root_results (opening checker : Image) (oracle : Oracle) (message : Message)
    (salts tapeSalts : CompleteSaltTape) (tops : MachineState)
    (tree : Tree tops (pentaPublicNodes oracle message salts) tapeSalts 11) (entry : Entry 236533 tops)
    (result : Execution)
    (state : result.state=rootPrefix (writeBits (rootNode tops 4) (wordAddress (heapWord 1))
      (oracle.permutation (packBuffer (window (memoryView tops) (pentaGroupWord 10 0))))) 10) :
    let output := (submission opening checker).readCommit result
    output.1=pentaPublicNodes oracle message salts PENTA_LEVELS 0 ∧
    (∀ k j, k<PENTA_LEVELS → j<5*pentaCount (k+1) →
      pentaTrapdoorNode output.2 k j=pentaPublicNodes oracle message salts k j) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=tapeSalts i) := by
  have v := penta_values oracle message salts
  let nodes := pentaPublicNodes oracle message salts
  let reply := oracle.permutation (packBuffer (window (memoryView tops) (pentaGroupWord 10 0)))
  let w := writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply
  have wheap : w.getReg .x9=4294971424 := by
    change (writeBits _ _ _).getReg .x9=_
    rw [CommitGolfCandidate.writeBits_register,root_node_keep tops .x9 (by decide) (by decide),entry.heap]
  have wout : w.getReg .x8=4294971392 := by
    change (writeBits _ _ _).getReg .x8=_
    rw [CommitGolfCandidate.writeBits_register,root_node_keep tops .x8 (by decide) (by decide),entry.out]
  have frame : ∀ word, heapWord 1+25≤word → word<2^33 → memoryView w word=memoryView tops word := by
    intro word lo hi
    change memoryView (writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply) word=_
    refine (permutation_write_memory (rootNode tops 4) (heapWord 1) word reply (by decide) hi).trans ?_
    unfold writeWindow
    rw [dif_neg (by omega)]
    exact congrArg (fun m => m (wordAddress word)) (root_node_mem tops)
  have inp : packBuffer (window (memoryView tops) (pentaGroupWord 10 0))=pentaInput (fun t => nodes 10 (5*0+t.val)) := by
    rw [←read_permutation_window]
    exact node_input tops nodes tapeSalts 10 0 (by decide) (by decide) tree
  have rv : reply=oracle.permutation (pentaInput (fun t => nodes 10 (5*0+t.val))) := congrArg oracle.permutation inp
  have value : nodes 11 0=(oracle.permutation (pentaInput (fun t => nodes 10 (5*0+t.val)))).extractLsb' 0 256 :=
    v.value 10 0 (by decide)
  have rootValue : nodeDigest w 1=nodes 11 0 := by
    unfold nodeDigest
    rw [show treeWord 1=heapWord 1 from rfl]
    have written := write_bits_digest (bits := 1600) (rootNode tops 4) (8*heapWord 1) 0 reply (by decide) (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at written
    apply written.trans
    rw [value,rv]
    rfl
  have final : result.state=rootPrefix w 10 := state
  simp only [Submission.readCommit,final]
  refine ⟨?_,?_,?_⟩
  · exact (root_copy_output w wheap wout).trans rootValue
  · intro k j hk hj
    have groupIn : j/5<pentaCount (k+1) := by omega
    have below := group_below_salts k (j/5) (by unfold PENTA_LEVELS at hk;omega) groupIn 0
    have slotEnd := slot_write_end k j
    have e : pentaGroupWord k (j/5+1)=pentaGroupWord k (j/5)+46 := by unfold pentaGroupWord;omega
    have addr := penta_slot_byte_address k j (by unfold PENTA_LEVELS at hk;omega)
    have low := trapdoor_below_levels k (j/5) (by unfold PENTA_LEVELS at hk;omega)
    have start := slot_after_zero_prefix k j
    unfold pentaTrapdoorNode
    have slice := read_buffer_slice (rootPrefix w 10) 4294971424 (submission opening checker).sizes.trapdoor
      (pentaSlotOffset k j) 32 (by change pentaSlotOffset k j+32≤2080378880;unfold saltWord at below;omega)
    rw [←addr] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer w wout _ 32 (by omega) (by unfold saltWord at below;omega) (by decide)]
    apply aligned_buffer_eq w _ 32 (by decide)
    intro t ht
    rw [frame _ (by unfold heapWord;omega) (by unfold saltWord at below;omega)]
    exact tree.node k j (by unfold PENTA_LEVELS at hk;omega) hj ⟨t,ht⟩
  · intro i
    have hi : i.val<2^24 := i.isLt
    unfold quadTrapdoorSalt
    have slice := read_buffer_slice (rootPrefix w 10) 4294971424 (submission opening checker).sizes.trapdoor
      (QUAD_SALT_BASE+16*i.val) 16 (by change 1811943424+16*i.val+16≤2080378880;omega)
    rw [show 4294971424+(QUAD_SALT_BASE+16*i.val)=8*saltWord i.val by unfold QUAD_SALT_BASE saltWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer w wout _ 16 (by unfold saltWord;omega) (by unfold saltWord;omega) (by decide)]
    apply aligned_buffer_eq w _ 16 (by decide)
    intro t ht
    rw [frame _ (by unfold heapWord saltWord;omega) (by unfold saltWord;omega)]
    exact tree.nonce i ⟨t,ht⟩

end TwoPermutationPrototype.Quad.Commit
