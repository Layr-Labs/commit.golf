import CommitGolfCandidate.QuadCommitExecution
import CommitGolfCandidate.QuadCommitLeafData
import CommitGolfCandidate.QuadCommitParentMeaning
import CommitGolfCandidate.TwoPermutationRootBytes

namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support
  read_buffer_slice splitBlocks)
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
attribute [local irreducible] image writeBits checkEvaluation Leaves.groups Quads.groups Quad2s.groups packedParentGroups
  body rootPrefix readBuffer

structure LeavesFinished (s : MachineState) : Prop where
  pc : s.pc=184908
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  kind : s.getReg .x13=1
  heap : s.getReg .x9=4294971424
  output : s.getReg .x8=4294971392

theorem leaves_finished (ready : MachineState) (r : ReadyRegs ready)
    {leaves : MachineState} (hit : leaves ∈ support (Leaves.groups 4096 0 ready)) :
    LeavesFinished leaves := by
  have rs := r.regs
  obtain ⟨pc,keep⟩ := Leaves.groups_post _ 4096 0 (by decide) rs (by decide) hit
  exact ⟨pc,(keep .x5 (by simp [Leaves.SavedReg])).trans rs.selector,
    (keep .x11 (by simp [Leaves.SavedReg])).trans rs.size,
    (keep .x13 (by simp [Leaves.SavedReg])).trans rs.primitive,
    (keep .x9 (by simp [Leaves.SavedReg])).trans r.heap,
    (keep .x8 (by simp [Leaves.SavedReg])).trans r.out⟩

theorem parent_initial_content (quad2s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads heap : Nat → BitVec 256) (qc : Quad2s.Content quad2s digests salts quads heap (2^20)) :
    Parents.Content (parentSetup quad2s 9) digests salts quads heap (2^20-1) := by
  refine ⟨retained2_same_mem quad2s (parentSetup quad2s 9) digests salts quads qc.toRetained2 rfl,?_⟩
  intro n lo hi
  have lower : 2^20≤n := by omega
  have atNode := qc.nodes (n-2^20) (by omega)
  rw [show 2^20+(n-2^20)=n by omega] at atNode
  unfold nodeDigest
  rw [CommitGolfCandidate.read_buffer_memory_congr _ quad2s
    (show (parentSetup quad2s 9).mem=quad2s.mem from rfl)]
  rw [show treeWord n=heapWord n by unfold treeWord heapWord;omega]
  exact atNode

theorem parent_phase_content (oracle : Oracle) (quad2s : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads heap : Nat → BitVec 256)
    (qc : Quad2s.Content quad2s digests salts quads heap (2^20))
    (qheap : quad2s.getReg .x9=4294971424) (qout : quad2s.getReg .x8=4294971392)
    (selector : quad2s.getReg .x5=0) (qpc : quad2s.pc=578212)
    (tree : ∀ j, 0<j → j<2^20 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j)))) :
    let parents := (checkEvaluation oracle (packedParentGroups 578248 13981 75 (parentSetup quad2s 9))).1
    Parents.Content parents digests salts quads heap 0 ∧ parents.getReg .x9=4294971424 ∧
      parents.getReg .x8=4294971392 := by
  let pstart := parentSetup quad2s 9
  let parents := (checkEvaluation oracle (packedParentGroups 578248 13981 75 pstart)).1
  change Parents.Content parents digests salts quads heap 0 ∧ parents.getReg .x9=4294971424 ∧ parents.getReg .x8=4294971392
  have pr := parent_setup_regs quad2s qheap selector
  have pc := parent_initial_content quad2s digests salts quads heap qc
  have done := Parents.groups_content oracle 578248 13981 75 pstart quads heap digests salts (by decide) tree pc pr.1
  have term := packed_groups_post 578248 13981 75 pstart (by decide)
    (fun _ => parent_setup_pc quad2s qpc) pr.1
    (check_evaluation_support oracle (packedParentGroups 578248 13981 75 pstart))
  have keep := Parents.groups_keeps pstart 578248 13981 75 .x8 (by decide) (by decide)
    (check_evaluation_support oracle (packedParentGroups 578248 13981 75 pstart))
  exact ⟨done,term.1.heap,keep.trans qout⟩

theorem quad_complete_content (oracle : Oracle) (start : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads : Nat → BitVec 256)
    (quad : ∀ h < 2^22, quads h=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (initial : Quads.Content start digests salts quads 0) :
    Retained2 (checkEvaluation oracle (Quads.groups 256 0 start)).1 digests salts quads := by
  have qc := Quads.groups_content oracle start 256 0 (by decide) digests salts quads quad initial
  rw [show 0+16384*256=2^22 by decide] at qc
  exact ⟨qc.toRetained,qc.nodes⟩

theorem quad2_complete_content (oracle : Oracle) (start : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads heap : Nat → BitVec 256)
    (quad : ∀ h < 2^20, heap (2^20+h)=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (initial : Quad2s.Content start digests salts quads heap 0) :
    Quad2s.Content (checkEvaluation oracle (Quad2s.groups 64 0 start)).1 digests salts quads heap (2^20) := by
  have qc := Quad2s.groups_content oracle start 64 0 (by decide) digests salts quads heap quad initial
  rw [show 0+16384*64=2^20 by decide] at qc
  exact qc

theorem quads_finished (leaves : MachineState) (fin : LeavesFinished leaves) (out : MachineState)
    (hit : out ∈ support (Quads.groups 256 0 (quadSetup leaves 9))) :
    out.pc=381560 ∧ out.getReg .x5=0 ∧ out.getReg .x11=200 ∧ out.getReg .x13=1 ∧
      out.getReg .x9=4294971424 ∧ out.getReg .x8=4294971392 := by
  have qregs := quad_setup_regs leaves fin.heap fin.selector fin.size fin.kind
  obtain ⟨qr,qpc,keep⟩ := Quads.groups_post (quadSetup leaves 9) 256 0 (by decide) qregs.1
    (fun _ => quad_setup_pc leaves fin.pc) hit
  exact ⟨qpc (by decide),qr.selector,qr.size,qr.primitive,(keep .x9 (by decide) (by decide)).trans fin.heap,
    (keep .x8 (by decide) (by decide)).trans fin.output⟩

theorem quad2s_finished (quads : MachineState) (pc : quads.pc=381560) (selector : quads.getReg .x5=0)
    (size : quads.getReg .x11=200) (kind : quads.getReg .x13=1)
    (heap : quads.getReg .x9=4294971424) (output : quads.getReg .x8=4294971392) (out : MachineState)
    (hit : out ∈ support (Quad2s.groups 64 0 (quad2Setup quads 9))) :
    out.pc=578212 ∧ out.getReg .x5=0 ∧ out.getReg .x9=4294971424 ∧ out.getReg .x8=4294971392 := by
  have qregs := quad2_setup_regs quads heap selector size kind
  obtain ⟨qr,qpc,keep⟩ := Quad2s.groups_post (quad2Setup quads 9) 64 0 (by decide) qregs.1
    (fun _ => quad2_setup_pc quads pc) hit
  exact ⟨qpc (by decide),qr.selector,(keep .x9 (by decide) (by decide)).trans heap,
    (keep .x8 (by decide) (by decide)).trans output⟩

theorem quad2_setup_mem (s : MachineState) : (quad2Setup s 9).mem=s.mem := rfl
theorem quad_setup_mem (s : MachineState) : (quadSetup s 9).mem=s.mem := rfl

theorem tree_content (oracle : Oracle) (leaves : MachineState) (fin : LeavesFinished leaves)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads heap : Nat → BitVec 256)
    (retained : Retained leaves digests salts)
    (quad : ∀ h < 2^22, quads h=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (quad2 : ∀ h < 2^20, heap (2^20+h)=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (tree : ∀ j, 0<j → j<2^20 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j)))) :
    let quadState := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
    let quad2State := (checkEvaluation oracle (Quad2s.groups 64 0 (quad2Setup quadState 9))).1
    let parents := (checkEvaluation oracle (packedParentGroups 578248 13981 75 (parentSetup quad2State 9))).1
    Parents.Content parents digests salts quads heap 0 ∧ parents.getReg .x9=4294971424 ∧
      parents.getReg .x8=4294971392 := by
  let qstart := quadSetup leaves 9
  let quadState := (checkEvaluation oracle (Quads.groups 256 0 qstart)).1
  let q2start := quad2Setup quadState 9
  let quad2State := (checkEvaluation oracle (Quad2s.groups 64 0 q2start)).1
  let pstart := parentSetup quad2State 9
  let parents := (checkEvaluation oracle (packedParentGroups 578248 13981 75 pstart)).1
  change Parents.Content parents digests salts quads heap 0 ∧ parents.getReg .x9=4294971424 ∧ parents.getReg .x8=4294971392
  have initial : Quads.Content qstart digests salts quads 0 :=
    ⟨retained_same_mem leaves qstart digests salts retained (quad_setup_mem leaves),fun _ impossible => False.elim (by omega)⟩
  have qc := quad_complete_content oracle qstart digests salts quads quad initial
  obtain ⟨qpc,selector,size,kind,qheap,qout⟩ := quads_finished leaves fin quadState
    (check_evaluation_support oracle (Quads.groups 256 0 qstart))
  have initial2 : Quad2s.Content q2start digests salts quads heap 0 :=
    ⟨retained2_same_mem quadState q2start digests salts quads qc (quad2_setup_mem quadState),fun _ impossible => False.elim (by omega)⟩
  have q2c := quad2_complete_content oracle q2start digests salts quads heap quad2 initial2
  obtain ⟨q2pc,selector2,q2heap,q2out⟩ := quad2s_finished quadState qpc selector size kind qheap qout quad2State
    (check_evaluation_support oracle (Quad2s.groups 64 0 q2start))
  exact parent_phase_content oracle quad2State digests salts quads heap q2c q2heap q2out selector2 q2pc tree

private theorem eval_four (oracle : Oracle) (p : OracleComp World MachineState)
    (q r t : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (do let a ← p; let b ← q a; let c ← r b; let d ← t c; return finish d)).1 =
      finish (checkEvaluation oracle (t (checkEvaluation oracle (r (checkEvaluation oracle (q (checkEvaluation oracle p).1)).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

theorem body_evaluated (oracle : Oracle) (ready : MachineState) :
    let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
    let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
    let quad2s := (checkEvaluation oracle (Quad2s.groups 64 0 (quad2Setup quads 9))).1
    let parents := (checkEvaluation oracle (packedParentGroups 578248 13981 75 (parentSetup quad2s 9))).1
    (checkEvaluation oracle (body ready)).1=rootPrefix parents 10 := by
  have code : body ready = (do
      let leaves ← Leaves.groups 4096 0 ready
      let quads ← Quads.groups 256 0 (quadSetup leaves 9)
      let quad2s ← Quad2s.groups 64 0 (quad2Setup quads 9)
      let parents ← packedParentGroups 578248 13981 75 (parentSetup quad2s 9)
      return rootPrefix parents 10) := by unfold body;rfl
  rw [code]
  exact eval_four oracle (Leaves.groups 4096 0 ready)
    (fun leaves => Quads.groups 256 0 (quadSetup leaves 9))
    (fun quads => Quad2s.groups 64 0 (quad2Setup quads 9))
    (fun quad2s => packedParentGroups 578248 13981 75 (parentSetup quad2s 9)) (fun parents => rootPrefix parents 10)

/-- The final machine state of the tree phase under a fixed oracle. -/
def finalState (oracle : Oracle) (ready : MachineState) : MachineState :=
  let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
  let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
  let quad2s := (checkEvaluation oracle (Quad2s.groups 64 0 (quad2Setup quads 9))).1
  let parents := (checkEvaluation oracle (packedParentGroups 578248 13981 75 (parentSetup quad2s 9))).1
  rootPrefix parents 10

theorem serialized_results (opening checker : Image) (parents : MachineState) (quads heap : Nat → BitVec 256)
    (digests : DigestTape) (salts : CompleteSaltTape) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : Parents.Content parents digests salts quads heap 0) :
    let output := (submission opening checker).readCommit result
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2^21 → quadTrapdoorHeap output.2 n=heap n) ∧
    (∀ g, g<2^22 → quad2TrapdoorQuad output.2 g=quads g) ∧
    (∀ i : Index, quadTrapdoorLeaf output.2 i=digests i) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=salts i) := by
  simp only [Submission.readCommit,state]
  constructor
  · exact (root_copy_output parents heapReg outReg).trans (content.nodes 1 (by decide) (by decide))
  constructor
  · intro n pos small
    unfold quadTrapdoorHeap
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (32*n) 32 (by change 32*n+32≤2466267136;omega)
    rw [show 8*(32*n)=256*n by omega,show 4294971424+32*n=8*treeWord n by unfold treeWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold treeWord;omega) (by unfold treeWord;omega) (by decide)]
    exact content.nodes n pos small
  constructor
  · intro g hg
    unfold quad2TrapdoorQuad
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (quad2SlotOffset g) 32 (by change quad2SlotOffset g+32≤2466267136;unfold quad2SlotOffset QUAD2_GROUP_BASE QUAD_SALT_BASE;rw [length_value];omega)
    rw [←quad_slot_byte_address] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold quadSlotWord quad2GroupWord;omega)
      (by unfold quadSlotWord quad2GroupWord;omega) (by decide)]
    exact retained2_quad_buffer parents digests salts quads content.toRetained2 g hg
  constructor
  · intro i
    have hi : i.val<2^24 := i.isLt
    unfold quadTrapdoorLeaf
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (quadSlotOffset i.val) 32 (by change quadSlotOffset i.val+32≤2466267136;unfold quadSlotOffset QUAD_GROUP_BASE;omega)
    rw [←leaf_byte_address] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold leafWord groupWord;omega)
      (by unfold leafWord groupWord;omega) (by decide)]
    exact retained_leaf_buffer parents digests salts content.toRetained i
  · intro i
    have hi : i.val<2^24 := i.isLt
    unfold quadTrapdoorSalt
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (QUAD_SALT_BASE+16*i.val) 16 (by change 1811943424+16*i.val+16≤2466267136;omega)
    rw [show 4294971424+(QUAD_SALT_BASE+16*i.val)=8*saltWord i.val by unfold QUAD_SALT_BASE saltWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 16 (by unfold saltWord;omega) (by unfold saltWord;omega) (by decide)]
    exact retained_salt_buffer parents digests salts content.toRetained i

/-- Everything serialized by the commit, for ANY leaf-entry state whose memory holds the
message windows, an arbitrary salt tape and the zero group prefixes. -/
theorem physical_results (opening checker : Image) (oracle : Oracle) (message : Message)
    (salts : CompleteSaltTape) (ready : MachineState) (r : ReadyRegs ready)
    (messages : ∀ i : Index, window (memoryView ready) (leafStart i.val+5) = messageWords message i)
    (nonces : ∀ i : Index, window (memoryView ready) (Leaves.leafSalt i.val) = saltWords (salts i))
    (zeros : ∀ g < 2^22, ∀ k : Fin 9, memoryView ready (groupWord g+k.val)=0)
    (quadZeros : ∀ h < 2^20, ∀ k : Fin 9, memoryView ready (quad2GroupWord h+k.val)=0)
    (result : Execution) (state : result.state=finalState oracle ready) :
    let output := (submission opening checker).readCommit result
    output.1=quad2PublicTree oracle message salts 1 ∧
    (∀ n, 0<n → n<2^21 → quadTrapdoorHeap output.2 n=quad2PublicTree oracle message salts n) ∧
    (∀ g, g<2^22 → quad2TrapdoorQuad output.2 g=quad2PublicQuads oracle message salts g) ∧
    (∀ i : Index, quadTrapdoorLeaf output.2 i=quadPublicLeaves oracle message salts i) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=salts i) := by
  let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
  let digests := quadPublicLeaves oracle message salts
  let quads := quad2PublicQuads oracle message salts
  let heap := quad2PublicTree oracle message salts
  have fin := leaves_finished ready r (check_evaluation_support oracle (Leaves.groups 4096 0 ready))
  have retained := ready_leaf_retained oracle ready r message salts messages nonces zeros quadZeros
  have quad (h : Nat) (bound : h<2^22) : quads h=quadFunction oracle.permutation (quadGroupLeaves digests h) := rfl
  have quad2 (h : Nat) (bound : h<2^20) :
      heap (2^20+h)=quadFunction oracle.permutation (fun k => quads (4*h+k.val)) :=
    quad2_heap_node oracle.compression (quadFunction oracle.permutation) digests h bound
  have tree (j : Nat) (pos : 0<j) (bound : j<2^20) :
      heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))) :=
    quad2_heap_parent oracle.compression (quadFunction oracle.permutation) digests j pos bound
  obtain ⟨content,heapReg,outReg⟩ := tree_content oracle leaves fin digests _ quads heap retained quad quad2 tree
  exact serialized_results opening checker _ quads heap digests _ _ state heapReg outReg content

end TwoPermutationPrototype.Quad.Commit
