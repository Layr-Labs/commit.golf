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
attribute [local irreducible] image writeBits checkEvaluation Leaves.groups Quads.groups packedParentGroups
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

theorem parent_initial_content (quads : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (heap : Nat → BitVec 256) (qc : Quads.Content quads digests salts heap (2^22)) :
    Parents.Content (parentSetup quads 9) digests salts heap (2^22-1) := by
  refine ⟨retained_same_mem quads (parentSetup quads 9) digests salts qc.toRetained rfl,?_⟩
  intro n lo hi
  have lower : 2^22≤n := by omega
  have atNode := qc.nodes (n-2^22) (by omega)
  rw [show 2^22+(n-2^22)=n by omega] at atNode
  unfold nodeDigest
  rw [CommitGolfCandidate.read_buffer_memory_congr _ quads
    (show (parentSetup quads 9).mem=quads.mem from rfl)]
  rw [show treeWord n=heapWord n by unfold treeWord heapWord;omega]
  exact atNode

theorem parent_phase_content (oracle : Oracle) (quads : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (heap : Nat → BitVec 256)
    (qc : Quads.Content quads digests salts heap (2^22))
    (qheap : quads.getReg .x9=4294971424) (qout : quads.getReg .x8=4294971392)
    (selector : quads.getReg .x5=0) (qpc : quads.pc=381560)
    (tree : ∀ j, 0<j → j<2^22 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j)))) :
    let parents := (checkEvaluation oracle (packedParentGroups 381596 15709 267 (parentSetup quads 9))).1
    Parents.Content parents digests salts heap 0 ∧ parents.getReg .x9=4294971424 ∧
      parents.getReg .x8=4294971392 := by
  let pstart := parentSetup quads 9
  let parents := (checkEvaluation oracle (packedParentGroups 381596 15709 267 pstart)).1
  change Parents.Content parents digests salts heap 0 ∧ parents.getReg .x9=4294971424 ∧ parents.getReg .x8=4294971392
  have pr := parent_setup_regs quads qheap selector
  have pc := parent_initial_content quads digests salts heap qc
  have done := Parents.groups_content oracle 381596 15709 267 pstart heap digests salts (by decide) tree pc pr.1
  have term := packed_groups_post 381596 15709 267 pstart (by decide)
    (fun _ => parent_setup_pc quads qpc) pr.1
    (check_evaluation_support oracle (packedParentGroups 381596 15709 267 pstart))
  have keep := Parents.groups_keeps pstart 381596 15709 267 .x8 (by decide) (by decide)
    (check_evaluation_support oracle (packedParentGroups 381596 15709 267 pstart))
  exact ⟨done,term.1.heap,keep.trans qout⟩

theorem quad_complete_content (oracle : Oracle) (start : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (heap : Nat → BitVec 256)
    (quad : ∀ h < 2^22, heap (2^22+h)=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (initial : Quads.Content start digests salts heap 0) :
    Quads.Content (checkEvaluation oracle (Quads.groups 256 0 start)).1 digests salts heap (2^22) := by
  have qc := Quads.groups_content oracle start 256 0 (by decide) digests salts heap quad initial
  rw [show 0+16384*256=2^22 by decide] at qc
  exact qc

theorem quads_finished (leaves : MachineState) (fin : LeavesFinished leaves) (out : MachineState)
    (hit : out ∈ support (Quads.groups 256 0 (quadSetup leaves 9))) :
    out.pc=381560 ∧ out.getReg .x5=0 ∧ out.getReg .x9=4294971424 ∧ out.getReg .x8=4294971392 := by
  have qregs := quad_setup_regs leaves fin.heap fin.selector fin.size fin.kind
  obtain ⟨qr,qpc,keep⟩ := Quads.groups_post (quadSetup leaves 9) 256 0 (by decide) qregs.1
    (fun _ => quad_setup_pc leaves fin.pc) hit
  exact ⟨qpc (by decide),qr.selector,(keep .x9 (by decide) (by decide)).trans fin.heap,
    (keep .x8 (by decide) (by decide)).trans fin.output⟩

theorem tree_content (oracle : Oracle) (leaves : MachineState) (fin : LeavesFinished leaves)
    (digests : DigestTape) (salts : CompleteSaltTape) (heap : Nat → BitVec 256)
    (retained : Retained leaves digests salts)
    (quad : ∀ h < 2^22, heap (2^22+h)=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (tree : ∀ j, 0<j → j<2^22 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j)))) :
    let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
    let parents := (checkEvaluation oracle (packedParentGroups 381596 15709 267 (parentSetup quads 9))).1
    Parents.Content parents digests salts heap 0 ∧ parents.getReg .x9=4294971424 ∧
      parents.getReg .x8=4294971392 := by
  let qstart := quadSetup leaves 9
  let quads := (checkEvaluation oracle (Quads.groups 256 0 qstart)).1
  let pstart := parentSetup quads 9
  let parents := (checkEvaluation oracle (packedParentGroups 381596 15709 267 pstart)).1
  change Parents.Content parents digests salts heap 0 ∧ parents.getReg .x9=4294971424 ∧ parents.getReg .x8=4294971392
  have initial : Quads.Content qstart digests salts heap 0 :=
    ⟨retained_same_mem leaves qstart digests salts retained rfl,fun _ impossible => False.elim (by omega)⟩
  have qc := quad_complete_content oracle qstart digests salts heap quad initial
  obtain ⟨qpc,selector,qheap,qout⟩ := quads_finished leaves fin quads
    (check_evaluation_support oracle (Quads.groups 256 0 qstart))
  exact parent_phase_content oracle quads digests salts heap qc qheap qout selector qpc tree

private theorem eval_three (oracle : Oracle) (p : OracleComp World MachineState)
    (q r : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (do let a ← p; let b ← q a; let c ← r b; return finish c)).1 =
      finish (checkEvaluation oracle (r (checkEvaluation oracle (q (checkEvaluation oracle p).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

theorem body_evaluated (oracle : Oracle) (ready : MachineState) :
    let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
    let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
    let parents := (checkEvaluation oracle (packedParentGroups 381596 15709 267 (parentSetup quads 9))).1
    (checkEvaluation oracle (body ready)).1=rootPrefix parents 10 := by
  have code : body ready = (do
      let leaves ← Leaves.groups 4096 0 ready
      let quads ← Quads.groups 256 0 (quadSetup leaves 9)
      let parents ← packedParentGroups 381596 15709 267 (parentSetup quads 9)
      return rootPrefix parents 10) := by unfold body;rfl
  rw [code]
  exact eval_three oracle (Leaves.groups 4096 0 ready)
    (fun leaves => Quads.groups 256 0 (quadSetup leaves 9))
    (fun quads => packedParentGroups 381596 15709 267 (parentSetup quads 9)) (fun parents => rootPrefix parents 10)

/-- The final machine state of the tree phase under a fixed oracle. -/
def finalState (oracle : Oracle) (ready : MachineState) : MachineState :=
  let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
  let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
  let parents := (checkEvaluation oracle (packedParentGroups 381596 15709 267 (parentSetup quads 9))).1
  rootPrefix parents 10

theorem serialized_results (opening checker : Image) (parents : MachineState) (heap : Nat → BitVec 256)
    (digests : DigestTape) (salts : CompleteSaltTape) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : Parents.Content parents digests salts heap 0) :
    let output := (submission opening checker).readCommit result
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2^23 → quadTrapdoorHeap output.2 n=heap n) ∧
    (∀ i : Index, quadTrapdoorLeaf output.2 i=digests i) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=salts i) := by
  simp only [Submission.readCommit,state]
  constructor
  · exact (root_copy_output parents heapReg outReg).trans (content.nodes 1 (by decide) (by decide))
  constructor
  · intro n pos small
    unfold quadTrapdoorHeap
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (32*n) 32 (by change 32*n+32≤2080378880;omega)
    rw [show 8*(32*n)=256*n by omega,show 4294971424+32*n=8*treeWord n by unfold treeWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold treeWord;omega) (by unfold treeWord;omega) (by decide)]
    exact content.nodes n pos small
  constructor
  · intro i
    have hi : i.val<2^24 := i.isLt
    unfold quadTrapdoorLeaf
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (quadSlotOffset i.val) 32 (by change quadSlotOffset i.val+32≤2080378880;unfold quadSlotOffset QUAD_GROUP_BASE;omega)
    rw [←leaf_byte_address] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold leafWord groupWord;omega)
      (by unfold leafWord groupWord;omega) (by decide)]
    exact retained_leaf_buffer parents digests salts content.toRetained i
  · intro i
    have hi : i.val<2^24 := i.isLt
    unfold quadTrapdoorSalt
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (QUAD_SALT_BASE+16*i.val) 16 (by change 1811943424+16*i.val+16≤2080378880;omega)
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
    (result : Execution) (state : result.state=finalState oracle ready) :
    let output := (submission opening checker).readCommit result
    output.1=quadPublicTree oracle message salts 1 ∧
    (∀ n, 0<n → n<2^23 → quadTrapdoorHeap output.2 n=quadPublicTree oracle message salts n) ∧
    (∀ i : Index, quadTrapdoorLeaf output.2 i=quadPublicLeaves oracle message salts i) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=salts i) := by
  let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
  let digests := quadPublicLeaves oracle message salts
  let heap := quadPublicTree oracle message salts
  have fin := leaves_finished ready r (check_evaluation_support oracle (Leaves.groups 4096 0 ready))
  have retained := ready_leaf_retained oracle ready r message salts messages nonces zeros
  have quad (h : Nat) (bound : h<2^22) : heap (2^22+h)=quadFunction oracle.permutation (quadGroupLeaves digests h) :=
    quad_heap_node oracle.compression (quadFunction oracle.permutation) digests h bound
  have tree (j : Nat) (pos : 0<j) (bound : j<2^22) :
      heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))) :=
    quad_heap_parent oracle.compression (quadFunction oracle.permutation) digests j pos bound
  obtain ⟨content,heapReg,outReg⟩ := tree_content oracle leaves fin digests _ heap retained quad tree
  exact serialized_results opening checker _ heap digests _ _ state heapReg outReg content

end TwoPermutationPrototype.Quad.Commit
