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
attribute [local irreducible] image writeBits checkEvaluation Leaves.groups Quads.groups Quad2s.groups Quad3s.groups packedParentGroups
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

theorem quad_setup_mem (s : MachineState) : (quadSetup s 9).mem=s.mem := rfl
theorem quad2_setup_mem (s : MachineState) : (quad2Setup s 9).mem=s.mem := rfl
theorem quad3_setup_mem (s : MachineState) : (quad3Setup s 9).mem=s.mem := rfl
theorem parent_setup_mem (s : MachineState) : (parentSetup s 9).mem=s.mem := rfl

theorem parent_initial_content (quad3s : MachineState) (digests : DigestTape) (salts : CompleteSaltTape)
    (quads quad2s heap : Nat → BitVec 256) (qc : Quad3s.Content quad3s digests salts quads quad2s heap (2^18)) :
    Parents.Content (parentSetup quad3s 9) digests salts quads quad2s heap (2^18-1) := by
  refine ⟨retained3_same_mem quad3s (parentSetup quad3s 9) digests salts quads quad2s qc.toRetained3
    (parent_setup_mem quad3s),?_⟩
  intro n lo hi
  have lower : 2^18≤n := by omega
  have atNode := qc.nodes (n-2^18) (by omega)
  rw [show 2^18+(n-2^18)=n by omega] at atNode
  unfold nodeDigest
  rw [CommitGolfCandidate.read_buffer_memory_congr _ quad3s (parent_setup_mem quad3s)]
  rw [show treeWord n=heapWord n by unfold treeWord heapWord;omega]
  exact atNode

theorem parent_phase_content (oracle : Oracle) (quad3s : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s heap : Nat → BitVec 256)
    (qc : Quad3s.Content quad3s digests salts quads quad2s heap (2^18))
    (qheap : quad3s.getReg .x9=4294971424) (qout : quad3s.getReg .x8=4294971392)
    (selector : quad3s.getReg .x5=0) (qpc : quad3s.pc=774864)
    (tree : ∀ j, 0<j → j<2^18 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j)))) :
    let parents := (checkEvaluation oracle (packedParentGroups 774900 13797 19 (parentSetup quad3s 9))).1
    Parents.Content parents digests salts quads quad2s heap 0 ∧ parents.getReg .x9=4294971424 ∧
      parents.getReg .x8=4294971392 := by
  let pstart := parentSetup quad3s 9
  let parents := (checkEvaluation oracle (packedParentGroups 774900 13797 19 pstart)).1
  change Parents.Content parents digests salts quads quad2s heap 0 ∧ parents.getReg .x9=4294971424 ∧ parents.getReg .x8=4294971392
  have pr := parent_setup_regs quad3s qheap selector
  have pc := parent_initial_content quad3s digests salts quads quad2s heap qc
  have done := Parents.groups_content oracle 774900 13797 19 pstart quads quad2s heap digests salts (by decide) tree pc pr.1
  have term := packed_groups_post 774900 13797 19 pstart (by decide)
    (fun _ => parent_setup_pc quad3s qpc) pr.1
    (check_evaluation_support oracle (packedParentGroups 774900 13797 19 pstart))
  have keep := Parents.groups_keeps pstart 774900 13797 19 .x8 (by decide) (by decide)
    (check_evaluation_support oracle (packedParentGroups 774900 13797 19 pstart))
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
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s : Nat → BitVec 256)
    (quad : ∀ h < 2^20, quad2s h=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (initial : Quad2s.Content start digests salts quads quad2s 0) :
    Retained3 (checkEvaluation oracle (Quad2s.groups 64 0 start)).1 digests salts quads quad2s := by
  have qc := Quad2s.groups_content oracle start 64 0 (by decide) digests salts quads quad2s quad initial
  rw [show 0+16384*64=2^20 by decide] at qc
  exact ⟨qc.toRetained2,qc.nodes⟩

theorem quad3_complete_content (oracle : Oracle) (start : MachineState)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s heap : Nat → BitVec 256)
    (quad : ∀ m < 2^18, heap (2^18+m)=quadFunction oracle.permutation (fun k => quad2s (4*m+k.val)))
    (initial : Quad3s.Content start digests salts quads quad2s heap 0) :
    Quad3s.Content (checkEvaluation oracle (Quad3s.groups 16 0 start)).1 digests salts quads quad2s heap (2^18) := by
  have qc := Quad3s.groups_content oracle start 16 0 (by decide) digests salts quads quad2s heap quad initial
  rw [show 0+16384*16=2^18 by decide] at qc
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
    out.pc=578212 ∧ out.getReg .x5=0 ∧ out.getReg .x11=200 ∧ out.getReg .x13=1 ∧
      out.getReg .x9=4294971424 ∧ out.getReg .x8=4294971392 := by
  have qregs := quad2_setup_regs quads heap selector size kind
  obtain ⟨qr,qpc,keep⟩ := Quad2s.groups_post (quad2Setup quads 9) 64 0 (by decide) qregs.1
    (fun _ => quad2_setup_pc quads pc) hit
  exact ⟨qpc (by decide),qr.selector,qr.size,qr.primitive,(keep .x9 (by decide) (by decide)).trans heap,
    (keep .x8 (by decide) (by decide)).trans output⟩

theorem quad3s_finished (quad2s : MachineState) (pc : quad2s.pc=578212) (selector : quad2s.getReg .x5=0)
    (size : quad2s.getReg .x11=200) (kind : quad2s.getReg .x13=1)
    (heap : quad2s.getReg .x9=4294971424) (output : quad2s.getReg .x8=4294971392) (out : MachineState)
    (hit : out ∈ support (Quad3s.groups 16 0 (quad3Setup quad2s 9))) :
    out.pc=774864 ∧ out.getReg .x5=0 ∧ out.getReg .x9=4294971424 ∧ out.getReg .x8=4294971392 := by
  have qregs := quad3_setup_regs quad2s heap selector size kind
  obtain ⟨qr,qpc,keep⟩ := Quad3s.groups_post (quad3Setup quad2s 9) 16 0 (by decide) qregs.1
    (fun _ => quad3_setup_pc quad2s pc) hit
  exact ⟨qpc (by decide),qr.selector,(keep .x9 (by decide) (by decide)).trans heap,
    (keep .x8 (by decide) (by decide)).trans output⟩

theorem tree_content (oracle : Oracle) (leaves : MachineState) (fin : LeavesFinished leaves)
    (digests : DigestTape) (salts : CompleteSaltTape) (quads quad2s heap : Nat → BitVec 256)
    (retained : Retained leaves digests salts)
    (quad : ∀ h < 2^22, quads h=quadFunction oracle.permutation (quadGroupLeaves digests h))
    (quad2 : ∀ h < 2^20, quad2s h=quadFunction oracle.permutation (fun k => quads (4*h+k.val)))
    (quad3 : ∀ m < 2^18, heap (2^18+m)=quadFunction oracle.permutation (fun k => quad2s (4*m+k.val)))
    (tree : ∀ j, 0<j → j<2^18 → heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j)))) :
    let quadState := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
    let quad2State := (checkEvaluation oracle (Quad2s.groups 64 0 (quad2Setup quadState 9))).1
    let quad3State := (checkEvaluation oracle (Quad3s.groups 16 0 (quad3Setup quad2State 9))).1
    let parents := (checkEvaluation oracle (packedParentGroups 774900 13797 19 (parentSetup quad3State 9))).1
    Parents.Content parents digests salts quads quad2s heap 0 ∧ parents.getReg .x9=4294971424 ∧
      parents.getReg .x8=4294971392 := by
  let qstart := quadSetup leaves 9
  let quadState := (checkEvaluation oracle (Quads.groups 256 0 qstart)).1
  let q2start := quad2Setup quadState 9
  let quad2State := (checkEvaluation oracle (Quad2s.groups 64 0 q2start)).1
  let q3start := quad3Setup quad2State 9
  let quad3State := (checkEvaluation oracle (Quad3s.groups 16 0 q3start)).1
  let pstart := parentSetup quad3State 9
  let parents := (checkEvaluation oracle (packedParentGroups 774900 13797 19 pstart)).1
  change Parents.Content parents digests salts quads quad2s heap 0 ∧ parents.getReg .x9=4294971424 ∧ parents.getReg .x8=4294971392
  have initial : Quads.Content qstart digests salts quads 0 :=
    ⟨retained_same_mem leaves qstart digests salts retained (quad_setup_mem leaves),fun _ impossible => False.elim (by omega)⟩
  have qc := quad_complete_content oracle qstart digests salts quads quad initial
  obtain ⟨qpc,selector,size,kind,qheap,qout⟩ := quads_finished leaves fin quadState
    (check_evaluation_support oracle (Quads.groups 256 0 qstart))
  have initial2 : Quad2s.Content q2start digests salts quads quad2s 0 :=
    ⟨retained2_same_mem quadState q2start digests salts quads qc (quad2_setup_mem quadState),fun _ impossible => False.elim (by omega)⟩
  have q2c := quad2_complete_content oracle q2start digests salts quads quad2s quad2 initial2
  obtain ⟨q2pc,selector2,size2,kind2,q2heap,q2out⟩ := quad2s_finished quadState qpc selector size kind qheap qout quad2State
    (check_evaluation_support oracle (Quad2s.groups 64 0 q2start))
  have initial3 : Quad3s.Content q3start digests salts quads quad2s heap 0 :=
    ⟨retained3_same_mem quad2State q3start digests salts quads quad2s q2c (quad3_setup_mem quad2State),fun _ impossible => False.elim (by omega)⟩
  have q3c := quad3_complete_content oracle q3start digests salts quads quad2s heap quad3 initial3
  obtain ⟨q3pc,selector3,q3heap,q3out⟩ := quad3s_finished quad2State q2pc selector2 size2 kind2 q2heap q2out quad3State
    (check_evaluation_support oracle (Quad3s.groups 16 0 q3start))
  exact parent_phase_content oracle quad3State digests salts quads quad2s heap q3c q3heap q3out selector3 q3pc tree

private theorem eval_five (oracle : Oracle) (p : OracleComp World MachineState)
    (q r t u : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (do let a ← p; let b ← q a; let c ← r b; let d ← t c; let e ← u d; return finish e)).1 =
      finish (checkEvaluation oracle (u (checkEvaluation oracle (t (checkEvaluation oracle (r (checkEvaluation oracle (q (checkEvaluation oracle p).1)).1)).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

theorem body_evaluated (oracle : Oracle) (ready : MachineState) :
    let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
    let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
    let quad2s := (checkEvaluation oracle (Quad2s.groups 64 0 (quad2Setup quads 9))).1
    let quad3s := (checkEvaluation oracle (Quad3s.groups 16 0 (quad3Setup quad2s 9))).1
    let parents := (checkEvaluation oracle (packedParentGroups 774900 13797 19 (parentSetup quad3s 9))).1
    (checkEvaluation oracle (body ready)).1=rootPrefix parents 10 := by
  have code : body ready = (do
      let leaves ← Leaves.groups 4096 0 ready
      let quads ← Quads.groups 256 0 (quadSetup leaves 9)
      let quad2s ← Quad2s.groups 64 0 (quad2Setup quads 9)
      let quad3s ← Quad3s.groups 16 0 (quad3Setup quad2s 9)
      let parents ← packedParentGroups 774900 13797 19 (parentSetup quad3s 9)
      return rootPrefix parents 10) := by unfold body;rfl
  rw [code]
  exact eval_five oracle (Leaves.groups 4096 0 ready)
    (fun leaves => Quads.groups 256 0 (quadSetup leaves 9))
    (fun quads => Quad2s.groups 64 0 (quad2Setup quads 9))
    (fun quad2s => Quad3s.groups 16 0 (quad3Setup quad2s 9))
    (fun quad3s => packedParentGroups 774900 13797 19 (parentSetup quad3s 9)) (fun parents => rootPrefix parents 10)

/-- The final machine state of the tree phase under a fixed oracle. -/
def finalState (oracle : Oracle) (ready : MachineState) : MachineState :=
  let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
  let quads := (checkEvaluation oracle (Quads.groups 256 0 (quadSetup leaves 9))).1
  let quad2s := (checkEvaluation oracle (Quad2s.groups 64 0 (quad2Setup quads 9))).1
  let quad3s := (checkEvaluation oracle (Quad3s.groups 16 0 (quad3Setup quad2s 9))).1
  let parents := (checkEvaluation oracle (packedParentGroups 774900 13797 19 (parentSetup quad3s 9))).1
  rootPrefix parents 10

theorem serialized_results (opening checker : Image) (parents : MachineState) (quads quad2s heap : Nat → BitVec 256)
    (digests : DigestTape) (salts : CompleteSaltTape) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : Parents.Content parents digests salts quads quad2s heap 0) :
    let output := (submission opening checker).readCommit result
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2^19 → quadTrapdoorHeap output.2 n=heap n) ∧
    (∀ g, g<2^22 → quad2TrapdoorQuad output.2 g=quads g) ∧
    (∀ h, h<2^20 → quad3TrapdoorQuad2 output.2 h=quad2s h) ∧
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
  · intro h hh
    unfold quad3TrapdoorQuad2
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 (submission opening checker).sizes.trapdoor
      (quad3SlotOffset h) 32 (by change quad3SlotOffset h+32≤2466267136;unfold quad3SlotOffset QUAD3_GROUP_BASE;omega)
    rw [←quad3_slot_byte_address] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold quad3SlotWord quad3GroupWord;omega)
      (by unfold quad3SlotWord quad3GroupWord;omega) (by decide)]
    exact retained3_quad2_buffer parents digests salts quads quad2s content.toRetained3 h hh
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
    (quad3Zeros : ∀ m < 2^18, ∀ k : Fin 9, memoryView ready (quad3GroupWord m+k.val)=0)
    (result : Execution) (state : result.state=finalState oracle ready) :
    let output := (submission opening checker).readCommit result
    output.1=quad3PublicTree oracle message salts 1 ∧
    (∀ n, 0<n → n<2^19 → quadTrapdoorHeap output.2 n=quad3PublicTree oracle message salts n) ∧
    (∀ g, g<2^22 → quad2TrapdoorQuad output.2 g=quad2PublicQuads oracle message salts g) ∧
    (∀ h, h<2^20 → quad3TrapdoorQuad2 output.2 h=quad3PublicQuad2s oracle message salts h) ∧
    (∀ i : Index, quadTrapdoorLeaf output.2 i=quadPublicLeaves oracle message salts i) ∧
    (∀ i : Index, quadTrapdoorSalt output.2 i=salts i) := by
  let leaves := (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
  let digests := quadPublicLeaves oracle message salts
  let quads := quad2PublicQuads oracle message salts
  let quad2s := quad3PublicQuad2s oracle message salts
  let heap := quad3PublicTree oracle message salts
  have fin := leaves_finished ready r (check_evaluation_support oracle (Leaves.groups 4096 0 ready))
  have retained := ready_leaf_retained oracle ready r message salts messages nonces zeros quadZeros quad3Zeros
  have quad (h : Nat) (bound : h<2^22) : quads h=quadFunction oracle.permutation (quadGroupLeaves digests h) := rfl
  have quad2 (h : Nat) (bound : h<2^20) :
      quad2s h=quadFunction oracle.permutation (fun k => quads (4*h+k.val)) := rfl
  have quad3 (m : Nat) (bound : m<2^18) :
      heap (2^18+m)=quadFunction oracle.permutation (fun k => quad2s (4*m+k.val)) :=
    quad3_heap_node oracle.compression (quadFunction oracle.permutation) digests m bound
  have tree (j : Nat) (pos : 0<j) (bound : j<2^18) :
      heap j=projectReply (oracle.compression (heap (2*j+1) ++ heap (2*j))) :=
    quad3_heap_parent oracle.compression (quadFunction oracle.permutation) digests j pos bound
  obtain ⟨content,heapReg,outReg⟩ := tree_content oracle leaves fin digests _ quads quad2s heap retained quad quad2 quad3 tree
  exact serialized_results opening checker _ quads quad2s heap digests _ _ state heapReg outReg content

end TwoPermutationPrototype.Quad.Commit
