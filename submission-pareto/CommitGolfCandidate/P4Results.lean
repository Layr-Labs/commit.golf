import CommitGolfCandidate.P4Physical
import CommitGolfCandidate.TwoPermutationPackedCapBytes

/-! The serialized P4 commitment and trapdoor (04680e02's `TwoPermutationPackedMeaning.wide_physical_results`, with
the leaf content taken from the grouped invariant and the key recovered from the first two tape slots). -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
attribute [local irreducible] checkEvaluation FullWidth.parentGroups packedParentGroups rootPrefix

noncomputable def publicHeap (o : Oracle) (m : Message) (k : Key) : Nat → BitVec 256 :=
  mixedTranscriptHeap o.compression (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (salts o.permutation k))

def tapeOf (s : MachineState) (i : Index) : BitVec 128 := nonceBuffer s i.val

theorem leaves_content (o : Oracle) (k : Key) (m : Message) (out : MachineState)
    (good : Good o k m (memoryView out) N) :
    ParentContent (parentSetup out 5) (publicHeap o m k) (tapeOf out) (2^24-1) := by
  constructor
  · intro n lo hi
    have valid : n-LENGTH<LENGTH := by change n<2*2^24 at hi;change n-2^24<2^24;omega
    let i : Index := ⟨n-LENGTH,valid⟩
    have idx : n=LENGTH+i.val := by change n=2^24+(n-2^24);change 2^24-1<n at lo;omega
    rw [idx,publicHeap,mixed_heap_leaf]
    unfold nodeDigest
    rw [read_buffer_memory_congr _ out (show (parentSetup out 5).mem=out.mem from rfl)]
    have addr : treeWord (LENGTH+i.val)=leafDest i.val := by change 516+32*2^24+4*(2^24+i.val)=_;unfold leafDest;omega
    rw [addr]
    apply aligned_buffer_eq out _ 32 (by decide)
    intro kk hk
    have value := congrFun (good.children i i.isLt) (⟨kk,hk⟩ : Fin 4)
    change memoryView out (leafDest i.val+kk)=_ at value
    rw [value]
    rfl
  · intro i
    unfold nonceBuffer tapeOf
    rw [read_buffer_memory_congr _ out (show (parentSetup out 5).mem=out.mem from rfl)]
    rfl

private theorem evaluated_two_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (second : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (do
      let one ← p
      let two ← second one
      pure (finish two))).1 =
      finish (checkEvaluation oracle (second (checkEvaluation oracle p).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

theorem state_mk (e : Exit) (s : MachineState) (c q : Nat) : (Execution.mk e s c q).state=s := rfl

theorem packed_output_state (o : Oracle) (leaves : MachineState) :
    (packedOutput o leaves).state=(checkEvaluation o (postLeaves leaves)).1 := by
  unfold packedOutput
  exact state_mk _ _ _ _

theorem output_state (o : Oracle) (leaves : MachineState) :
    (packedOutput o leaves).state=rootPrefix (checkEvaluation o (packedParentGroups 580040 19065 55
      (checkEvaluation o (FullWidth.parentGroups 186816 32768 1048575 480 (mixedStopSetup (parentSetup leaves 5)))).1)).1 10 := by
  rw [packed_output_state]
  unfold postLeaves
  exact evaluated_two_finish o _ (fun full => packedParentGroups 580040 19065 55 full) (fun parents => rootPrefix parents 10)

private def serializationModel := Assembly.checkerReference commitImage

private theorem codecABI : CommitABI serializationModel where
  code := rfl
  message := rfl
  output := rfl
  trapdoor := rfl
  size := rfl
  fuel := by decide

private theorem serialized (parents : MachineState) (heap : Nat → BitVec 256)
    (tape : Index → BitVec 128) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : ParentContent parents heap tape 0) :
    (actual.readCommit result).1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → (actual.readCommit result).2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, (actual.readCommit result).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=tape i) := by
  have equality : actual.readCommit result = serializationModel.readCommit result := by
    simp only [Submission.readCommit, actual, Artifact.submission, serializationModel, Assembly.checkerReference]
  rw [equality]
  exact serialized_parent_results serializationModel codecABI parents heap tape result state heapReg outReg content

private theorem packed_sequence_keep_output (remaining count : Nat) (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentsTrace remaining count state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction count generalizing state with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (packed_parent_keeps_register state _ answer .x8 (by decide) (by decide))

private theorem packed_groups_keep_output (base : Word) (span groups : Nat)
    (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentGroups base span groups state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction groups generalizing state with
  | zero =>
    simp only [packedParentGroups,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ groups ih =>
    simp only [packedParentGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have later := ih _ tail
    rw [MachineState.getReg_setPC] at later
    exact later.trans (packed_sequence_keep_output _ _ _ (out := body) path)

private theorem content_memory (before after : MachineState) (heap : Nat → BitVec 256)
    (tape : Index → BitVec 128) (remaining : Nat) (same : after.mem=before.mem)
    (prior : ParentContent before heap tape remaining) : ParentContent after heap tape remaining := by
  constructor
  · intro node lo hi
    exact (CommitGolfCandidate.read_buffer_memory_congr after before same _ _).trans (prior.nodes node lo hi)
  · intro index
    exact (CommitGolfCandidate.read_buffer_memory_congr after before same _ _).trans (prior.nonces index)

theorem parent_phase_facts (oracle : Oracle) (before : MachineState)
    (digests : DigestTape) (tape : Index → BitVec 128)
    (regs : ParentRegs before (2^24-1)) (pc : before.pc=186804)
    (prior : ParentContent before (mixedTranscriptHeap oracle.compression digests) tape (2^24-1))
    (output : before.getReg .x8=4294971392) :
    let start := mixedStopSetup before
    let full := (checkEvaluation oracle (FullWidth.parentGroups 186816 32768 1048575 480 start)).1
    let parents := (checkEvaluation oracle (packedParentGroups 580040 19065 55 full)).1
    ParentContent parents (mixedTranscriptHeap oracle.compression digests) tape 0 ∧
      ParentRegs parents 0 ∧ parents.getReg .x8=4294971392 := by
  let start := mixedStopSetup before
  let full := (checkEvaluation oracle (FullWidth.parentGroups 186816 32768 1048575 480 start)).1
  let parents := (checkEvaluation oracle (packedParentGroups 580040 19065 55 full)).1
  have startRegs : ParentRegs start (2^24-1) := mixed_stop_parent_regs before _ regs
  have startPC : start.pc=186816 := by
    rw [mixed_stop_pc,pc]
    rfl
  have startContent := content_memory before start _ tape _ (mixed_stop_memory before) prior
  have content : ParentContent parents (mixedTranscriptHeap oracle.compression digests) tape 0 :=
    mixed_parent_phases_content oracle start digests tape startContent startRegs startPC
  have fullPost : ParentRegs full 1048575 ∧
      (0 < 480 → full.pc=FullWidth.parentPC 186816 32768+8) :=
    FullWidth.groups_post 186816 32768 1048575 480 start
      (by decide) (fun _ => startPC) startRegs (out := full)
    (check_evaluation_support oracle (FullWidth.parentGroups 186816 32768 1048575 480 start))
  have fullPC : full.pc=580040 := fullPost.2 (by decide)
  have endRegs : ParentRegs parents 0 := (packed_groups_post 580040 19065 55 full (by decide)
    (fun _ => fullPC) fullPost.1 (out := parents)
    (check_evaluation_support oracle (packedParentGroups 580040 19065 55 full))).1
  have fullOutput : full.getReg .x8=start.getReg .x8 :=
    FullWidth.groups_keep_register 186816 32768 1048575 480 start full .x8 (by decide) (by decide)
      (check_evaluation_support oracle (FullWidth.parentGroups 186816 32768 1048575 480 start))
  have finalOutput : parents.getReg .x8=full.getReg .x8 :=
    packed_groups_keep_output 580040 19065 55 full (out := parents)
      (check_evaluation_support oracle (packedParentGroups 580040 19065 55 full))
  exact ⟨content,endRegs,finalOutput.trans (fullOutput.trans ((mixed_stop_register before .x8 (by decide)).trans output))⟩

theorem slice_of_slice {n outer width start len : Nat} (word : BitVec n) (bound : start+len≤width) :
    (word.extractLsb' outer width).extractLsb' start len=word.extractLsb' (outer+start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mid : start+j<width := by omega
  simp [mid,hj,Nat.add_assoc]

/-- Word `w` of the serialized tape is memory word `leafSalt 0 + w`. -/
theorem tape_word {n : Nat} (td : BitVec n) (s : MachineState)
    (slots : ∀ i : Index, td.extractLsb' (8*(80*LENGTH+16*i.val)) 128=tapeOf s i) (w : Nat) (hw : w<2*LENGTH) :
    td.extractLsb' (8*(80*LENGTH+8*w)) 64=memoryView s (leafSalt 0+w) := by
  have valid : w/2<LENGTH := by change w<2*2^24 at hw;change w/2<2^24;omega
  have slot := slots ⟨w/2,valid⟩
  have outer := slice_of_slice (outer := 8*(80*LENGTH+16*(w/2))) td (start := 64*(w%2)) (len := 64)
    (show 64*(w%2)+64≤128 by omega)
  rw [show 8*(80*LENGTH+8*w)=8*(80*LENGTH+16*(w/2))+64*(w%2) by omega,←outer,slot]
  unfold tapeOf nonceBuffer
  have inner := read_buffer_slice s (8*leafSalt (w/2)) 16 (8*(w%2)) 8 (by omega)
  rw [show 64*(w%2)=8*(8*(w%2)) by omega]
  refine inner.trans ?_
  rw [show 8*leafSalt (w/2)+8*(w%2)=8*(leafSalt 0+w) by unfold leafSalt;omega]
  exact Packed.Checker.read_buffer_word s _

theorem physical_results (o : Oracle) (m : Message) (k : Key) :
    let output := actual.readCommit (packedOutput o (seededLeaves o m k))
    output.1=publicHeap o m k 1 ∧
    (∀ n, 0<n → n<2*LENGTH → output.2.extractLsb' (256*n) 256=publicHeap o m k n) ∧
    (∀ i : Index, output.2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=tapeOf (seededLeaves o m k) i) ∧
    (∀ j : Fin 3, output.2.extractLsb' (8*(80*LENGTH+8+8*j.val)) 64=k.extractLsb' (64*j.val) 64) := by
  let leaves := seededLeaves o m k
  obtain ⟨live,good⟩ := seeded_content o m k
  have pc := live_end_pc leaves live
  obtain ⟨regs,spc,keep⟩ := parent_setup_ready leaves pc live.selector live.heapBase live.strideBase live.quartet
  have facts := parent_phase_facts o (parentSetup leaves 5)
    (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (salts o.permutation k)) (tapeOf leaves)
    regs spc (leaves_content o k m leaves good) (keep.trans live.out)
  have out := serialized _ (publicHeap o m k) (tapeOf leaves) (packedOutput o leaves) (output_state o leaves)
    facts.2.1.heap facts.2.2 facts.1
  refine ⟨out.1,out.2.1,out.2.2,?_⟩
  intro j
  have word := tape_word _ leaves out.2.2 (1+j.val) (by have:=j.isLt;change 1+j.val<2*2^24;omega)
  rw [show 80*LENGTH+8+8*j.val=80*LENGTH+8*(1+j.val) by omega,word]
  have intact := good.key (1+j.val) (by omega) (by have:=j.isLt;omega)
  change memoryView leaves (leafSalt 0+(1+j.val))=_ at intact
  rw [intact,keyBlock,show 1+j.val-1=j.val by omega]

end TwoPermutationPrototype.Grouped
