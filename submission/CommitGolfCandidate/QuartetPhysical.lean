import CommitGolfCandidate.QuartetPhysicalInputs
import CommitGolfCandidate.QuartetRVModel
import CommitGolfCandidate.TwoPermutationRootBytes
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1700000
attribute [local irreducible] readBuffer checkEvaluation qReady qGroups QuartetLeaves.groups packedParentsTrace packedParentGroups rootPrefix physicalHeap originalLeaf

structure FinalStores (s : MachineState) (heap raw : Nat → BitVec 256) (salts : CompleteSaltTape) : Prop where
  nodes : ∀ n, 0<n → n<8388608 → nodeDigest s n=heap n
  children : ∀ i : Index, readBuffer s (8*qLeaf i.val) 32=raw i.val
  nonces : ∀ i : Index, readBuffer s (8*qSalt i.val) 16=salts i

def packedOutput (oracle : Oracle) (s : MachineState) {bits : Nat} (coins : BitVec bits) : Execution :=
  ⟨.success,(checkEvaluation oracle (commitBody s coins)).1,541679900,41943039⟩

private theorem eval_phases (oracle : Oracle) (p : OracleComp World MachineState)
    (q f g : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (do let l ← p;let m ← q l;let r ← f m;let t ← g r;return finish t)).1 =
      finish (checkEvaluation oracle (g (checkEvaluation oracle (f (checkEvaluation oracle (q (checkEvaluation oracle p).1)).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem packed_output_eq (oracle : Oracle) (s : MachineState) {bits : Nat} (coins : BitVec bits) :
    packedOutput oracle s coins=⟨.success,(checkEvaluation oracle (commitBody s coins)).1,541679900,41943039⟩ := rfl
private theorem packed_output_state (s : MachineState) :
    (⟨.success,s,541679900,41943039⟩ : Execution).state=s := rfl
attribute [local irreducible] packedOutput

private theorem eval_output (oracle : Oracle) (s : MachineState) {bits : Nat} (coins : BitVec bits) :
    let leaves := (checkEvaluation oracle (QuartetLeaves.groups 4096 0 (qReady s coins))).1
    let quad := (checkEvaluation oracle (qGroups 8192 0 (qStartPrefix leaves 3))).1
    let pre := (checkEvaluation oracle (packedParentsTrace 4194176 127 (upStartPrefix quad 6))).1
    let parents := (checkEvaluation oracle (packedParentGroups QuartetUpper.loopBase 32767 128 pre)).1
    (packedOutput oracle s coins).state=rootPrefix parents 10 := by
  have pr := congrArg Execution.state (packed_output_eq oracle s coins)
  refine pr.trans ((packed_output_state _).trans ?_)
  unfold commitBody
  exact eval_phases oracle (QuartetLeaves.groups 4096 0 (qReady s coins))
    (fun l => qGroups 8192 0 (qStartPrefix l 3))
    (fun q => packedParentsTrace 4194176 127 (upStartPrefix q 6))
    (fun pre => packedParentGroups QuartetUpper.loopBase 32767 128 pre)
    (fun parents => rootPrefix parents 10)

private theorem finish_stores (s leafState : MachineState) (heap raw : Nat → BitVec 256) (salts : CompleteSaltTape)
    (p : UpperContent s heap (memoryView leafState) 0) (l : PaddedLeaves (memoryView leafState) (fun i => digestWords (raw i)))
    (saved : ∀ i : Index, window (memoryView leafState) (qSalt i.val)=saltWords (salts i)) : FinalStores s heap raw salts := by
  refine ⟨p.nodes,?_,?_⟩
  · intro i;apply aligned_buffer_eq _ _ _ (by decide);intro k hk
    have hi : i.val<16777216:=i.isLt
    exact (p.high _ (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource;omega)).trans
      (congrFun (l.2 i.val hi) (⟨k,hk⟩ : Fin 4))
  · intro i;apply aligned_buffer_eq _ _ _ (by decide);intro k hk
    have hi : i.val<16777216:=i.isLt
    exact (p.high _ (by unfold qSalt qSource;omega) (by unfold qSalt;omega)).trans
      (congrFun (saved i) (⟨k,hk⟩ : Fin 2))

private theorem serialize (parents : MachineState) (heap raw : Nat → BitVec 256) (salts : CompleteSaltTape)
    (res : Execution) (state : res.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (stores : FinalStores parents heap raw salts) :
    let output := actual.readCommit res
    output.1=heap 1 ∧
      (∀ n, 0<n → n<8388608 → Opening.trapdoorHeap (s:=actual) output.2 n=heap n) ∧
      (∀ i : Index, QuartetRV.trapdoorLeaf (s:=actual) output.2 i.val=raw i.val) ∧
      (∀ i : Index, QuartetRV.trapdoorSalt (s:=actual) output.2 i=salts i) := by
  have out : actual.layout.commitment=4294971392:=rfl
  have td : actual.layout.trapdoor=4294971424:=rfl
  have size : actual.sizes.trapdoor=2952790016:=rfl
  simp only [Opening.trapdoorHeap,QuartetRV.trapdoorLeaf,QuartetRV.trapdoorSalt,Submission.readCommit,state,out,td]
  refine ⟨(root_copy_output parents heapReg outReg).trans (stores.nodes 1 (by decide) (by decide)),?_,?_,?_⟩
  · intro n pos small
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor (32*n) 32 (by rw [size];omega)
    rw [show 8*(32*n)=256*n by omega,show 4294971424+32*n=8*treeWord n by unfold treeWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold treeWord;omega) (by unfold treeWord;omega) (by decide)]
    exact stores.nodes n pos small
  · intro i;have hi : i.val<16777216 := i.isLt
    let off := 32*LENGTH+512*(i.val/4)+72+32*(i.val%4)
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor off 32
      (by rw [size];dsimp [off,LENGTH,LOG_LENGTH];omega)
    rw [show 4294971424+off=8*qLeaf i.val by dsimp [off,qLeaf,qSource,LENGTH,LOG_LENGTH];omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 32 (by unfold qLeaf qSource;omega) (by unfold qLeaf qSource;omega) (by decide)]
    exact stores.children i
  · intro i;have hi : i.val<16777216 := i.isLt
    let off:=160*LENGTH+16*i.val
    have slice:=read_buffer_slice (rootPrefix parents 10) 4294971424 actual.sizes.trapdoor off 16
      (by rw [size];dsimp [off,LENGTH,LOG_LENGTH];omega)
    rw [show 4294971424+off=8*qSalt i.val by dsimp [off,qSalt,LENGTH,LOG_LENGTH];omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents outReg _ 16 (by unfold qSalt;omega) (by unfold qSalt;omega) (by decide)]
    exact stores.nonces i


theorem physical_results (oracle : Oracle) (msg : Message) (packed : BitVec (128*LENGTH)) :
    let output := actual.readCommit (packedOutput oracle (actual.initialState .commit msg) packed)
    let salts := splitBlocks 128 LENGTH packed
    let heap := physicalHeap oracle msg salts
    output.1=heap 1 ∧
      (∀ n, 0<n → n<8388608 → Opening.trapdoorHeap (s:=actual) output.2 n=heap n) ∧
      (∀ i : Index, QuartetRV.trapdoorLeaf (s:=actual) output.2 i.val=originalLeaf oracle msg salts i.val) ∧
      (∀ i : Index, QuartetRV.trapdoorSalt (s:=actual) output.2 i=salts i) := by
  let s:=actual.initialState .commit msg
  let start:=qReady s packed
  let salts:=splitBlocks 128 LENGTH packed
  let heap:=physicalHeap oracle msg salts
  let ready:=q_ready_regs s (show CommitEntry s from ⟨rfl,rfl,rfl,rfl⟩) packed
  let leaves:=(checkEvaluation oracle (QuartetLeaves.groups 4096 0 start)).1
  obtain ⟨_,qpc,qregs,carry⟩ := start_q start ready (check_evaluation_support oracle (QuartetLeaves.groups 4096 0 start))
  let qs:=qStartPrefix leaves 3
  let quad:=(checkEvaluation oracle (qGroups 8192 0 qs)).1
  obtain ⟨_,upc,uregs,out⟩ := start_upper qs qregs qpc carry (check_evaluation_support oracle (qGroups 8192 0 qs))
  let us:=upStartPrefix quad 6
  let pre:=(checkEvaluation oracle (packedParentsTrace 4194176 127 us)).1
  let parents:=(checkEvaluation oracle (packedParentGroups QuartetUpper.loopBase 32767 128 pre)).1
  obtain ⟨leafContent,nonces⟩ := actual_leaf_content oracle msg packed
  have uContent:=ready_upper_content oracle msg salts leaves leafContent
  have preContent:=upper_sequence_semantics oracle us heap (memoryView leaves) 4194176 127 (by decide)
    (physical_heap_parent oracle msg salts) uContent uregs
  have parentContent:=upper_groups_semantics oracle QuartetUpper.loopBase 32767 128 pre heap (memoryView leaves) (by decide)
    (physical_heap_parent oracle msg salts) preContent.1 preContent.2
  have hit1:=check_evaluation_support oracle (packedParentsTrace 4194176 127 us)
  have hit2:=check_evaluation_support oracle (packedParentGroups QuartetUpper.loopBase 32767 128 pre)
  have pc1:= (packed_parent_segment_post 191180 4194176 127 0 us uregs (by simpa [packedParentPC] using upc) hit1).2
  have pc2 : pre.pc=QuartetUpper.loopBase := pc1
  have preg := (packed_groups_post QuartetUpper.loopBase 32767 128 pre (by decide) (fun _ => pc2) preContent.2 hit2).1
  have x8:= (wide_parent_full_register _ _ _ _ hit2).trans ((packed_sequence_keeps_output _ _ _ hit1).trans out)
  exact serialize parents heap (originalLeaf oracle msg salts) salts _ (eval_output oracle s packed) preg.heap x8
    (finish_stores parents leaves heap _ salts parentContent leafContent nonces)

end TwoPermutationPrototype.QuartetCommit
