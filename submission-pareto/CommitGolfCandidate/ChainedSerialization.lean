import CommitGolfCandidate.ChainedHeapOutput

/-! Abstract-state serialization and its instantiation for the delivered seeded run. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 4096
attribute [local irreducible] checkEvaluation chainedCommitBody deliveredReady Chain.chainFinalReady readBuffer

private theorem delivered_output_eq (oracle : Oracle) (message : Message) (key : Key) :
    deliveredSeedOutput oracle message key =
      ⟨.success,(checkEvaluation oracle (chainedCommitBody (deliveredReady oracle message key))).1,
        1653371596,102382335⟩ := rfl

private theorem execution_state (s : MachineState) :
    (⟨.success,s,1653371596,102382335⟩ : Execution).state = s := rfl

attribute [local irreducible] deliveredSeedOutput

theorem delivered_seed_state (oracle : Oracle) (message : Message) (key : Key) :
    (deliveredSeedOutput oracle message key).state =
      (checkEvaluation oracle (chainedCommitBody (deliveredReady oracle message key))).1 :=
  (congrArg Execution.state (delivered_output_eq oracle message key)).trans (execution_state _)

theorem serialized_body_results (candidate : Submission)
    (output : candidate.layout.commitment = 4294971392) (trap : candidate.layout.trapdoor = heapBase)
    (size : candidate.sizes.trapdoor = 96*LENGTH)
    (result : Execution) (s : MachineState) (state : result.state = s)
    (heap : Nat → BitVec 238) (salts : Index → BitVec 128)
    (root : readBuffer s 4294971392 32 = (heap 1).setWidth 256)
    (content : HeapContent s heap 0)
    (nonces : ∀ i : Index, readBuffer s (8*leafSalt i.val) 16 = salts i) :
    (candidate.readCommit result).1 = (heap 1).setWidth 256 ∧
    (∀ n, 0<n → n<2*LENGTH →
      (candidate.readCommit result).2.extractLsb' (256*n) 256 = (heap n).setWidth 256) ∧
    (∀ i : Index, (candidate.readCommit result).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128 = salts i) := by
  simp only [Submission.readCommit,state,output,trap]
  refine ⟨root,?_,?_⟩
  · intro n positive small
    have bound : n < 2*2^24 := small
    have slice := read_buffer_slice s heapBase candidate.sizes.trapdoor (32*n) 32
      (by rw [size]; change 32*n+32 ≤ 96*2^24; omega)
    rw [show 8*(32*n) = 256*n by omega] at slice
    exact slice.trans (content.nodes n positive (by omega))
  · intro i
    have bound : i.val < 2^24 := i.isLt
    have slice := read_buffer_slice s heapBase candidate.sizes.trapdoor (80*LENGTH+16*i.val) 16
      (by rw [size]; change 80*2^24+16*i.val+16 ≤ 96*2^24; omega)
    rw [show heapBase+(80*LENGTH+16*i.val) = 8*leafSalt i.val by
      change 4294971424+(80*2^24+16*i.val) = _; unfold leafSalt; omega] at slice
    exact slice.trans (nonces i)

theorem delivered_physical_results (oracle : Oracle) (message : Message) (key : Key) :
    let result := deliveredSeedOutput oracle message key
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    (Artifact.submission.readCommit result).1 = (heap 1).setWidth 256 ∧
    (∀ n, 0<n → n<2*LENGTH →
      (Artifact.submission.readCommit result).2.extractLsb' (256*n) 256 = (heap n).setWidth 256) ∧
    (∀ i : Index, (Artifact.submission.readCommit result).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128 =
      deliveredSalts oracle key i) := by
  have content := Chain.final_content oracle Artifact.submission rfl rfl message key (artifact_commit_entry message)
  have regs : Chain.BodyRegs (deliveredReady oracle message key) := by
    simpa only [deliveredReady] using content.1
  have nonces : ∀ i : Index,
      (window (memoryView (deliveredReady oracle message key)) (leafSalt i.val) : Words 2) =
        saltWords (deliveredSalts oracle key i) := by
    simpa only [deliveredReady,deliveredSalts] using content.2.nonces
  exact serialized_body_results Artifact.submission rfl rfl rfl _ _
    (delivered_seed_state oracle message key) _ _ (delivered_body_root oracle message key)
    (chained_commit_body_heap oracle _ regs _ nonces) (delivered_body_nonce oracle message key)

end CommitGolfCandidate.Chained.Native
