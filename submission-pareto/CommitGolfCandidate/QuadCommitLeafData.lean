import CommitGolfCandidate.QuadCommitRetained
import CommitGolfCandidate.QuadCommitExecution
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_support splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
attribute [local irreducible] image writeBits checkEvaluation Leaves.groups Leaves.group Leaves.batch

theorem all_leaf_prefix (oracle : Oracle) (s : MachineState) (r : Leaves.Regs s 0 0) :
    Leaves.PinnedLeafPrefix oracle (memoryView s)
      (checkEvaluation oracle (Leaves.groups 4096 0 s)).1 (2^24) := by
  have raw := Leaves.prefix_groups oracle (memoryView s) s
    4096 0 (by decide) (fun _ => r) (Leaves.empty_pinned_leaf_prefix oracle s)
  rw [show 4096*(0+4096)=2^24 by decide] at raw
  exact raw

theorem ready_leaf_retained (oracle : Oracle) (ready : MachineState) (r : ReadyRegs ready)
    (msg : Message) (salts : CompleteSaltTape)
    (messages : ∀ i : Index, window (memoryView ready) (leafStart i.val+5) = messageWords msg i)
    (nonces : ∀ i : Index, window (memoryView ready) (Leaves.leafSalt i.val) = saltWords (salts i))
    (zeros : ∀ g < 2^22, ∀ k : Fin 9, memoryView ready (groupWord g+k.val)=0)
    (quadZeros : ∀ h < 2^20, ∀ k : Fin 9, memoryView ready (quad2GroupWord h+k.val)=0)
    (quad3Zeros : ∀ m < 2^18, ∀ k : Fin 9, memoryView ready (quad3GroupWord m+k.val)=0) :
    Retained (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1 (quadPublicLeaves oracle msg salts) salts :=
  retained_from_prefix oracle (memoryView ready) (checkEvaluation oracle (Leaves.groups 4096 0 ready)).1
    (quadPublicLeaves oracle msg salts) salts (all_leaf_prefix oracle ready r.regs)
    (windows_pinned_leaf oracle (memoryView ready) msg salts messages nonces) nonces zeros quadZeros quad3Zeros
end TwoPermutationPrototype.Quad.Commit
