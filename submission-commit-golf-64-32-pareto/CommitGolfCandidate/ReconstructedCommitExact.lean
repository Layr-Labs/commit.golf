import CommitGolfCandidate.ReconstructedCommitSetup
import CommitGolfCandidate.HidingDistribution
import CommitGolfCandidate.TwoPermutationSyscall

namespace CommitGolfCandidate.Reconstruction.CommitExact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype (window)

attribute [local irreducible] execute writeBits ArtifactEncoding.decode

/-- Executing a prefix of an image against a fixed oracle deterministically reaches
the designated machine state, for every possible continuation fuel. -/
def Segment (o : Oracle) (im : Image) (n : Nat) (s t : MachineState) : Prop :=
  ∃ c q : Nat, ∀ fuel : Nat,
    fixedOracleRun o (execute im (n+fuel) s true) =
    (fun r : Execution => r.charge c q) <$> fixedOracleRun o (execute im fuel t true)

theorem empty (o : Oracle) (im : Image) (s : MachineState) : Segment o im 0 s s := by
  refine ⟨0,0,fun fuel => ?_⟩
  simp [Execution.charge]

theorem compose {o : Oracle} {im : Image} {n m : Nat} {s t u : MachineState}
    (first : Segment o im n s t) (second : Segment o im m t u) : Segment o im (n+m) s u := by
  obtain ⟨c,q,f⟩ := first
  obtain ⟨c',q',g⟩ := second
  refine ⟨c+c',q+q',fun fuel => ?_⟩
  rw [Nat.add_assoc,f,g,Functor.map_map]
  congr 1
  funext r
  simp [Execution.charge,Nat.add_assoc,Function.comp_def]

theorem plain (o : Oracle) (im : Image) (s t : MachineState) (op : Instruction)
    (f : fetch im s = some op) (valid : ordinaryStep s op = some t) :
    Segment o im 1 s t := by
  refine ⟨instructionCycles op,0,fun fuel => ?_⟩
  rw [Nat.add_comm 1,execute_ordinary_step im op s t fuel true f valid]
  rw [bind_pure_comp,fixed_oracle_run_map]

theorem call (o : Oracle) (im : Image) (s : MachineState) (query : PublicSpec.Domain)
    (f : fetch im s = some (.base .ECALL)) (selector : s.getReg .x5 = 0)
    (args : oracleInput s = some query) :
    Segment o im 1 s (writeOracleAnswer s (s.getReg .x12) query (o.answer (m := Id) query)) := by
  refine ⟨oracleCycles query,1,fun fuel => ?_⟩
  rw [Nat.add_comm 1,execute,f]
  simp only [selector,ite_true,args]
  rw [fixed_oracle_run_public o query]
  rw [bind_pure_comp,fixed_oracle_run_map]

theorem permutation (o : Oracle) (im : Image) (s : MachineState) (src dst : Nat)
    (room : src + 25 ≤ 2^33) (target : dst + 25 ≤ 2^33)
    (source : s.getReg .x10 = wordAddress src) (out : s.getReg .x12 = wordAddress dst)
    (selector : s.getReg .x5 = 0) (len : s.getReg .x11 = 200) (perm : s.getReg .x13 = 1)
    (f : fetch im s = some (.base .ECALL)) :
    Segment o im 1 s (writeBits s (wordAddress dst) (o.permutation (packBuffer (window (memoryView s) src)))) := by
  have h := call o im s _ f selector (oracle_input_permutation s src dst room target source out len perm)
  rw [out] at h
  exact h

end CommitGolfCandidate.Reconstruction.CommitExact
