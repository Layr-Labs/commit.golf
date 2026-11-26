import CommitGolf.Artifact
import CommitGolfCandidate.ReconstructedBindingGame
import CommitGolfCandidate.ReconstructedFetch

namespace CommitGolfCandidate.Reconstruction.Binding.Machine
open CommitGolf CommitGolf.Riscv OracleComp RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
attribute [local irreducible] ArtifactEncoding.decode

abbrev image := Artifact.submission.image .check

/-- The four ecall sites in the actual compiled parent and the two sites in its leaf. -/
def oracleSite : Fin 6 → Nat := ![741,753,763,770,213,231]

private theorem bound : ∀ j : Fin 6, oracleSite j < 796 := by decide

theorem fetch_oracle (i : Fin 6) (s : MachineState) (pc : s.pc = BitVec.ofNat 64 (4096+4*oracleSite i)) :
    fetch image s = some (.base .ECALL) := by
  have words : ∀ j : Fin 6, Artifact.checkCode.get 32 ⟨oracleSite j,bound j⟩ = 0x73 := by decide
  rw [fetch_packed image Artifact.checkCode rfl _ (bound i) (by have := bound i; omega) s pc,words]
  rfl

def observation (o : Oracle) (fuel : Nat) (s : MachineState) :=
  checkEvaluation o (recordRows (execute image fuel s false))

private theorem recorded_map {α β : Type} (o : Oracle) (p : OracleComp World α) (f : α → β) :
    checkEvaluation o (recordRows (f <$> p)) =
      ((f (checkEvaluation o (recordRows p)).1.1,(checkEvaluation o (recordRows p)).1.2),
       (checkEvaluation o (recordRows p)).2) := by
  rw [map_eq_bind_pure_comp, record_rows_bind]
  simp [check_evaluation_map,record_rows_pure]

/-- One authentic call of this program prepends precisely the public row and
increments the replay query counter, with the trusted post-syscall state. -/
theorem step_oracle (o : Oracle) (i : Fin 6) (s : MachineState) (fuel : Nat) (q : PublicSpec.Domain)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*oracleSite i)) (sel : s.getReg .x5 = 0)
    (input : oracleInput s = some q) :
    let a := o.answer (m := Id) q
    let after := observation o fuel (writeOracleAnswer s (s.getReg .x12) q a)
    observation o (fuel+1) s =
      ((after.1.1.charge (oracleCycles q) 1,queryRows (.inr q) a ++ after.1.2),1+after.2) := by
  simp only [observation,execute,fetch_oracle i s pc,sel,ite_true,input,bind_pure_comp]
  rw [record_rows_query,check_evaluation_public_bind,check_evaluation_map,recorded_map]

/-- Recorded execution can splice an arbitrary non-query instruction segment. -/
theorem step_ordinary (o : Oracle) (before after : MachineState) (instructions cycles : Nat)
    (run : ∀ fuel, execute image (instructions+fuel) before false =
      (do let result ← execute image fuel after false; return result.charge cycles 0)) (fuel : Nat) :
    observation o (instructions+fuel) before =
      (((observation o fuel after).1.1.charge cycles 0,(observation o fuel after).1.2),
        (observation o fuel after).2) := by
  unfold observation
  rw [run,bind_pure_comp,recorded_map]

end CommitGolfCandidate.Reconstruction.Binding.Machine
