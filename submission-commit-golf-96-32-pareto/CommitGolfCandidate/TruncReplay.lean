import CommitGolfCandidate.TruncReplayParent
import CommitGolfCandidate.BindingReplay
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 55000
attribute [local irreducible] lowerHash climb storeNode pathInputs

def parents (input : CheckInput) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure fun _ => 0
  | k+1 => do
    let tab ← parents input k
    let d ← queryParent input k
    return fun i => if i=k then d else tab i

theorem parentsRun (o : Oracle) (input : CheckInput) (n : Nat) :
    o.run (parents input n) = pure (fun i => if i<n then parentAt o.compression input i else 0,41*n) := by
  induction n with
  | zero => simp [parents,oracle_run_pure]
  | succ n ih =>
    simp only [parents,oracle_run_bind,ih,pure_bind,parentRun,oracle_run_pure]
    congr 1
    apply Prod.ext
    · funext i
      by_cases eqn : i=n
      · subst i; simp
      · by_cases lt : i<n <;> simp [eqn,lt,show (i<n+1) ↔ i<n by omega]
    · dsimp; omega

theorem parentsBound (input : CheckInput) (n : Nat) : IsTotalQueryBound (parents input n) (41*n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    rw [show 41*(n+1)=41*n+41 by omega]
    apply isTotalQueryBound_bind ih
    intro tab
    simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
    exact parentBound _ _

end CommitGolfCandidate.Trunc
