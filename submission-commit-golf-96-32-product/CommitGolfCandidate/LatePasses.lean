import CommitGolfCandidate.LatePass
import CommitGolfCandidate.LateParentBasis

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def stage (n : Nat) : Fin 24 := ⟨n%24,by omega⟩
def boundary : Nat → Nat
  | 0 => 932
  | n+1 => parentEndPC (stage n)

def passes (h : Compression) (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => pass h (passes h s n) (stage n)

def total (cost : Fin 24 → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => total cost n + cost (stage n)

private theorem aligned (n : Nat) (lt : n<24) : boundary n=passStart (stage n) := by
  have all : ∀ x : Fin 24, boundary x = passStart (stage x) := by decide
  exact all ⟨n,lt⟩

theorem poses (h : Compression) (s : MachineState) (start : Entry s 932) (n : Nat) (bound : n≤24) :
    Entry (passes h s n) (boundary n) := by
  induction n with
  | zero => exact start
  | succ n ih => exact pass_end h _ (stage n) (aligned n (by omega) ▸ ih (by omega))

theorem passes_run (o : Oracle) (s : MachineState) (start : Entry s 932) (n : Nat) (bound : n≤24) (fuel : Nat) :
    o.run (execute commitImage (fuel+total passSteps n) s true) =
      (do let (out,c) ← o.run (execute commitImage fuel (passes o.compression s n) true)
          return (out.charge (total passCycles n) (total levelSize n), total levelSize n+c)) := by
  induction n generalizing fuel with
  | zero => simp [total,passes,Execution.charge]
  | succ n ih =>
    let d := stage n
    have entry := poses o.compression s start n (by omega)
    rw [aligned n (by omega)] at entry
    rw [show fuel+total passSteps (n+1)=(fuel+passSteps d)+total passSteps n by simp [total,d]; omega,
      ih (by omega),pass_run o _ d entry fuel]
    simp only [bind_assoc,pure_bind,Execution.charge,total,passes,Nat.add_assoc,d]

theorem passes_contents (h : Compression) (s : MachineState) (start : Entry s 932)
    (base : Nat → Digest) (salt : SaltTape) (inTree : LevelsThrough h base 0 s) (inGaps : Gaps s)
    (inSalt : ∀ i : Index, readBuffer s (saltAddress i) 24 = salt i) (n : Nat) (bound : n≤24) :
    LevelsThrough h base n (passes h s n) ∧ Gaps (passes h s n) ∧
      ∀ i : Index, readBuffer (passes h s n) (saltAddress i) 24 = salt i := by
  induction n with
  | zero => exact ⟨inTree,inGaps,inSalt⟩
  | succ n ih =>
    have lt : n<24 := by omega
    have ix : (stage n).val=n := Nat.mod_eq_of_lt lt
    have e := poses h s start n (by omega)
    rw [aligned n lt] at e
    obtain ⟨st,g,sa⟩ := ih (by omega)
    have st' := pass_nodes h _ (stage n) e base (ix.symm ▸ st) g
    rw [ix] at st'
    exact ⟨st',pass_gaps _ _ _ e g,fun i => (pass_salt _ _ _ e i).trans (sa i)⟩

end CommitGolfCandidate.Late
