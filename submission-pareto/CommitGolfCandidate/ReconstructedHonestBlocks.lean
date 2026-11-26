import CommitGolfCandidate.ReconstructedHonestAbstract
import CommitGolfCandidate.ReconstructedHonestBinaryRank

namespace CommitGolfCandidate.Reconstruction.HonestBlocks
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow HonestRegisters HonestAbstract
open CommitBlocks (addr)
open HonestBinaryRank (index)

/-- Decode only aligned, in-image addresses using the trusted packed image. -/
def readOp {n : Nat} (p : ArtifactEncoding.Packed n) (pc : Word) : Option Instruction :=
  if pc == addr (index pc) then
    if h : index pc < n then decodeInstruction (p.get 32 ⟨index pc,h⟩) else none
  else none

theorem fetch_op {n : Nat} (p : ArtifactEncoding.Packed n) (im : Image)
    (same : im.code = ArtifactEncoding.decode 32 p) (small : 4096+4*n < 2^64)
    (s : MachineState) (op : Instruction) (found : readOp p s.pc = some op) : fetch im s = some op := by
  unfold readOp at found
  split at found
  · rename_i pc
    split at found
    · rename_i h
      exact (fetch_packed im p same _ h (by omega) s (beq_iff_eq.mp pc)).trans found
    · cases found
  · cases found

def plain : Instruction → Bool
  | .base .ECALL => false
  | _ => true

def prune (keep : Reg → Bool) (m : Known) (r : Reg) := if keep r then m r else none

theorem pruned (s : MachineState) (m : Known) (h : Agrees s m) (keep : Reg → Bool) :
    Agrees s (prune keep m) := by
  intro r v eq
  cases k : keep r with
  | false => simp [prune,k] at eq
  | true => exact h r v (by simpa [prune,k] using eq)

/-- At every possible machine branch, either check the cutpoint postcondition
or continue with the verified remaining cost. A caller may forget irrelevant
registers at every PC, reducing the proof table. -/
def check {n : Nat} (packed : ArtifactEncoding.Packed n) (cut : Word → Bool)
    (post : Word → Known → Bool) (keep : Word → Reg → Bool) : Nat → Word → Known → Nat → Bool
  | 0, _, _, _ => false
  | h+1, pc, m, budget =>
    match readOp packed pc with
    | none => false
    | some op => plain op && direct op && decide (price op ≤ budget) &&
      (destinations pc m op).all fun next =>
        let facts := prune (keep next) (update m op)
        if cut next then post next facts else check packed cut post keep h next facts (budget-price op)

/-- A composable checked cost bound. The boundary assumption applies only to
machine states satisfying the certified control-register postconditions. -/
theorem sound {n : Nat} (packed : ArtifactEncoding.Packed n) (im : Image)
    (code : im.code = ArtifactEncoding.decode 32 packed) (small : 4096+4*n < 2^64)
    (cut : Word → Bool) (post : Word → Known → Bool) (keep : Word → Reg → Bool)
    (coins : Bool) (tail : Nat) (boundary : ∀ pc m, cut pc = true → post pc m = true →
      ∀ s : MachineState, s.pc = pc → Agrees s m → ∀ f r, r ∈ support (execute im f s coins) → r.cycles ≤ tail)
    (height : Nat) (pc : Word) (m : Known) (budget : Nat) (checked : check packed cut post keep height pc m budget = true)
    (s : MachineState) (atPC : s.pc = pc) (agrees : Agrees s m) (fuel : Nat) (r : Execution)
    (run : r ∈ support (execute im fuel s coins)) : r.cycles ≤ budget+tail := by
  induction height generalizing pc m budget s fuel r with
  | zero => cases checked
  | succ h ih =>
    cases fuel with
    | zero => simp only [execute,support_pure,Set.mem_singleton_iff] at run; subst r; exact Nat.zero_le _
    | succ f =>
      cases opAt : readOp packed pc with
      | none => simp [check,opAt] at checked
      | some op =>
        simp only [check,opAt,Bool.and_eq_true,decide_eq_true_eq] at checked
        obtain ⟨⟨⟨notCall,direct'⟩,priceBound⟩,next⟩ := checked
        have noCall : op ≠ .base .ECALL := by rintro rfl; cases notCall
        have fetch := fetch_op packed im code small s op (atPC ▸ opAt)
        rw [show f+1=1+f by omega,execute_add,mem_support_bind_iff] at run
        obtain ⟨mid,first,rest⟩ := run
        have ⟨fee,progress⟩ := one im s op m coins fetch noCall direct' agrees mid first
        by_cases cont : mid.exit = .unfinished
        · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at rest
          obtain ⟨out,remain,rfl⟩ := rest
          obtain ⟨target,stronger⟩ := progress cont
          rw [atPC] at target
          have edge := List.all_eq_true.mp next mid.state.pc target
          let m' := prune (keep mid.state.pc) (update m op)
          have consistent : Agrees mid.state m' := pruned _ _ stronger _
          cases done : cut mid.state.pc with
          | true =>
            have accept : post mid.state.pc m' = true := by simpa only [done,ite_true] using edge
            have b := boundary _ _ done accept mid.state rfl consistent f out remain
            change mid.cycles+out.cycles ≤ _
            omega
          | false =>
            have more : check packed cut post keep h mid.state.pc m' (budget-price op) = true := by
              simpa only [done,Bool.false_eq_true,ite_false] using edge
            have b := ih _ _ _ more mid.state rfl consistent f out remain
            change mid.cycles+out.cycles ≤ _
            omega
        · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at rest
          subst r; omega

end CommitGolfCandidate.Reconstruction.HonestBlocks
