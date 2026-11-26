import CommitGolfCandidate.ReconstructedHonestCuts

namespace CommitGolfCandidate.Reconstruction.HonestFrame
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCuts HonestFlow

/-- A branch-insensitive certificate that none of the requested registers is
written before the next selected cutpoint. This holds for arbitrary input words. -/
def check {n : Nat} (packed : ArtifactEncoding.Packed n) (stop : Word → Bool) (regs : List Reg) : Nat → Word → Bool
  | 0, _ => false
  | h+1, pc =>
    match HonestBlocks.readOp packed pc with
    | none => false
    | some op => HonestBlocks.plain op && direct op && regs.all (fun r => !writesReg op r) &&
      (targets pc op).all (fun next => stop next || check packed stop regs h next)

theorem sound {n : Nat} (packed : ArtifactEncoding.Packed n) (im : Image)
    (code : im.code = ArtifactEncoding.decode 32 packed) (small : 4096+4*n < 2^64)
    (stop : Word → Bool) (regs : List Reg) (h : Nat) (pc : Word) (proof : check packed stop regs h pc = true)
    (coins : Bool) (s t : MachineState) (whereAt : s.pc = pc) (path : Reaches im coins stop s t) :
    ∀ r ∈ regs, t.getReg r = s.getReg r := by
  induction h generalizing s pc with
  | zero => cases proof
  | succ h ih =>
    cases opAt : HonestBlocks.readOp packed pc with
    | none => simp [check,opAt] at proof
    | some op =>
      simp only [check,opAt,Bool.and_eq_true] at proof
      obtain ⟨⟨⟨plain,dir⟩,regsOK⟩,next⟩ := proof
      have noCall : op ≠ .base .ECALL := by rintro rfl; cases plain
      have read := HonestBlocks.fetch_op _ _ code small s op (whereAt ▸ opAt)
      have advance (v : Execution) (one : v ∈ support (execute im 1 s coins)) (cont : v.exit = .unfinished) :
          v.state.pc ∈ targets pc op ∧ ∀ r ∈ regs, v.state.getReg r = s.getReg r := by
        have targets' := (charged_successors im s op coins read dir (fun e => (noCall e).elim) v one).2 cont
        refine ⟨whereAt ▸ targets'.1,?_⟩
        intro r mem
        have stayed := List.all_eq_true.mp regsOK r mem
        exact ordinary_step_keeps s v.state op r (HonestAbstract.continued_step im s op coins read noCall v one cont)
          (by simpa using stayed)
      cases path with
      | hit first cont _ => exact (advance _ first cont).2
      | more first cont inside after =>
        have ⟨target,kept⟩ := advance _ first cont
        have tail := List.all_eq_true.mp next _ target
        simp only [inside,Bool.false_or] at tail
        intro r mem
        exact (ih _ tail _ rfl after r mem).trans (kept r mem)

end CommitGolfCandidate.Reconstruction.HonestFrame
