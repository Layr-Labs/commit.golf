import CommitGolfCandidate.ReconstructedCheckOrdinary

namespace CommitGolfCandidate.Reconstruction.CheckParentImage
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

inductive Action where
  | plain (i : Op)
  | oracle (site : Fin 6)
  | ret
  deriving Repr

def Action.instr : Action→Instruction
  | .plain i=>i.instr
  | .oracle _=>.base .ECALL
  | .ret=>.base (.JALR .x0 .x1 0)

/-- The checker calls this subroutine from its individual path loop and its
shared cap loop. Both call sites execute this same compiled body. -/
def program : Array Action := #[
  .plain (.arith (.addi .x2 .x2 3952)),
  .plain (.sd .x2 .x1 136),
  .plain (.sd .x2 .x8 128),
  .plain (.arith (.addi .x8 .x2 144)),
  .plain (.arith (.addi .x15 .x11 0)),
  .plain (.arith (.addi .x14 .x10 0)),
  .plain (.ld .x10 .x12 24),
  .plain (.ld .x11 .x12 16),
  .plain (.ld .x13 .x12 8),
  .plain (.ld .x16 .x12 0),
  .plain (.sd .x8 .x10 4040),
  .plain (.sd .x8 .x11 4032),
  .plain (.sd .x8 .x13 4024),
  .plain (.sd .x8 .x16 4016),
  .plain (.ld .x10 .x12 32),
  .plain (.ld .x11 .x12 40),
  .plain (.ld .x13 .x12 48),
  .plain (.ld .x12 .x12 56),
  .plain (.sd .x8 .x10 4048),
  .plain (.sd .x8 .x11 4056),
  .plain (.sd .x8 .x13 4064),
  .plain (.sd .x8 .x12 4072),
  .plain (.arith (.addiw .x10 .x15 1)),
  .plain (.arith (.slli .x11 .x10 32)),
  .plain (.arith (.addi .x12 .x0 24)),
  .plain (.arith (.srli .x11 .x11 32)),
  .plain (.branch .ne .x10 .x12 8),
  .plain (.arith (.addi .x10 .x0 4095)),
  .plain (.arith (.slli .x10 .x10 48)),
  .plain (.arith (.addi .x12 .x11 4076)),
  .plain (.arith (.addi .x13 .x0 4084)),
  .plain (.branch .ge .x12 .x13 72),
  .plain (.arith (.slli .x11 .x11 3)),
  .plain (.arith (.lui .x12 512)),
  .plain (.arith (.addi .x12 .x12 608)),
  .plain (.arith (.rr .add .x11 .x12 .x11)),
  .plain (.ld .x11 .x11 0),
  .plain (.arith (.rr .sub32 .x11 .x0 .x11)),
  .plain (.arith (.addi .x12 .x0 4095)),
  .plain (.arith (.rr .shr .x11 .x12 .x11)),
  .plain (.arith (.rr .bitOr .x10 .x11 .x10)),
  .plain (.ld .x11 .x8 4040),
  .plain (.arith (.srli .x12 .x12 16)),
  .plain (.ld .x13 .x8 4072),
  .plain (.arith (.rr .bitXor .x10 .x10 .x12)),
  .plain (.arith (.rr .bitOr .x11 .x10 .x11)),
  .plain (.sd .x8 .x11 4040),
  .plain (.arith (.rr .bitOr .x10 .x10 .x13)),
  .plain (.jal .x0 12),
  .plain (.ld .x11 .x8 4072),
  .plain (.arith (.rr .bitOr .x10 .x11 .x10)),
  .plain (.sd .x8 .x10 4072),
  .plain (.arith (.slli .x10 .x15 32)),
  .plain (.arith (.srli .x17 .x10 32)),
  .plain (.arith (.addi .x6 .x17 4088)),
  .plain (.arith (.addi .x7 .x0 12)),
  .plain (.arith (.slli .x16 .x17 3)),
  .plain (.branch .lt .x7 .x6 136),
  .plain (.sd .x8 .x0 4008),
  .plain (.sd .x8 .x0 4000),
  .plain (.sd .x8 .x0 3992),
  .plain (.sd .x8 .x0 3984),
  .plain (.arith (.addi .x10 .x8 4016)),
  .plain (.arith (.addi .x11 .x0 64)),
  .plain (.arith (.addi .x12 .x8 3952)),
  .plain (.arith (.addi .x13 .x0 0)),
  .plain (.arith (.addi .x5 .x0 0)),
  .oracle 0,
  .plain (.branch .eq .x6 .x7 64),
  .plain (.arith (.lui .x10 512)),
  .plain (.arith (.addi .x10 .x10 808)),
  .plain (.arith (.rr .add .x10 .x10 .x16)),
  .plain (.ld .x6 .x10 0),
  .plain (.arith (.addi .x7 .x0 3)),
  .plain (.arith (.addi .x11 .x0 64)),
  .plain (.arith (.addi .x13 .x0 0)),
  .plain (.arith (.addi .x10 .x8 3952)),
  .plain (.arith (.addi .x12 .x8 3952)),
  .plain (.arith (.addi .x5 .x0 0)),
  .oracle 1,
  .plain (.arith (.slli .x10 .x7 32)),
  .plain (.arith (.srli .x10 .x10 32)),
  .plain (.arith (.addi .x7 .x7 1)),
  .plain (.branch .lt .x10 .x6 8164),
  .plain (.arith (.addi .x10 .x8 3952)),
  .plain (.arith (.addi .x11 .x0 64)),
  .plain (.arith (.addi .x12 .x14 0)),
  .plain (.arith (.addi .x13 .x0 0)),
  .plain (.arith (.addi .x5 .x0 0)),
  .oracle 2,
  .plain (.jal .x0 28),
  .plain (.arith (.addi .x10 .x8 4016)),
  .plain (.arith (.addi .x11 .x0 64)),
  .plain (.arith (.addi .x12 .x14 0)),
  .plain (.arith (.addi .x13 .x0 0)),
  .plain (.arith (.addi .x5 .x0 0)),
  .oracle 3,
  .plain (.arith (.addi .x17 .x17 4076)),
  .plain (.arith (.addi .x10 .x0 4084)),
  .plain (.branch .ge .x17 .x10 48),
  .plain (.branch .eq .x15 .x0 72),
  .plain (.arith (.lui .x10 512)),
  .plain (.arith (.addi .x10 .x10 608)),
  .plain (.arith (.rr .add .x10 .x10 .x16)),
  .plain (.ld .x10 .x10 0),
  .plain (.ld .x11 .x14 24),
  .plain (.arith (.rr .sub32 .x10 .x0 .x10)),
  .plain (.arith (.addi .x12 .x0 4095)),
  .plain (.arith (.rr .shr .x10 .x12 .x10)),
  .plain (.arith (.rr .bitAnd .x10 .x10 .x11)),
  .plain (.jal .x0 28),
  .plain (.arith (.lui .x10 512)),
  .plain (.arith (.addi .x10 .x10 408)),
  .plain (.arith (.rr .add .x10 .x10 .x16)),
  .plain (.ld .x10 .x10 0),
  .plain (.ld .x11 .x14 24),
  .plain (.arith (.rr .remu .x10 .x11 .x10)),
  .plain (.sd .x14 .x10 24),
  .plain (.ld .x1 .x2 136),
  .plain (.ld .x8 .x2 128),
  .plain (.arith (.addi .x2 .x2 144)),
  .ret]

private def same : Option Instruction→Instruction→Bool
  | some (.base x),.base y=>decide (x=y)
  | some (.word a b c d),.word e f g h=>decide (a=e ∧ b=f ∧ c=g ∧ d=h)
  | some (.sraiw a b c),.sraiw d e f=>decide (a=d ∧ b=e ∧ c=f)
  | _,_=>false

private theorem same_sound {op : Option Instruction} {expect : Instruction} (h : same op expect=true) : op=some expect := by
  cases op with
  | none => cases expect <;> contradiction
  | some a =>
    cases a <;> cases expect <;> simp_all [same]

def entry (i : Fin 122) := program[i.val]'i.isLt

private theorem words : ∀ i : Fin 122, same (decodeInstruction
    (Artifact.checkCode.get 32 ⟨674+i.val,by have:=i.isLt; omega⟩)) (entry i).instr=true := by decide

theorem fetch_action (i : Fin 122) (s : MachineState) (pc : s.pc=CommitBlocks.addr (674+i.val)) :
    fetch image s=some (entry i).instr := by
  have lim := i.isLt
  rw [fetch_packed image Artifact.checkCode rfl _ (by omega :674+i.val<796) (by omega) s pc]
  exact same_sound (words i)

theorem oracle_site (i : Fin 122) (site : Fin 6) (h : entry i=Action.oracle site) :
    674+i.val=oracleSite site := by
  have yes : ∀ x : Fin 122, (match entry x with
      | .oracle k=>decide (674+x.val=oracleSite k)
      | _=>true)=true := by decide
  have z := yes i
  rw [h] at z
  exact of_decide_eq_true z

def find (pc : Word) : Option (Fin 122) :=
  let n := ((pc.toNat-4096)/4)-674
  if h : n<122 then if pc==CommitBlocks.addr (674+n) then some ⟨n,h⟩ else none else none

theorem find_pc {pc : Word} {i : Fin 122} (h : find pc=some i) : pc=CommitBlocks.addr (674+i.val) := by
  unfold find at h;dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i eq
  cases h
  exact beq_iff_eq.1 eq

end CommitGolfCandidate.Reconstruction.CheckParentImage
