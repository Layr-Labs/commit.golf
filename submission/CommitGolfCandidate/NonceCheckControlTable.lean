import CommitGolfCandidate.NonceOpeningFetch

/-! Finite control-flow facts for the retained checker instruction bytes.
No old ordinary instruction jumps back to its replaced first word. The sole
link-producing call returns to4256; its sole indirect return uses that link. -/
namespace CommitGolfCandidate.NonceCheckControl
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def oldImage : Image := capProgram.image .check

def CorePC (pc : Word) : Prop := 4100 ≤ pc.toNat ∧ pc.toNat ≤ 4892 ∧ pc.toNat%4=0
instance (pc : Word) : Decidable (CorePC pc) := by unfold CorePC; infer_instance

def Link (state : MachineState) : Prop := state.getReg .x1=0 ∨ state.getReg .x1=4256

def checked (pc : Word) : Instruction → Bool
  | .base (.ADD rd _ _) | .base (.SUB rd _ _) | .base (.MUL rd _ _)
  | .base (.OR rd _ _) | .base (.AND rd _ _) | .base (.XOR rd _ _)
  | .base (.ADDI rd _ _) | .base (.ANDI rd _ _) | .base (.XORI rd _ _)
  | .base (.SLLI rd _ _) | .base (.SRLI rd _ _) | .base (.LD rd _ _) =>
    decide (rd ≠ .x1 ∧ CorePC (pc+4))
  | .base (.SD _ _ _) => decide (CorePC (pc+4))
  | .base (.BEQ _ _ offset) | .base (.BNE _ _ offset)
  | .base (.BLTU _ _ offset) | .base (.BGEU _ _ offset) =>
    decide (CorePC (pc+4) ∧ CorePC (pc+signExtend13 offset))
  | .base (.JAL rd offset) =>
    decide ((rd=.x0 ∨ rd=.x1) ∧ CorePC (pc+signExtend21 offset) ∧ (rd=.x1 → pc+4=4256))
  | .base (.JALR rd source offset) => decide (rd=.x0 ∧ source=.x1 ∧ offset=0)
  | .base .ECALL => decide (CorePC (pc+4))
  | _ => false

def checkedIndex (index : Nat) : Bool :=
  match (oldImage.code[index]?).bind decodeInstruction with
  | some instruction => checked (BitVec.ofNat 64 (4096+4*index)) instruction
  | none => false

theorem old_length : oldImage.code.length=200 := by decide

theorem checked_table : ∀ index : Fin 200, checkedIndex index=true := by decide

theorem fetched_checked (state : MachineState) (instruction : Instruction)
    (fetched : fetch oldImage state=some instruction) : checked state.pc instruction=true := by
  obtain ⟨index,bounded,pc,decoded⟩:=nonce_fetch_some_index oldImage state instruction fetched
  rw [old_length] at bounded
  have accepted:=checked_table ⟨index,bounded⟩
  simpa only [checkedIndex,decoded,pc] using accepted

end CommitGolfCandidate.NonceCheckControl
