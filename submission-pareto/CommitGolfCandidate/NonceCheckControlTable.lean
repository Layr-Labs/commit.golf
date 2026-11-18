import CommitGolfCandidate.NonceCompressedFetch
import CommitGolfCandidate.CapExperimentalABI

/-! Finite control-flow facts for the retained checker instruction bytes.
No old ordinary instruction jumps back to its replaced first word. The two
link-producing calls return to 4256 and 4408; the indirect returns use that link. -/
namespace CommitGolfCandidate.NonceCheckControl
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def oldImage : Image := capProgram.image .check

theorem fetch_some_index (image : Image) (state : MachineState) (instruction : Instruction)
    (fetched : fetch image state = some instruction) :
    ∃ index, index < image.code.length ∧
      state.pc = BitVec.ofNat 64 (4096 + 4 * index) ∧
      (image.code[index]?).bind decodeInstruction = some instruction := by
  have enabled : 4096 ≤ state.pc.toNat ∧ state.pc.toNat % 4 = 0 := by
    by_contra invalid
    simp only [fetch, if_neg invalid] at fetched
    contradiction
  let index := (state.pc.toNat - 4096) / 4
  have decoded : (image.code[index]?).bind decodeInstruction = some instruction := by
    have equality := fetched
    simp only [fetch, if_pos enabled] at equality
    change (match image.code[index]? with | some word => decodeInstruction word | none => none) =
      some instruction at equality
    cases item : image.code[index]? <;> simpa only [item, Option.bind] using equality
  have bounded : index < image.code.length := by
    by_contra outside
    have absent : image.code[index]? = none := List.getElem?_eq_none (by omega)
    simp only [absent, Option.bind_none] at decoded
    contradiction
  refine ⟨index, bounded, ?_, decoded⟩
  have numeric : state.pc.toNat = 4096 + 4 * index := by dsimp only [index]; omega
  calc
    state.pc = BitVec.ofNat 64 state.pc.toNat := by simp
    _ = _ := by rw [numeric]

/-- Retained checker words 1..199, the leaf routine at words 257..439 and the two
truncation stubs at words 440..444; the unused words 200..256 and the expansion
wrapper at words 445..545 lie outside. -/
def CorePC (pc : Word) : Prop :=
  ((4100 ≤ pc.toNat ∧ pc.toNat ≤ 4892) ∨ (5124 ≤ pc.toNat ∧ pc.toNat ≤ 5872)) ∧ pc.toNat % 4 = 0
instance (pc : Word) : Decidable (CorePC pc) := by unfold CorePC; infer_instance

def Link (state : MachineState) : Prop :=
  state.getReg .x1 = 0 ∨ state.getReg .x1 = 4256 ∨ state.getReg .x1 = 4408

def checked (pc : Word) : Instruction → Bool
  | .base (.ADD rd _ _) | .base (.SUB rd _ _) | .base (.MUL rd _ _)
  | .base (.OR rd _ _) | .base (.AND rd _ _) | .base (.XOR rd _ _)
  | .base (.ADDI rd _ _) | .base (.ANDI rd _ _) | .base (.XORI rd _ _)
  | .base (.SLLI rd _ _) | .base (.SRLI rd _ _) | .base (.LD rd _ _) =>
    decide (rd ≠ .x1 ∧ CorePC (pc+4))
  | .base (.SD _ _ _) => decide (CorePC (pc+4))
  | .base (.SH _ _ _) => decide (CorePC (pc+4))
  | .base (.BEQ _ _ offset) | .base (.BNE _ _ offset)
  | .base (.BLTU _ _ offset) | .base (.BGEU _ _ offset) =>
    decide (CorePC (pc+4) ∧ CorePC (pc+signExtend13 offset))
  | .base (.JAL rd offset) =>
    decide ((rd=.x0 ∨ rd=.x1) ∧ CorePC (pc+signExtend21 offset) ∧ (rd=.x1 → pc+4=4256 ∨ pc+4=4408))
  | .base (.JALR rd source offset) => decide (rd=.x0 ∧ source=.x1 ∧ offset=0)
  | .base .ECALL => decide (CorePC (pc+4))
  | _ => false

def checkedIndex (index : Nat) : Bool :=
  match (oldImage.code[index]?).bind decodeInstruction with
  | some instruction => checked (BitVec.ofNat 64 (4096+4*index)) instruction
  | none => false

theorem old_length : oldImage.code.length=445 := by decide

theorem checked_table : ∀ index : Fin 445, checkedIndex index=true := by decide +kernel

theorem fetched_checked (state : MachineState) (instruction : Instruction)
    (fetched : fetch oldImage state=some instruction) : checked state.pc instruction=true := by
  obtain ⟨index,bounded,pc,decoded⟩:=fetch_some_index oldImage state instruction fetched
  rw [old_length] at bounded
  have accepted:=checked_table ⟨index,bounded⟩
  simpa only [checkedIndex,decoded,pc] using accepted

end CommitGolfCandidate.NonceCheckControl
