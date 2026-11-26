import CommitGolfCandidate.ReconstructedCheckProgram

namespace CommitGolfCandidate.Reconstruction.CheckLeafImage
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

def code : Array (Option CheckSpecial.Op) := #[
  some (.basic (.ld .x5 .x13 0)),
  some (.basic (.sd .x17 .x5 0)),
  some (.basic (.arith (.addi .x17 .x17 8))),
  some (.basic (.arith (.addi .x13 .x13 8))),
  some (.bnePtr .x17 .x7 8176),
  some (.basic (.arith (.slli .x11 .x11 32))),
  some (.basic (.arith (.srli .x25 .x11 32))),
  some (.basic (.arith (.slli .x12 .x12 32))),
  some (.basic (.arith (.srli .x18 .x12 32))),
  some (.andi .x27 .x10 63),
  some (.basic (.arith (.addi .x11 .x0 200))),
  some (.basic (.arith (.addi .x12 .x8 2048))),
  some (.basic (.arith (.addi .x12 .x12 3784))),
  some (.basic (.arith (.addi .x13 .x0 1))),
  some (.basic (.arith (.addi .x10 .x6 0))),
  some (.basic (.arith (.addi .x5 .x0 0))),
  none,
  some (.basic (.arith (.slli .x16 .x16 8))),
  some (.basic (.arith (.lui .x10 1))),
  some (.subPtr .x10 .x8 .x10),
  some (.basic (.ld .x10 .x10 1712)),
  some (.basic (.arith (.rr .add .x16 .x10 .x16))),
  some (.basic (.arith (.addi .x10 .x16 519))),
  some (.basic (.arith (.addi .x11 .x8 2048))),
  some (.basic (.arith (.addi .x11 .x11 3872))),
  some (.basic (.sd .x11 .x10 0)),
  some (.basic (.sd .x11 .x14 8)),
  some (.basic (.sd .x11 .x15 16)),
  some (.basic (.arith (.addi .x11 .x0 200))),
  some (.basic (.arith (.addi .x12 .x8 3784))),
  some (.basic (.arith (.addi .x13 .x0 1))),
  some (.basic (.arith (.addi .x10 .x8 2048))),
  some (.basic (.arith (.addi .x10 .x10 3872))),
  some (.basic (.arith (.addi .x5 .x0 0))),
  none,
  some (.basic (.ld .x10 .x8 3808)),
  some (.basic (.ld .x12 .x8 3784)),
  some (.basic (.ld .x13 .x8 3792)),
  some (.basic (.ld .x14 .x8 3800)),
  some (.basic (.arith (.slli .x10 .x10 16))),
  some (.basic (.arith (.srli .x11 .x10 16)))]

private def same : Option Instruction→Instruction→Bool
  | some (.base x),.base y=>decide (x=y)
  | _,_=>false

private theorem matched {op : Option Instruction} {want : Instruction} (h : same op want=true) : op=some want := by
  cases op with
  | none=>cases want <;> contradiction
  | some a=>cases a <;> cases want <;> simp_all [same]

def entry (i : Fin 41) := code[i.val]'i.isLt

private theorem words : ∀ i : Fin 41, (match entry i with
  | some op=>same (decodeInstruction (Artifact.checkCode.get 32 ⟨197+i.val,by have:=i.isLt;omega⟩)) op.instr
  | none=>true)=true := by decide

def lookup (pc : Word) : Option CheckSpecial.Op := do
  let idx := (pc.toNat-4096)/4-197
  if bound : idx<41 then
    if pc=CommitBlocks.addr (197+idx) then entry ⟨idx,bound⟩ else none
  else none

theorem decoded (s : MachineState) (op : CheckSpecial.Op) (ok : lookup s.pc=some op) :
    fetch image s=some op.instr := by
  unfold lookup at ok;dsimp only at ok
  split at ok <;> try contradiction
  rename_i bound
  split at ok <;> try contradiction
  rename_i pc
  let i : Fin 41:=⟨_,bound⟩
  have reflect := words i
  change entry i=some op at ok
  rw [ok] at reflect
  rw [fetch_packed image Artifact.checkCode rfl _ (by have:=i.isLt;omega :197+i.val<796) (by have:=i.isLt;omega) s pc]
  exact matched reflect

end CommitGolfCandidate.Reconstruction.CheckLeafImage
