import CommitGolfCandidate.ReconstructedCheckCursorOps
import CommitGolfCandidate.ReconstructedCheckDecode

namespace CommitGolfCandidate.Reconstruction.CheckCursorImage
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckLink
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

def headCode : Array Op := #[
  .plain (.basic (.arith (.srli .x10 .x24 3))),
  .plain (.andi .x10 .x10 4088),
  .plain (.basic (.arith (.rr .add .x12 .x10 .x19))),
  .plain (.basic (.ld .x10 .x12 0)),
  .plain (.andi .x11 .x24 63),
  .plain (.basic (.arith (.rr .shr .x14 .x10 .x24))),
  .plain (.basic (.arith (.addi .x10 .x24 64))),
  .plain (.basic (.branch .eq .x11 .x0 72)),
  .plain (.basic (.ld .x13 .x12 8)),
  .plain (.basic (.arith (.srli .x10 .x10 3))),
  .plain (.andi .x10 .x10 4088),
  .plain (.basic (.arith (.rr .add .x12 .x10 .x19))),
  .plain (.basic (.ld .x10 .x12 0)),
  .plain (.basic (.arith (.rr .sub32 .x15 .x0 .x11))),
  .plain (.basic (.arith (.rr .shl .x13 .x13 .x15))),
  .plain (.basic (.arith (.rr .bitOr .x14 .x13 .x14))),
  .plain (.basic (.arith (.rr .shr .x10 .x10 .x11))),
  .plain (.basic (.arith (.addi .x13 .x0 9))),
  .plain (.basic (.branch .lt .x11 .x13 40)),
  .plain (.basic (.ld .x12 .x12 8)),
  .plain (.basic (.arith (.addi .x13 .x0 64))),
  .plain (.subPtr .x11 .x13 .x11),
  .plain (.basic (.arith (.rr .shl .x11 .x12 .x11))),
  .plain (.basic (.arith (.rr .bitOr .x10 .x11 .x10))),
  .plain (.basic (.jal .x0 16)),
  .plain (.basic (.arith (.srli .x10 .x10 3))),
  .plain (.basic (.arith (.rr .add .x10 .x10 .x19))),
  .plain (.basic (.ld .x10 .x10 0)),
  .plain (.basic (.arith (.addi .x11 .x24 120))),
  .plain (.basic (.arith (.srli .x12 .x11 3))),
  .plain (.andi .x12 .x12 4088),
  .plain (.basic (.arith (.rr .add .x12 .x12 .x19))),
  .plain (.basic (.ld .x15 .x12 0)),
  .plain (.andi .x13 .x11 63),
  .plain (.basic (.arith (.rr .shr .x11 .x15 .x11))),
  .plain (.basic (.branch .eq .x13 .x0 20)),
  .plain (.basic (.ld .x12 .x12 8)),
  .plain (.basic (.arith (.rr .sub32 .x13 .x0 .x13))),
  .plain (.basic (.arith (.rr .shl .x12 .x12 .x13))),
  .plain (.basic (.arith (.rr .bitOr .x11 .x12 .x11))),
  .plain (.basic (.arith (.addi .x12 .x24 184))),
  .plain (.basic (.arith (.srli .x13 .x12 3))),
  .plain (.andi .x13 .x13 4088),
  .plain (.basic (.arith (.rr .add .x13 .x13 .x19))),
  .plain (.basic (.ld .x16 .x13 0)),
  .plain (.andi .x15 .x12 63),
  .plain (.basic (.arith (.rr .shr .x12 .x16 .x12))),
  .plain (.basic (.arith (.addi .x16 .x0 27))),
  .plain (.basic (.branch .lt .x15 .x16 20)),
  .plain (.basic (.ld .x13 .x13 8)),
  .plain (.basic (.arith (.rr .sub32 .x15 .x0 .x15))),
  .plain (.basic (.arith (.rr .shl .x13 .x13 .x15))),
  .plain (.basic (.arith (.rr .bitOr .x12 .x13 .x12)))]

def lowerCode : Array Op := #[
  .plain (.basic (.arith (.srli .x10 .x24 3))),
  .plain (.andi .x10 .x10 4088),
  .plain (.basic (.arith (.rr .add .x5 .x10 .x19))),
  .plain (.basic (.ld .x10 .x5 0)),
  .plain (.basic (.ld .x15 .x9 0)),
  .plain (.andi .x6 .x24 63),
  .plain (.basic (.arith (.rr .shr .x10 .x10 .x24))),
  .plain (.basic (.arith (.addi .x16 .x24 64))),
  .plain (.basic (.arith (.addi .x17 .x24 128))),
  .plain (.basic (.branch .eq .x6 .x0 100)),
  .plain (.basic (.ld .x5 .x5 8)),
  .plain (.basic (.arith (.rr .sub32 .x7 .x0 .x6))),
  .plain (.basic (.arith (.srli .x16 .x16 3))),
  .plain (.andi .x16 .x16 4088),
  .plain (.basic (.arith (.rr .add .x16 .x16 .x19))),
  .plain (.basic (.ld .x28 .x16 0)),
  .plain (.basic (.ld .x16 .x16 8)),
  .plain (.basic (.arith (.rr .shl .x5 .x5 .x7))),
  .plain (.basic (.arith (.rr .bitOr .x10 .x5 .x10))),
  .plain (.basic (.arith (.rr .shr .x5 .x28 .x24))),
  .plain (.basic (.arith (.slli .x16 .x16 1))),
  .xori .x7 .x24 4095,
  .plain (.basic (.arith (.srli .x17 .x17 3))),
  .plain (.andi .x17 .x17 4088),
  .plain (.basic (.arith (.rr .add .x17 .x17 .x19))),
  .plain (.basic (.ld .x28 .x17 0)),
  .plain (.basic (.ld .x17 .x17 8)),
  .plain (.basic (.arith (.rr .shl .x16 .x16 .x7))),
  .plain (.basic (.arith (.rr .bitOr .x16 .x16 .x5))),
  .plain (.basic (.arith (.rr .shr .x5 .x28 .x24))),
  .plain (.basic (.arith (.slli .x17 .x17 1))),
  .plain (.basic (.arith (.rr .shl .x17 .x17 .x7))),
  .plain (.basic (.arith (.rr .bitOr .x17 .x17 .x5))),
  .plain (.basic (.jal .x0 28)),
  .plain (.basic (.arith (.srli .x16 .x16 3))),
  .plain (.basic (.arith (.rr .add .x16 .x16 .x19))),
  .plain (.basic (.ld .x16 .x16 0)),
  .plain (.basic (.arith (.srli .x17 .x17 3))),
  .plain (.basic (.arith (.rr .add .x17 .x17 .x19))),
  .plain (.basic (.ld .x17 .x17 0)),
  .plain (.basic (.arith (.addi .x24 .x24 192))),
  .plain (.basic (.arith (.lui .x5 1))),
  .plain (.subPtr .x5 .x8 .x5),
  .plain (.basic (.ld .x29 .x5 1728)),
  .plain (.basic (.arith (.rr .add .x5 .x29 .x15))),
  .plain (.basic (.arith (.srli .x7 .x24 3))),
  .plain (.andi .x28 .x7 4088),
  .plain (.basic (.arith (.rr .add .x28 .x28 .x19))),
  .plain (.basic (.ld .x7 .x28 0)),
  .plain (.basic (.arith (.addi .x5 .x5 3905))),
  .plain (.basic (.arith (.rr .bitAnd .x5 .x5 .x29))),
  .plain (.basic (.arith (.rr .add .x29 .x5 .x6))),
  .plain (.basic (.arith (.rr .shr .x7 .x7 .x6))),
  .plain (.basic (.arith (.addi .x30 .x0 65))),
  .plain (.basic (.branch .lt .x29 .x30 20)),
  .plain (.basic (.ld .x28 .x28 8)),
  .plain (.basic (.arith (.rr .sub32 .x6 .x0 .x6))),
  .plain (.basic (.arith (.rr .shl .x6 .x28 .x6))),
  .plain (.basic (.arith (.rr .bitOr .x7 .x6 .x7))),
  .plain (.basic (.arith (.addi .x6 .x0 256))),
  .plain (.basic (.arith (.rr .sub32 .x6 .x6 .x15))),
  .plain (.basic (.arith (.lui .x28 1))),
  .plain (.subPtr .x28 .x8 .x28),
  .plain (.basic (.ld .x28 .x28 1728)),
  .plain (.basic (.arith (.rr .bitAnd .x6 .x6 .x28))),
  .plain (.basic (.arith (.addi .x28 .x0 4095))),
  .plain (.basic (.arith (.rr .shr .x6 .x28 .x6))),
  .plain (.basic (.arith (.addi .x28 .x26 4088))),
  .plain (.basic (.arith (.rr .bitAnd .x6 .x7 .x6))),
  .plain (.basic (.arith (.addi .x7 .x0 11))),
  .plain (.basic (.branch .lt .x7 .x28 7776))]

def decode (base : Nat) (code : Array Op) (pc : Word) : Option Op :=
  let k:=((pc.toNat-4096)/4)-base
  if pc=CommitBlocks.addr (base+k) then code[k]? else none

def agree (base : Nat) (code : Array Op) :=
  ∀ i : Fin code.size, CheckDecode.same (decodeInstruction (Artifact.checkCode.get 32 ⟨(base+i.val)%796,by omega⟩)) (code[i.val]'i.isLt).instr=true

theorem decode_sound (base : Nat) (code : Array Op) (bound : base+code.size≤796) (exactWords : agree base code)
    (s : MachineState) (op : Op) (ok : decode base code s.pc=some op) : fetch image s=some op.instr := by
  unfold decode at ok;dsimp only at ok
  split at ok <;> try contradiction
  rename_i pc
  let k:=((s.pc.toNat-4096)/4)-base
  change code[k]?=some op at ok
  have lim : k<code.size := by by_contra h;simpa [h] using ok
  have eq : code[k]=op := by simpa [lim] using ok
  have f:=exactWords ⟨k,lim⟩
  have ix : (⟨(base+k)%796,Nat.mod_lt _ (by decide)⟩ : Fin 796)=⟨base+k,by omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  rw [eq,ix] at f
  rw [fetch_packed image Artifact.checkCode rfl (base+k) (by omega) (by omega) s pc]
  apply CheckDecode.same_sound f

theorem head_decoded : ∀ s : MachineState,∀ op,decode 122 headCode s.pc=some op→fetch image s=some op.instr := decode_sound 122 headCode (by decide) (by unfold agree;decide +kernel)
theorem lower_decoded : ∀ s : MachineState,∀ op,decode 280 lowerCode s.pc=some op→fetch image s=some op.instr := decode_sound 280 lowerCode (by decide) (by unfold agree;decide +kernel)

end CommitGolfCandidate.Reconstruction.CheckCursorImage
