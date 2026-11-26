import CommitGolfCandidate.S5MaskMemory
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] readBuffer
theorem write_frame {bits : Nat} (state : MachineState) (address : Word) (answer : BitVec bits) :
    writeBits state address answer =
      { state with mem := (writeBits state address answer).mem, pc := state.pc+4 } := by
  let put (s : MachineState) (i : Nat) := s.setByte (address + BitVec.ofNat 64 i)
      (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))
  have onlyMemory (is : List Nat) (s : MachineState) :
      is.foldl put s = { s with mem := (is.foldl put s).mem } := by
    induction is generalizing s with
    | nil => rfl
    | cons i rest ih => exact ih (put s i)
  unfold writeBits
  change ((List.range ((bits+7)/8)).foldl put state).setPC (state.pc+4) = _
  rw [onlyMemory (List.range ((bits+7)/8)) state]
  rfl

theorem clearedReply (d : Height) (w : wireWidth d=240) (s : MachineState) (a : Nat) (v : Output) (aligned : a%8=0) (bound : a+32≤2^64) :
    (writeBits s (BitVec.ofNat 64 a) v).setHalfword (BitVec.ofNat 64 (a+30)) 0=
    writeBits s (BitVec.ofNat 64 a) (storeReply d v) := by
  have h:=clear_reply_memory d w s a v aligned bound
  have f:=write_frame s (BitVec.ofNat 64 a) v
  have g:=write_frame s (BitVec.ofNat 64 a) (storeReply d v)
  generalize writeBits s (BitVec.ofNat 64 a) v=raw at h f ⊢
  generalize writeBits s (BitVec.ofNat 64 a) (storeReply d v)=out at h g ⊢
  cases s;cases raw;cases out
  simp only [MachineState.mk.injEq] at f g
  simp only [MachineState.setHalfword,MachineState.setMem,MachineState.mk.injEq] at h ⊢
  simp_all

theorem masked_reply_step (d : Height) (width : wireWidth d=240) (state : MachineState) (base : Nat) (answer : BitVec 256)
    (dest : state.getReg .x12 = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (bound : base + 32 ≤ 2^64) :
    execInstrBr (writeBits state (state.getReg .x12) answer) (.SH .x12 .x0 30) =
      (writeBits state (state.getReg .x12) (storeReply d answer)).setPC (state.pc+8) := by
  have clear := clear_reply_memory d width state base answer aligned bound
  change ((writeBits state (state.getReg .x12) answer).setHalfword
      ((writeBits state (state.getReg .x12) answer).getReg .x12 + signExtend12 30)
      0).setPC ((writeBits state (state.getReg .x12) answer).pc + 4) = _
  rw [writeBits_register, dest]
  change (((writeBits state (BitVec.ofNat 64 base) answer).setHalfword
      (BitVec.ofNat 64 base + BitVec.ofNat 64 30) 0).setPC _) = _
  rw [← BitVec.ofNat_add]
  have rawFrame := write_frame state (BitVec.ofNat 64 base) answer
  have padFrame := write_frame state (BitVec.ofNat 64 base) (storeReply d answer)
  generalize writeBits state (BitVec.ofNat 64 base) answer = raw at clear rawFrame ⊢
  generalize writeBits state (BitVec.ofNat 64 base) (storeReply d answer) = padded at clear padFrame ⊢
  cases state
  cases raw
  cases padded
  simp only [MachineState.mk.injEq] at rawFrame padFrame
  simp only [MachineState.setPC, MachineState.setHalfword, MachineState.setMem,
    MachineState.mk.injEq] at clear ⊢
  simp_all [BitVec.add_assoc]

end CommitGolfCandidate.S5Machine
