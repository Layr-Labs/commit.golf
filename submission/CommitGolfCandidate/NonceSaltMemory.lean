import CommitGolfCandidate.NonceSaltExecution
import CommitGolfCandidate.Memory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem nonce_memory_reg (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by cases reg <;> rfl

private theorem nonce_memory_word (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query=(if query=address then value else state.getMem query) := by
  simp [MachineState.getMem,MachineState.setMem]

theorem nonce_separate_words (left right i j : Nat)
    (leftBound : left+32 ≤ 2^64) (rightBound : right+32 ≤ 2^64)
    (iBound : i < 4) (jBound : j < 4)
    (separate : left+32 ≤ right ∨ right+32 ≤ left) :
    BitVec.ofNat 64 (left+8*i) ≠ BitVec.ofNat 64 (right+8*j) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : left+8*i < 2^64),
    Nat.mod_eq_of_lt (by omega : right+8*j < 2^64)] at natural
  rcases separate with before | after <;> omega

def readNonce (state : MachineState) (address : Nat) : BitVec 256 :=
  expandNonce192 ((readBuffer state address 32).extractLsb' 0 192)

private theorem nonce_group_words (a b c d : Word) :
    (((a++b)++c)++d)=a++((b++c)++d) := by
  calc
    (((a++b)++c)++d : BitVec 256) = ((a++b)++(c++d) : BitVec 256) :=
      BitVec.append_assoc (x₁:=a++b) (x₂:=c) (x₃:=d)
    _ = (a++(b++(c++d)) : BitVec 256) :=
      BitVec.append_assoc (x₁:=a) (x₂:=b) (x₃:=c++d)
    _ = _ := congrArg (fun value : BitVec 192 => a++value)
      (BitVec.append_assoc (x₁:=b) (x₂:=c) (x₃:=d)).symm

theorem nonce_pad_words (w0 w1 w2 w3 : Word) :
    expandNonce192 (((((w3++w2)++w1)++w0) : BitVec 256).extractLsb' 0 192)=
      (((0#64++w2)++w1)++w0) := by
  rw [nonce_group_words,BitVec.extractLsb'_append_eq_right]
  change (((w2++w1)++w0).setWidth 256)=_
  rw [BitVec.setWidth_eq_append (by decide : 192≤256)]
  exact (nonce_group_words 0 w2 w1 w0).symm

theorem nonce_salt_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4,address≠state.getReg .x10+BitVec.ofNat 64 (8*word.val)) :
    (nonceSaltState state).getMem address=state.getMem address := by
  have a0 : address≠state.getReg .x10 := by simpa using outside ⟨0,by decide⟩
  have a1 : address≠state.getReg .x10+8#64 := outside ⟨1,by decide⟩
  have a2 : address≠state.getReg .x10+16#64 := outside ⟨2,by decide⟩
  have a3 : address≠state.getReg .x10+24#64 := outside ⟨3,by decide⟩
  simp [nonceSaltState,nonceSaltPrefix,nonceSaltInstructions,execInstrBr,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,nonce_memory_reg,
    nonce_memory_word,signExtend12,a0,a1,a2,a3]

theorem nonce_salt_memory (state : MachineState)
    (separated : ∀ source : Fin 3,∀ destination : Fin 4,
      state.getReg .x18+BitVec.ofNat 64 (8*source.val)≠
        state.getReg .x10+BitVec.ofNat 64 (8*destination.val)) (word : Fin 4) :
    (nonceSaltState state).getMem (state.getReg .x10+BitVec.ofNat 64 (8*word.val))=
      if word.val<3 then state.getMem (state.getReg .x18+BitVec.ofNat 64 (8*word.val)) else 0 := by
  have h10 : state.getReg .x18+8#64≠state.getReg .x10 := by
    simpa using separated ⟨1,by decide⟩ ⟨0,by decide⟩
  have h20 : state.getReg .x18+16#64≠state.getReg .x10 := by
    simpa using separated ⟨2,by decide⟩ ⟨0,by decide⟩
  have h21 : state.getReg .x18+16#64≠state.getReg .x10+8#64 := separated ⟨2,by decide⟩ ⟨1,by decide⟩
  fin_cases word <;>
    simp [nonceSaltState,nonceSaltPrefix,nonceSaltInstructions,execInstrBr,
      MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,nonce_memory_reg,
      signExtend12,h10,h20,h21]
  rfl

theorem nonce_salt_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x18=BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x10=BitVec.ofNat 64 destination)
    (sourceAligned : source%8=0) (destinationAligned : destination%8=0)
    (sourceBound : source+32≤2^64) (destinationBound : destination+32≤2^64)
    (separate : source+32≤destination ∨ destination+32≤source) :
    readBuffer (nonceSaltState state) destination 32=readNonce state source := by
  have copied (word : Fin 4) := nonce_salt_memory state (by
    intro i j
    rw [sourcePointer,destinationPointer,←BitVec.ofNat_add,←BitVec.ofNat_add]
    exact nonce_separate_words source destination i.val j.val sourceBound destinationBound
      (by omega) j.isLt separate) word
  have w0 := copied ⟨0,by decide⟩
  have w1 := copied ⟨1,by decide⟩
  have w2 := copied ⟨2,by decide⟩
  have w3 := copied ⟨3,by decide⟩
  simp only [sourcePointer,destinationPointer,←BitVec.ofNat_add] at w0 w1 w2 w3
  norm_num only [Nat.reduceMul,Nat.add_zero,ite_true,ite_false] at w0 w1 w2 w3
  rw [read_digest_words _ _ destinationAligned,w0,w1,w2,w3]
  unfold readNonce
  rw [read_digest_words _ _ sourceAligned,nonce_pad_words]
  rfl

theorem nonce_salt_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x10=BitVec.ofNat 64 destination)
    (aligned : address%8=0) (destinationBound : destination+32≤2^64) (readBound : address+32≤2^64)
    (separate : address+32≤destination ∨ destination+32≤address) :
    readBuffer (nonceSaltState state) address 32=readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply nonce_salt_memory_outside
  intro j
  rw [destinationPointer,←BitVec.ofNat_add]
  exact nonce_separate_words address destination i j.val readBound destinationBound hi j.isLt separate

theorem nonce_read_buffer_memory_congr (left right : MachineState) (same : left.mem=right.mem)
    (address count : Nat) : readBuffer left address count=readBuffer right address count := by
  simp only [readBuffer,MachineState.getByte,MachineState.getMem,same]

theorem nonce_read_memory_congr (left right : MachineState) (same : left.mem=right.mem)
    (address : Nat) : readNonce left address=readNonce right address := by
  unfold readNonce
  rw [nonce_read_buffer_memory_congr left right same]

end CommitGolfCandidate
