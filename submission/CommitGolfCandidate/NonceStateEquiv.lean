import CommitGolfCandidate.Execution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

structure NonceStateEquiv (left right : MachineState) : Prop where
  pc : left.pc=right.pc
  registers : ∀ reg, left.getReg reg=right.getReg reg
  memory : ∀ address, address.toNat%8=0 → left.getMem address=right.getMem address

namespace NonceStateEquiv

theorem refl (state : MachineState) : NonceStateEquiv state state := ⟨rfl,fun _ => rfl,fun _ _ => rfl⟩

theorem aligned_address (address : Word) : (alignToDword address).toNat%8=0 := by
  have offset : byteOffset (alignToDword address)=0 := by
    simp only [byteOffset,alignToDword,BitVec.and_assoc]
    rw [show (~~~7#64) &&& 7#64=0#64 by decide]
    simp
  have numeric : byteOffset (alignToDword address)=(alignToDword address).toNat%8 := by
    unfold byteOffset
    rw [BitVec.toNat_and]
    change (alignToDword address).toNat &&& (2^3-1)=(alignToDword address).toNat%2^3
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  exact numeric.symm.trans offset

theorem byte (left right : MachineState) (related : NonceStateEquiv left right) (address : Word) :
    left.getByte address=right.getByte address := by
  unfold MachineState.getByte
  rw [related.memory _ (aligned_address address)]

theorem read_buffer (left right : MachineState) (related : NonceStateEquiv left right)
    (address count : Nat) : readBuffer left address count=readBuffer right address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  rw [byte left right related]

theorem set_pc (left right : MachineState) (related : NonceStateEquiv left right) (pc : Word) :
    NonceStateEquiv (left.setPC pc) (right.setPC pc) :=
  ⟨rfl,fun reg => by simpa only [MachineState.getReg_setPC] using related.registers reg,
    fun address aligned => related.memory address aligned⟩

theorem set_reg (left right : MachineState) (related : NonceStateEquiv left right)
    (reg : Reg) (value : Word) : NonceStateEquiv (left.setReg reg value) (right.setReg reg value) := by
  refine ⟨by simpa only [MachineState.pc_setReg] using related.pc,?_,?_⟩
  · intro query
    by_cases equal : reg=query
    · subst query
      by_cases zero : reg=.x0
      · subst reg
        rfl
      · rw [MachineState.getReg_setReg_eq zero,MachineState.getReg_setReg_eq zero]
    · rw [MachineState.getReg_setReg_ne _ _ _ _ equal,MachineState.getReg_setReg_ne _ _ _ _ equal]
      exact related.registers query
  · intro address aligned
    cases reg <;> exact related.memory address aligned

private theorem get_reg_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg=state.getReg reg := by
  cases reg <;> rfl

theorem set_mem (left right : MachineState) (related : NonceStateEquiv left right)
    (address value : Word) : NonceStateEquiv (left.setMem address value) (right.setMem address value) := by
  refine ⟨by simpa only [MachineState.pc_setMem] using related.pc,?_,?_⟩
  · intro reg
    rw [get_reg_set_mem,get_reg_set_mem]
    exact related.registers reg
  · intro query aligned
    by_cases equal : query=address
    · subst query
      rw [MachineState.getMem_setMem_eq,MachineState.getMem_setMem_eq]
    · rw [MachineState.getMem_setMem_ne equal,MachineState.getMem_setMem_ne equal]
      exact related.memory query aligned

theorem set_byte (left right : MachineState) (related : NonceStateEquiv left right)
    (address : Word) (value : Byte) : NonceStateEquiv (left.setByte address value) (right.setByte address value) := by
  unfold MachineState.setByte
  dsimp only
  rw [related.memory _ (aligned_address address)]
  exact set_mem left right related _ _

end NonceStateEquiv
end CommitGolfCandidate
