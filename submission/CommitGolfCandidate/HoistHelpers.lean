import CommitGolfCandidate.Execution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem hoist_pc_pc (state : MachineState) (first second : Word) :
    (state.setPC first).setPC second = state.setPC second := rfl

theorem hoist_pc_self (state : MachineState) : state.setPC state.pc = state := by
  cases state; rfl

theorem hoist_read_width (state : MachineState) (address kind : Nat) (zero : kind = 0) :
    BitVec.setWidth 512 (readBuffer state address
      (((if kind = 0 then 512 else PERMUTATION_WIDTH) + 7) / 8)) =
      readBuffer state address 64 := by
  subst kind
  exact BitVec.setWidth_eq _

theorem hoist_write_bits_pc {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (pc : Word) :
    writeBits (state.setPC pc) address answer =
      (writeBits state address answer).setPC (pc + 4) := by
  have byte_pc (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setPC pc).setByte a b = (s.setByte a b).setPC pc := by
    cases s; rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setPC pc) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setPC pc := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons, byte_pc] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  rfl

end CommitGolfCandidate
