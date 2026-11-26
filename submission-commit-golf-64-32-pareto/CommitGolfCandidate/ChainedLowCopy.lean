import CommitGolfCandidate.ChainedFieldDescriptor

/-! Repeated straight-line copies, including safe forward in-place compaction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

@[irreducible] def lowCopyState : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => lowCopyState n (byteCopyPrefix s 4)

theorem low_copy_zero (s : MachineState) : lowCopyState 0 s=s := by unfold lowCopyState; rfl
theorem low_copy_succ (n : Nat) (s : MachineState) :
    lowCopyState (n+1) s=lowCopyState n (byteCopyPrefix s 4) := by
  conv => lhs; unfold lowCopyState

theorem byte_offset_succ (base : Word) (index : Nat) :
    (base+1)+BitVec.ofNat 64 index=base+BitVec.ofNat 64 (index+1) := by
  change (base+BitVec.ofNat 64 1)+BitVec.ofNat 64 index=_
  rw [byte_offset_add,Nat.add_comm 1]

def CopyAhead (source destination : Word) (count : Nat) : Prop :=
  ∀ (index : Nat), index ≤ count → ∀ (written : Nat), written < index →
    source+BitVec.ofNat 64 index≠destination+BitVec.ofNat 64 written

theorem copy_ahead_shift (source destination : Word) (count : Nat)
    (ahead : CopyAhead source destination (count+1)) : CopyAhead (source+1) (destination+1) count := by
  intro index inside written before
  rw [byte_offset_succ,byte_offset_succ]
  exact ahead (index+1) (by omega) (written+1) (by omega)

theorem low_copy_source (n : Nat) (s : MachineState) :
    (lowCopyState n s).getReg .x5=s.getReg .x5+BitVec.ofNat 64 n := by
  induction n generalizing s with
  | zero => simp [low_copy_zero]
  | succ n ih => rw [low_copy_succ,ih,byte_copy_source,byte_offset_succ]

theorem low_copy_destination (n : Nat) (s : MachineState) :
    (lowCopyState n s).getReg .x6=s.getReg .x6+BitVec.ofNat 64 n := by
  induction n generalizing s with
  | zero => simp [low_copy_zero]
  | succ n ih => rw [low_copy_succ,ih,byte_copy_destination,byte_offset_succ]

theorem low_copy_frame (n : Nat) (s : MachineState) (reg : Reg) (source : reg≠.x5)
    (destination : reg≠.x6) (temporary : reg≠.x11) : (lowCopyState n s).getReg reg=s.getReg reg := by
  induction n generalizing s with
  | zero => rw [low_copy_zero]
  | succ n ih => rw [low_copy_succ,ih,byte_copy_frame s reg source destination temporary]

theorem low_copy_pc (n : Nat) (s : MachineState) : (lowCopyState n s).pc=s.pc+BitVec.ofNat 64 (16*n) := by
  induction n generalizing s with
  | zero => simp [low_copy_zero]
  | succ n ih =>
    rw [low_copy_succ,ih,byte_copy_pc s 4 (by decide)]
    change (s.pc+BitVec.ofNat 64 16)+BitVec.ofNat 64 (16*n)=_
    rw [byte_offset_add]
    congr 2
    omega

theorem native_low_copy_plan (bytes : Proof) (s : MachineState)
    (memory : BytesAt s (s.getReg .x5) bytes)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) bytes.length) (query : Word) :
    (lowCopyState bytes.length s).getByte query=writeByteList s.getByte (s.getReg .x6) bytes query := by
  induction bytes generalizing s with
  | nil => rw [List.length_nil,low_copy_zero]; rfl
  | cons byte bytes ih =>
    have first : s.getByte (s.getReg .x5)=byte := by simpa using memory 0 (by simp)
    have nextMemory : BytesAt (byteCopyPrefix s 4) ((byteCopyPrefix s 4).getReg .x5) bytes := by
      intro index inside
      rw [byte_copy_source,byte_copy_byte,byte_offset_succ]
      have different : s.getReg .x5+BitVec.ofNat 64 (index+1)≠s.getReg .x6 := by
        simpa using ahead (index+1) (by simp only [List.length_cons]; omega) 0 (by omega)
      rw [ite_eq_right different]
      simpa using memory (index+1) (by simpa using inside)
    have nextAhead : CopyAhead ((byteCopyPrefix s 4).getReg .x5) ((byteCopyPrefix s 4).getReg .x6) bytes.length := by
      rw [byte_copy_source,byte_copy_destination]
      exact copy_ahead_shift _ _ _ ahead
    have result := ih (byteCopyPrefix s 4) nextMemory nextAhead
    have stepMemory : (byteCopyPrefix s 4).getByte=storeByteFn s.getByte (s.getReg .x6) byte := by
      funext address
      rw [byte_copy_byte,first]
      rfl
    rw [stepMemory,byte_copy_destination] at result
    rw [List.length_cons,low_copy_succ]
    exact result

def LowCopyAt (image : Image) (base : Word) (count : Nat) : Prop :=
  ∀ index, index<count → ByteCopyAt image (base+BitVec.ofNat 64 (16*index))

def LowCopyReady : Nat → MachineState → Prop
  | 0,_ => True
  | n+1,s => accessValid (s.getReg .x5) 1=true ∧ accessValid (s.getReg .x6) 1=true ∧
      LowCopyReady n (byteCopyPrefix s 4)

theorem low_copy_execution (image : Image) (base : Word) (n : Nat) (code : LowCopyAt image base n)
    (s : MachineState) (pc : s.pc=base) (ready : LowCopyReady n s) (fuel : Nat) (coins : Bool) :
    execute image (4*n+fuel) s coins=
      (do let result ← execute image fuel (lowCopyState n s) coins
          return result.charge (4*n) 0) := by
  induction n generalizing base s with
  | zero => simp [low_copy_zero,Execution.charge]
  | succ n ih =>
    have firstCode : ByteCopyAt image base := by simpa using code 0 (by omega)
    have nextCode : LowCopyAt image (base+16) n := by
      intro index inside
      have result := code (index+1) (by omega)
      have location : (base+16)+BitVec.ofNat 64 (16*index)=base+BitVec.ofNat 64 (16*(index+1)) := by
        change (base+BitVec.ofNat 64 16)+BitVec.ofNat 64 (16*index)=_
        rw [byte_offset_add]
        congr 2
        omega
      rw [location]
      exact result
    have nextPC : (byteCopyPrefix s 4).pc=base+16 := by rw [byte_copy_pc s 4 (by decide),pc]; rfl
    have count : 4*(n+1)+fuel=4+(4*n+fuel) := by omega
    rw [count,byte_copy_execution image base firstCode s pc ready.1 ready.2.1,
      ih (base+16) nextCode (byteCopyPrefix s 4) nextPC ready.2.2,low_copy_succ]
    simp [Execution.charge,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
