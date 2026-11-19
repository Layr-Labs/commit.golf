import CommitGolfCandidate.WriteMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def withMemoryOrigin (origin : Word → Word) (s : MachineState) : MachineState :=
  { s with mem := fun a => if alignToDword a=a then s.mem a else origin a }

theorem align_idempotent (a : Word) : alignToDword (alignToDword a)=alignToDword a := by
  simp [alignToDword,BitVec.and_assoc]

@[simp] theorem origin_getReg (origin : Word → Word) (s : MachineState) (r : Reg) :
    (withMemoryOrigin origin s).getReg r=s.getReg r := by cases r <;> rfl

@[simp] theorem origin_pc (origin : Word → Word) (s : MachineState) :
    (withMemoryOrigin origin s).pc=s.pc := rfl

@[simp] theorem origin_getByte (origin : Word → Word) (s : MachineState) (a : Word) :
    (withMemoryOrigin origin s).getByte a=s.getByte a := by
  change extractByte (if alignToDword (alignToDword a)=alignToDword a then _ else _) _ = _
  rw [if_pos (align_idempotent a)]
  rfl

theorem origin_unaligned (origin : Word → Word) (s : MachineState) (a : Word)
    (ha : alignToDword a≠a) : (withMemoryOrigin origin s).mem a=origin a := by
  simp only [withMemoryOrigin,ha,ite_false]

theorem setByte_unaligned (s : MachineState) (a q : Word) (b : Byte)
    (hq : alignToDword q≠q) : (s.setByte a b).mem q=s.mem q := by
  have ne : q≠alignToDword a := by
    intro e
    apply hq
    rw [e,align_idempotent]
  simp only [MachineState.setByte,MachineState.setMem,beq_iff_eq,ne,ite_false]

theorem aligned_mod (a : Word) (ha : alignToDword a=a) : a.toNat%8=0 := by
  have low : alignToDword a &&& 7#64=0 := by
    simp [alignToDword,BitVec.and_assoc]
  rw [ha] at low
  have n := congrArg BitVec.toNat low
  rw [BitVec.toNat_and] at n
  change a.toNat &&& (2^3-1)=0 at n
  rwa [Nat.and_two_pow_sub_one_eq_mod] at n

theorem aligned_mem_eq (s t : MachineState) (bytes : ∀ a, s.getByte a=t.getByte a)
    (a : Word) (ha : alignToDword a=a) : s.mem a=t.mem a := by
  have reads : readBuffer s a.toNat 32=readBuffer t a.toNat 32 := by
    unfold readBuffer
    apply congrArg (BitVec.ofNat 256)
    apply Finset.sum_congr rfl
    intro i _
    rw [bytes]
  have word := (read_digest_word s a.toNat 0 (aligned_mod a ha) (by decide)).symm.trans
    ((congrArg (fun b : BitVec 256 => b.extractLsb' 0 64) reads).trans
      (read_digest_word t a.toNat 0 (aligned_mod a ha) (by decide)))
  simpa only [Nat.mul_zero,Nat.add_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq,MachineState.getMem] using word

theorem mem_eq_origin (origin : Word → Word) (s t : MachineState)
    (bytes : ∀ a, s.getByte a=t.getByte a)
    (frame : ∀ a, alignToDword a≠a → s.mem a=origin a) :
    s.mem=(withMemoryOrigin origin t).mem := by
  funext a
  by_cases ha : alignToDword a=a
  · change s.mem a=(if alignToDword a=a then t.mem a else origin a)
    rw [if_pos ha]
    exact aligned_mem_eq s t bytes a ha
  · change s.mem a=(if alignToDword a=a then t.mem a else origin a)
    rw [if_neg ha]
    exact frame a ha

end CommitGolfCandidate
