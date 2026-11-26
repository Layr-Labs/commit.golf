import CommitGolfCandidate.TruncBFill
import CommitGolfCandidate.TruncUpper
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 180000

def byteAt (s : MachineState) (a : Nat) := s.getByte (BitVec.ofNat 64 a)
def digestAt (s : MachineState) (a : Nat) := readBuffer s a 32
def Separate (a n b m : Nat) := a+n ≤ b ∨ b+m ≤ a
def Quiet (s t : MachineState) (dst len : Nat) :=
  ∀ a, a<2^64 → Separate a 1 dst len → byteAt t a=byteAt s a

theorem byteMem {s t : MachineState} (m : t.mem=s.mem) (a : Nat) : byteAt t a=byteAt s a := by
  simp only [byteAt,MachineState.getByte,MachineState.getMem,m]

theorem quietDigest {s t : MachineState} {dst len : Nat} (q : Quiet s t dst len) (a : Nat)
    (b : a+32≤2^64) (sep : Separate a 32 dst len) : digestAt t a=digestAt s a := by
  unfold digestAt readBuffer
  apply congrArg (BitVec.ofNat 256);apply Finset.sum_congr rfl
  intro j hj
  have h:=Finset.mem_range.mp hj
  have e:=q (a+j) (by omega) (by unfold Separate at *;omega)
  change _ = _ at e; unfold byteAt at e;rw [e]

theorem quietCopy (s : MachineState) (src dst : Nat) (bounded : dst+32 ≤ 2^64) (aligned : dst%8=0) :
    Quiet s (copyAt s (BitVec.ofNat 64 src) (BitVec.ofNat 64 dst)) dst 32 := by
  intro a ba sep
  unfold byteAt MachineState.getByte
  apply congrArg (fun w => extractByte w _)
  unfold copyAt;apply opening_copy_memory_outside
  intro j eqn
  change alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 dst + BitVec.ofNat 64 (8*j.val) at eqn
  rw [PairCap.top_align_to_dword_of_nat a ba,← BitVec.ofNat_add] at eqn
  have e:=congrArg BitVec.toNat eqn
  have hj:=j.isLt
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*(a/8)<2^64),
      Nat.mod_eq_of_lt (by omega : dst+8*j.val<2^64)] at e
  unfold Separate at sep;omega

theorem quietHash (s : MachineState) (dst : Nat) (bounded : dst+32≤2^64) (d : Digest) :
    Quiet s (writeBits s (BitVec.ofNat 64 dst) d) dst 32 := by
  intro a ba sep;apply write_bits_byte_outside
  intro j hj eqn
  change j<32 at hj
  rw [← BitVec.ofNat_add] at eqn
  have e := congrArg BitVec.toNat eqn
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ba,Nat.mod_eq_of_lt (by omega)] at e
  unfold Separate at sep;omega

structure Written (s t : MachineState) (dst : Nat) (d : Digest) : Prop where
  atDst : digestAt t dst=d
  outside : Quiet s t dst 32

theorem copyWritten (s t : MachineState) (src dst : Nat)
    (m : t.mem=(copyAt s (BitVec.ofNat 64 src) (BitVec.ofNat 64 dst)).mem)
    (sa : src%8=0) (da : dst%8=0) (bs : src+32≤2^64) (bd : dst+32≤2^64) (sep : Separate src 32 dst 32) :
    Written s t dst (digestAt s src) := by
  refine ⟨(read_buffer_memory_congr _ _ m dst 32).trans (copyAtDigest s src dst sa da bs bd sep),?_⟩
  exact fun a ba e => (byteMem m a).trans (quietCopy s src dst bd da a ba e)

theorem hashWritten (s : MachineState) (dst : Nat) (reg : s.getReg .x24=BitVec.ofNat 64 dst)
    (bound : dst+32≤2^64) (d : Digest) : Written s (hashed s d) dst d := by
  have m : (hashSetupState s).mem=s.mem := rfl
  unfold hashed;rw [reg]
  refine ⟨?_,fun a ba sep => (quietHash _ dst bound d a ba sep).trans (byteMem m a)⟩
  have h:=write_bits_digest (hashSetupState s) dst 0 d (by decide) (by decide)
  simpa [digestAt] using h

end CommitGolfCandidate.Trunc.Batch
