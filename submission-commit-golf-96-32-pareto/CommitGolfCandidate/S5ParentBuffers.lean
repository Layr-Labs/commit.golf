import CommitGolfCandidate.S5PassEntry
import CommitGolfCandidate.S5NodeFrame
import CommitGolfCandidate.S5Operations
import CommitGolfCandidate.S5InputBlock
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64

def srcAddr (h : Height) (p : Nat) :=rowAddress h.val p
def dstAddr (h : Height) (p : Nat) :=nodeAddress (h.val+1) p

theorem buffers {h : Height} {p : Nat} (hp : p<count h) :
    srcAddr h p+96≤MEMORY_BYTES ∧ srcAddr h p%8=0 ∧ dstAddr h p+32≤MEMORY_BYTES ∧ dstAddr h p%8=0 := by
  have limit:=row_after h.val p h.isLt hp
  have padded:=padded_region (h.val+1)
  have fits : srcAddr h p+96≤rowBase := by change rowAddress _ _+96≤rowBase;omega
  exact ⟨fits.trans (by decide),rowAligned ..,(parent_below_salts _ _ hp).trans (by decide),nodeAligned ..⟩

theorem written (s : MachineState) (a : Nat) (v : Output) :
    readBuffer (writeBits s (BitVec.ofNat 64 a) v) a 32=v := by
  simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] using write_bits_digest s a 0 v (by decide) (by decide)

structure Addr (s : MachineState) (h : Height) (p : Nat) (f t : BitVec 12) : Prop where
  src : s.getReg .x21+signExtend12 f=BitVec.ofNat 64 (srcAddr h p)
  dst : s.getReg .x22+signExtend12 t=BitVec.ofNat 64 (dstAddr h p)
theorem ready_addr {s h p f t} (a : Addr s h p f t) :
    let r:=prepareCall s .x21 .x22 f t
    r.getReg .x10=BitVec.ofNat 64 (srcAddr h p) ∧ r.getReg .x12=BitVec.ofNat 64 (dstAddr h p) :=
  ⟨(call_addresses s .x21 .x22 f t (by decide)).1.trans a.src,(call_addresses s .x21 .x22 f t (by decide)).2.trans a.dst⟩
end CommitGolfCandidate.S5Machine
