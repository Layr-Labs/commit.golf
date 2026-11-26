import CommitGolfCandidate.S5Scratch
import CommitGolfCandidate.S5ParentBuffers
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
attribute [local irreducible] readBuffer writeBits

def Keeps (s t : MachineState) := ∀ r : Reg, r≠.x6 → r≠.x10 → r≠.x12 → r≠.x31 → t.getReg r=s.getReg r
theorem keeps_trans {s t u} (a : Keeps s t) (b : Keeps t u) : Keeps s u :=
  fun r c d e f=>(b r c d e f).trans (a r c d e f)
theorem keeps_regs {s t} (all : ∀ r,t.getReg r=s.getReg r) : Keeps s t := fun r _ _ _ _=>all r

structure PairCtx (d : Height) (b : Nat) (s : MachineState) : Prop extends Common s where
  src : s.getReg .x21=BitVec.ofNat 64 (srcAddr d (2*b))
  dst : s.getReg .x22=BitVec.ofNat 64 (dstAddr d (2*b))
  ctr : s.getReg .x20=BitVec.ofNat 64 (tiles d-b)
  tag : s.getReg .x29=tagWord d 0
  mask : s.getReg .x30=heldMask d

theorem ctx_kept {d b s t} (c : PairCtx d b s) (k : Keeps s t) : PairCtx d b t := by
  obtain ⟨⟨q5,q11,q13,q18,q9,q24,q25,q26,q27⟩,q21,q22,q20,q29,q30⟩:=c
  constructor
  · constructor <;> apply (k _ (by decide) (by decide) (by decide) (by decide)).trans <;> assumption
  all_goals apply (k _ (by decide) (by decide) (by decide) (by decide)).trans <;> assumption

theorem chain_addresses {d b s} (ctx : PairCtx d b s) (i : Lane) :
    s.getReg .x21+signExtend12 (BitVec.ofNat 12 (fromLane i))=BitVec.ofNat 64 (srcAddr d (2*b+i.val)) ∧
    s.getReg .x21+signExtend12 (BitVec.ofNat 12 (fromLane i+64))=BitVec.ofNat 64 (tagAddr d (2*b+i.val)) ∧
    s.getReg .x22+signExtend12 (BitVec.ofNat 12 (toLane i))=BitVec.ofNat 64 (dstAddr d (2*b+i.val)) := by
  have imm := (by decide +kernel : ∀ j : Lane,
    signExtend12 (BitVec.ofNat 12 (fromLane j))=BitVec.ofNat 64 (fromLane j) ∧
    signExtend12 (BitVec.ofNat 12 (fromLane j+64))=BitVec.ofNat 64 (fromLane j+64) ∧
    signExtend12 (BitVec.ofNat 12 (toLane j))=BitVec.ofNat 64 (toLane j)) i
  rw [ctx.src,ctx.dst,imm.1,imm.2.1,imm.2.2,←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add]
  have bound:=i.isLt;unfold srcAddr tagAddr dstAddr rowAddress nodeAddress Late.gapOffset fromLane toLane
  simp only [Nat.succ_ne_zero,ite_false]
  constructor
  · apply congrArg (BitVec.ofNat 64);omega
  · constructor <;> apply congrArg (BitVec.ofNat 64) <;> omega

def outsideLane (d : Height) (p : Nat) (s t : MachineState) := ∀ a n,a+n≤MEMORY_BYTES →
  Apart a n (dstAddr d p) 32 → Apart a n (tagAddr d p) 8 → Apart a n scratchBase 96 →
  readBuffer t a n=readBuffer s a n

theorem outside_trans {d p s t u} (a : outsideLane d p s t) (b : outsideLane d p t u) : outsideLane d p s u :=
  fun addr n fit dst tag pad=>(b _ _ fit dst tag pad).trans (a _ _ fit dst tag pad)
theorem outside_mem {d p s t} (eq : t.mem=s.mem) : outsideLane d p s t :=
  fun a n _ _ _ _=>read_congr_mem t s a n eq

theorem outside_footprint {d p s t a n} (f : unchanged s t a n)
    (covers : ∀ x k, Apart x k (dstAddr d p) 32 → Apart x k (tagAddr d p) 8 →
      Apart x k scratchBase 96 → Apart x k a n) : outsideLane d p s t :=
  fun b k fit dst tag scratch=>f b k fit (covers b k dst tag scratch)

theorem three_calls (o : Oracle) (s : MachineState) (n : Nat) (srcReg dstReg : Reg) (a b : BitVec 12)
    (x y : Nat) (op0 : Site .commit n (.ADDI .x10 srcReg a)) (op1 : Site .commit (n+1) (.ADDI .x12 dstReg b))
    (op2 : Site .commit (n+2) .ECALL) (pc : s.pc=pcAt n) (c : Common s)
    (xs : (prepareCall s srcReg dstReg a b).getReg .x10=BitVec.ofNat 64 x)
    (ys : (prepareCall s srcReg dstReg a b).getReg .x12=BitVec.ofNat 64 y)
    (xr : x+96≤MEMORY_BYTES) (xa : x%8=0) (yr : y+32≤MEMORY_BYTES) (ya : y%8=0) :
    Runs .commit true o s (callState s srcReg dstReg a b (o.compression (readBuffer s x 96))) 3 10 1 := by
  have xb : x<2^64:=by change x+96≤2^36 at xr;omega
  have yb : y<2^64:=by change y+32≤2^36 at yr;omega
  intro fuel
  have h:=execute_compression s n fuel srcReg dstReg a b op0 op1 op2 pc c.mode c.len c.kind (by
    simp only [xs,ys,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt xb,Nat.mod_eq_of_lt yb,xr,yr,xa,ya,decide_true,and_self])
  have from_ : ((prepareCall s srcReg dstReg a b).getReg .x10).toNat=x := by rw [xs,BitVec.toNat_ofNat,Nat.mod_eq_of_lt xb]
  rw [h,from_];unfold Late.hash
  erw [oracle_run_public_bind o (.inl _)]
  simp only [oracle_run_bind,oracle_run_pure,pure_bind,bind_assoc,Nat.add_zero];rfl
end CommitGolfCandidate.S5Machine
