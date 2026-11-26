import CommitGolfCandidate.LateOpenBlocks
import CommitGolfCandidate.LateLayout
import Mathlib.Data.Nat.Bitwise

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

inductive Test where | empty | depth | morePath | moreRecords | batch | moreCap | moreOverrides
deriving DecidableEq

def Test.start : Test → Nat
  | .empty=>14 | .depth=>17 | .morePath=>56 | .moreRecords=>59 | .batch=>61 | .moreCap=>89 | .moreOverrides=>128

def Test.target : Test → Nat
  | .empty=>60 | .depth=>19 | .morePath=>38 | .moreRecords=>19 | .batch=>135 | .moreCap=>68 | .moreOverrides=>108

def Test.args : Test → Reg × Reg
  | .empty => (.x27,.x0) | .depth => (.x27,.x6) | .morePath => (.x28,.x0)
  | .moreRecords => (.x27,.x0) | .batch => (.x16,.x6) | .moreCap | .moreOverrides => (.x28,.x0)

def Test.bits (b : Test) : BitVec 13 := BitVec.ofInt 13 (4*((b.target : Int)-(b.start : Int)))
def Test.instr (b : Test) := if b=.empty then Instr.BEQ b.args.1 b.args.2 b.bits else Instr.BNE b.args.1 b.args.2 b.bits
def Test.taken (b : Test) (s : MachineState) : Bool :=
  if b=.empty then s.getReg b.args.1 == s.getReg b.args.2 else s.getReg b.args.1 != s.getReg b.args.2
def Test.after (b : Test) (s : MachineState) :=
  s.setPC (pcAt (if b.taken s then b.target else b.start+1))

theorem test_run (b : Test) (s : MachineState) (pc : s.pc=pcAt b.start) : Runs s (b.after s) 1 1 := by
  have enc : decodeInstruction (openWord b.start)=some (.base b.instr) := by cases b <;> rfl
  have bound : b.start<140 := by cases b <;> decide
  have rs : Runs s (execInstrBr s b.instr) 1 1 := by
    have st : ordinaryStep s (.base b.instr)=some (execInstrBr s b.instr) := by cases b <;> rfl
    have cost : instructionCycles (.base b.instr)=1 := by cases b <;> rfl
    exact cost ▸ one _ bound _ enc s _ pc st
  have tgt : pcAt b.start+signExtend13 b.bits=pcAt b.target := by cases b <;> rfl
  have fall := pc_succ b.start
  have same : execInstrBr s b.instr = b.after s := by
    have choose (c : Bool) :
        (if c then s.setPC (s.pc+signExtend13 b.bits) else s.setPC (s.pc+4)) =
          s.setPC (pcAt (if c then b.target else b.start+1)) := by
      cases c <;> simp only [Bool.false_eq_true,if_false,if_true,pc,tgt,fall]
    by_cases eq : b=.empty
    · simp only [Test.instr,Test.after,Test.taken,if_pos eq]
      exact choose (s.getReg b.args.1 == s.getReg b.args.2)
    · simp only [Test.instr,Test.after,Test.taken,if_neg eq]
      exact choose (s.getReg b.args.1 != s.getReg b.args.2)
  exact same ▸ rs

theorem halt_run (s : MachineState) (pc : s.pc=pcAt 139)
    (mode : s.getReg .x5=1) (code : s.getReg .x10=0) (fuel : Nat) :
    execute image (fuel+1) s true = pure ⟨.success,s,1,0⟩ := by
  rw [execute,fetched 139 (by decide) .ECALL (by rfl) s pc,mode,code];rfl

theorem access_at (a : Nat) (range : a+8≤MEMORY_BYTES) (align : a%8=0) :
    accessValid (BitVec.ofNat 64 a) 8=true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a<2^64 by unfold MEMORY_BYTES at range;omega),
    range,align,decide_true,Bool.true_and]

private theorem zero_iff (n : Nat) (small : n<2^64) : BitVec.ofNat 64 n=0 ↔ n=0 := by
  constructor
  · intro e;have h:=congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at h;exact h
  · rintro rfl;rfl

theorem count_test (n : Nat) (small : n<2^64) : (BitVec.ofNat 64 n != (0 : Word))=decide (n≠0) := by
  by_cases z:n=0
  · subst n; rfl
  · have h := bne_iff_ne.mpr (fun e => z ((zero_iff _ small).mp e));simpa [z] using h

theorem decrement (n : Nat) (pos : 0<n) :
    BitVec.ofNat 64 n+18446744073709551615=BitVec.ofNat 64 (n-1) := by
  change BitVec.ofNat 64 n + (-1) = _
  rw [←BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) pos

theorem shifted (n k : Nat) : (BitVec.ofNat 64 n <<< k) = BitVec.ofNat 64 (n*2^k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_mod]

theorem shr (n k : Nat) (small : n<2^64) : (BitVec.ofNat 64 n >>> k) = BitVec.ofNat 64 (n/2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) small)]

theorem salt_ptr (i : Index) :
    BitVec.ofNat 64 rowBase + (((BitVec.ofNat 64 i.val <<< 1) + BitVec.ofNat 64 i.val) <<< 5) +
      (((BitVec.ofNat 64 i.val &&& 1) + 18446744073709551615) &&& 72) =
    BitVec.ofNat 64 (saltAddress i) := by
  have parity : BitVec.ofNat 64 i.val &&& 1 = BitVec.ofNat 64 (i.val%2) := by
    change BitVec.ofNat 64 i.val &&& BitVec.ofNat 64 (2^1-1) = _
    rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]
  rw [parity,shifted,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add]
  by_cases e : i.val%2=0
  · rw [e]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 72 = _
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64); unfold saltAddress;rw [if_pos e];omega
  · rw [show i.val%2=1 by omega]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 0 = _
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64); unfold saltAddress;rw [if_neg e];omega

theorem sibling_ptr (base i : Nat) (small : i<2^64) :
    BitVec.ofNat 64 base + (((BitVec.ofNat 64 i ^^^ 1) + (BitVec.ofNat 64 i >>> 1)) <<< 5) =
      BitVec.ofNat 64 (base+gapOffset (i ^^^ 1)) := by
  change BitVec.ofNat 64 base + (((BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 1)+ _) <<< 5) = _
  rw [shr _ _ small,←BitVec.ofNat_xor,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  unfold gapOffset
  by_cases even : i%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega

end CommitGolfCandidate.Late.Open
