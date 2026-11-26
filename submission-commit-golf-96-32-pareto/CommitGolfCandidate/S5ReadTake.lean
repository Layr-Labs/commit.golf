import CommitGolfCandidate.S5ReadFill
import CommitGolfCandidate.S5CheckCalc
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Check (Flow)
open Check.Sym (Calc compiled evaluated)
def extractOps : List Calc := [.addi .x7 .x0 64,.sub .x7 .x7 .x6,.sll .x28 .x21 .x7,.srl .x28 .x28 .x7,
  .sll .x28 .x28 .x29,.bor .x30 .x30 .x28,.srl .x21 .x21 .x6,.sub .x22 .x22 .x6,.add .x29 .x29 .x6,.sub .x31 .x31 .x6]
private theorem extraction_sites : Check.Sym.Listed extractOps 47:=by decide +kernel
private theorem shamt (n : Nat) (bound : n<64) : (W n).toNat%64=n:=by
  rw [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n<2^64 by omega),Nat.mod_eq_of_lt bound]
private theorem word_sub (a b : Nat) (small : b<2^64) (inside : b≤a) : W a-W b=W (a-b):=BitVec.ofNat_sub_ofNat_of_le _ _ small inside

structure Taken (o : Oracle) (s t : MachineState) (base bytes v bit k off width left : Nat) : Prop where
  run : Flow o s t 11 0
  pc : t.pc=pcAt 34
  cursor : Cursor t base bytes v (bit+off+width) (k-width)
  pending : (t.getReg .x30).toNat=window v bit (off+width)
  offset : t.getReg .x29=W (off+width)
  left : t.getReg .x31=W (left-width)
  mem : t.mem=s.mem
  keep : ∀ q,q∉([.x7,.x21,.x22,.x28,.x29,.x30,.x31] : List Reg)→t.getReg q=s.getReg q

theorem extract (o : Oracle) (s : MachineState) (base bytes v bit k off width left : Nat)
    (pos : 0<width) (sm : width≤32) (inbuf : width≤k) (kmax : k<width+8) (inside : off+width≤64)
    (remaining : width≤left) (pc : s.pc=pcAt 47) (c : Cursor s base bytes v (bit+off) k)
    (amount : s.getReg .x6=W width) (used : s.getReg .x29=W off) (count : s.getReg .x31=W left)
    (low : (s.getReg .x30).toNat=window v bit off) : ∃ t,Taken o s t base bytes v bit k off width left := by
  let u:=evaluated extractOps s
  obtain ⟨run,regs,mem,ip⟩:=compiled o extractOps 47 s pc extraction_sites (by change ∀ e∈([] : List (Check.Sym.Expr×Nat)),_;simp)
  let t:=u.setPC (pcAt 34)
  have jump : ordinaryStep u (.base (.JAL .x0 2097060))=some t := by
    change some (u.setPC (u.pc+signExtend21 2097060))=some t;rw [show u.pc=pcAt 57 from ip];rfl
  have back:=Check.one_flow o (show u.pc=pcAt 57 from ip) (Check.known (by decide +kernel)) (i:=.JAL .x0 2097060) jump
  have preserved (q : Reg) (safe : q∉([.x7,.x21,.x22,.x28,.x29,.x30,.x31] : List Reg)) : t.getReg q=s.getReg q := by
    apply MachineState.getReg_setPC.trans;apply (regs q).trans;cases q <;> first | rfl | (exfalso;apply safe;decide)
  have cutoff : (64#64-s.getReg .x6).toNat%64=64-width:=by rw [amount,show 64#64-W width=W (64-width) from word_sub 64 width (by omega) (by omega),shamt _ (by omega)]
  have stepWidth : (s.getReg .x6).toNat%64=width:=by rw [amount,shamt _ (by omega)]
  have stepOff : (s.getReg .x29).toNat%64=off:=by rw [used,shamt _ (by omega)]
  let smallWord:=(s.getReg .x21 <<< (64-width)) >>> (64-width)
  obtain ⟨smallValue,highValue⟩:=take_window (s.getReg .x21) v (bit+off) k width (by omega) inbuf c.buf
  have joined :=Writer.joined_word (s.getReg .x30) smallWord off (low ▸ Nat.mod_lt _ (Nat.two_pow_pos _))
  have nextLow : t.getReg .x30=W (window v bit (off+width)) := by
    apply MachineState.getReg_setPC.trans;apply (regs .x30).trans
    change s.getReg .x30 ||| (((s.getReg .x21 <<< ((64#64-s.getReg .x6).toNat%64)) >>> ((64#64-s.getReg .x6).toNat%64)) <<< ((s.getReg .x29).toNat%64))=_
    rw [cutoff,stepOff,joined,low,show smallWord.toNat=_ from smallValue,append_window];rfl
  have rest : (t.getReg .x21).toNat=window v (bit+off+width) (k-width) := by
    have val : t.getReg .x21=s.getReg .x21 >>> ((s.getReg .x6).toNat%64):=MachineState.getReg_setPC.trans (regs .x21)
    rw [val,stepWidth];exact highValue
  have rem : t.getReg .x22=W (k-width) := by
    apply MachineState.getReg_setPC.trans;apply (regs .x22).trans;change s.getReg .x22-s.getReg .x6=_
    rw [c.count,amount];exact word_sub _ _ (by omega) inbuf
  have same : bit+off+width+(k-width)=bit+off+k:=by omega
  have cur : Cursor t base bytes v (bit+off+width) (k-width) := by
    refine ⟨?_,(preserved _ (by decide)).trans c.end_,rem,rest,?_,c.input.same mem⟩
    · rw [same];exact (preserved _ (by decide)).trans c.ptr
    · rw [same];exact c.whole
  refine ⟨t,⟨run.trans back,rfl,cur,?_,?_,?_,mem,preserved⟩⟩
  · rw [nextLow,W,BitVec.toNat_ofNat];apply Nat.mod_eq_of_lt
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos (off+width))) (Nat.pow_le_pow_right (by decide) inside)
  · apply MachineState.getReg_setPC.trans;apply (regs .x29).trans;change s.getReg .x29+s.getReg .x6=_
    rw [used,amount];exact (BitVec.ofNat_add ..).symm
  · apply MachineState.getReg_setPC.trans;apply (regs .x31).trans;change s.getReg .x31-s.getReg .x6=_
    rw [count,amount];exact word_sub _ _ (by omega) remaining
end CommitGolfCandidate.S5Machine.Reader
