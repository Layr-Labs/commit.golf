import CommitGolfCandidate.LateCheckObs
import CommitGolfCandidate.LateCallState
import CommitGolfCandidate.LateOpenPathModel

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W AddrOK wordAt)

def High (s t : MachineState) := ∀ a n, 448≤a → a+n≤MEMORY_BYTES → readBuffer t a n=readBuffer s a n

theorem High.trans {s t u : MachineState} (h : High s t) (j : High t u) : High s u :=
  fun a n lo hi => (j a n lo hi).trans (h a n lo hi)

theorem High.memory {s t : MachineState} (mem : t.mem=s.mem) : High s t :=
  fun a n _ _ => read_congr_mem t s a n mem

theorem High.word {s t : MachineState} (h : High s t) (a : Nat) (al : a%8=0) (lo : 448≤a)
    (hi : a+8≤MEMORY_BYTES) : wordAt t a=wordAt s a := by
  have same:=h a 8 lo hi
  have eq (m : MachineState) : wordAt m a=readBuffer m a 8 :=
    (read_digest_word m a 0 al (by decide)).symm.trans (read_buffer_slice m a 32 0 8 (by decide))
  exact (eq t).trans (same.trans (eq s).symm)

theorem high_write {s t : MachineState} {a n : Nat} (h : Open.Outside s t a n)
    (al : a%8=0) (sz : n%8=0) (low : a+n≤448) : High s t :=
  fun q l lo hi => Open.outside_read h al sz q l hi (Or.inr (by omega))

inductive Op where | first | middle | last | final deriving DecidableEq
def Op.pc : Op → Nat | .first=>387 | .middle=>409 | .last=>412 | .final=>427
def Op.src : Op → Reg | .first | .last=>.x8 | .middle | .final=>.x0
def Op.dst : Op → Reg | .first=>.x0 | .middle | .last=>.x7 | .final=>.x21
def Op.a : Op → BitVec 12 | .first=>0 | .middle=>352 | .last | .final=>160
def Op.b : Op → BitVec 12 | .first=>352 | .last=>32 | _=>0

structure Mode (s : MachineState) : Prop where
  select : s.getReg .x5=0
  kind : s.getReg .x13=0
  width : s.getReg .x11=96

private theorem code (op : Op) :
    decodeInstruction (checkWord op.pc)=some (.base (.ADDI .x10 op.src op.a)) ∧
    decodeInstruction (checkWord (op.pc+1))=some (.base (.ADDI .x12 op.dst op.b)) ∧
    decodeInstruction (checkWord (op.pc+2))=some (.base .ECALL) := by
  cases op <;> exact ⟨rfl,rfl,rfl⟩

def result (op : Op) (s : MachineState) (ans : Digest) := callState s op.src op.dst op.a op.b ans

structure CallResult (o : Oracle) (op : Op) (s t : MachineState) (src dst : Nat) : Prop where
  runs : Normal.Runs o s t 3 1
  pc : t.pc=pcAt (op.pc+3)
  mem : t.mem=(store s dst (o.compression (readBuffer s src 96))).mem
  keep : ∀ r, .x10≠r → .x12≠r → t.getReg r=s.getReg r
  dest : t.getReg .x12=W dst

theorem doCall (o : Oracle) (op : Op) (s : MachineState) (src dst : Nat) (pc : s.pc=pcAt op.pc)
    (mode : Mode s) (sp : s.getReg op.src+signExtend12 op.a=W src) (dp : s.getReg op.dst+signExtend12 op.b=W dst)
    (sa : AddrOK src 96) (da : AddrOK dst 32) :
    CallResult o op s (result op s (o.compression (readBuffer s src 96))) src dst := by
  let u:=execInstrBr s (.ADDI .x10 op.src op.a)
  let r:=prepareCall s op.src op.dst op.a op.b
  let ans:=o.compression (readBuffer s src 96)
  have bound : op.pc+2<433 := by cases op <;> decide
  obtain ⟨a,b,c⟩:=code op
  have pc1 : u.pc=pcAt (op.pc+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have pc2 : r.pc=pcAt (op.pc+2) := by change u.pc+4=_;rw [pc1,pc_succ (op.pc+1)]
  have first : Runs s u 1 1 := one _ (by omega) _ a _ _ pc rfl
  have next : Runs u r 1 1 := one _ (by omega) _ b _ _ pc1 rfl
  have indep : Reg.x10≠op.dst := by cases op <;> decide
  obtain ⟨src',dst'⟩:=call_addresses s op.src op.dst op.a op.b indep
  have rs : r.getReg .x10=W src := src'.trans sp
  have rd : r.getReg .x12=W dst := dst'.trans dp
  have endRun:=Normal.syscall o r (op.pc+2) src dst bound pc2 c mode.select mode.kind mode.width rs rd sa da
  have read : readBuffer r src 96=readBuffer s src 96 := read_congr_mem _ _ _ _ rfl
  have same : Normal.afterCall o r src dst=result op s ans := by
    change writeBits r (W dst) (o.compression (readBuffer r src 96))=writeBits r (r.getReg .x12) ans
    rw [rd,read]
  rw [same] at endRun
  constructor
  · exact (Normal.deterministic o (first.trans next)).trans endRun
  · have h:=call_pc s op.src op.dst op.a op.b ans
    exact h.trans (by rw [pc];cases op <;> rfl)
  · change (callState s _ _ _ _ _).mem=_
    exact (call_memory s op.src op.dst op.a op.b _ indep).trans (by rw [dp];rfl)
  · intro reg h k;exact call_register s op.src op.dst reg op.a op.b ans h k
  · change (writeBits r (r.getReg .x12) ans).getReg .x12=_
    rw [writeBits_register,rd]

theorem CallResult.mode {o op s t src dst} (h : CallResult o op s t src dst) (m : Mode s) : Mode t :=
  ⟨(h.keep _ (by decide) (by decide)).trans m.select,(h.keep _ (by decide) (by decide)).trans m.kind,
   (h.keep _ (by decide) (by decide)).trans m.width⟩

theorem CallResult.written {o op s t src dst} (h : CallResult o op s t src dst) :
    readBuffer t dst 32=o.compression (readBuffer s src 96) :=
  (read_congr_mem _ _ _ _ h.mem).trans (store_read ..)

theorem CallResult.away {o op s t src dst} (h : CallResult o op s t src dst) (a n : Nat)
    (db : dst+32≤2^64) (bound : a+n≤2^64) (sep : a+n≤dst ∨ dst+32≤a) : readBuffer t a n=readBuffer s a n :=
  (read_congr_mem _ _ _ _ h.mem).trans (store_away _ _ _ _ _ db bound sep)

theorem CallResult.high {o op s t src dst} (h : CallResult o op s t src dst) (lo : dst+32≤448) : High s t :=
  fun a n ha bound => h.away a n (by omega) (by unfold MEMORY_BYTES at bound;omega) (Or.inr (by omega))

end CommitGolfCandidate.Late.Check.Micro
