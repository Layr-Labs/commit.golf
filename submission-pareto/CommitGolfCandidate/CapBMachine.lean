import CommitGolfCandidate.TwoPermutationPackedFetchBase
import CommitGolfCandidate.Layout2Helpers
import CommitGolfCandidate.Memory
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.Layout2CapTables

namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp Layout2Helpers
abbrev addr := BitVec.ofNat 64
def pc (w : Nat) := addr (4096+4*w)
def Run (I : Image) (s t : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel coins, execute I (steps+fuel) s coins = do
    let z ← execute I fuel t coins
    pure (z.charge cycles 0)
theorem Run.zero (I s) : Run I s s 0 0 := by intro f c;simp [Execution.charge]
theorem Run.thenDo {I s t u n c m d} (a : Run I s t n c) (b : Run I t u m d) :
    Run I s u (n+m) (c+d) := by
  intro f coin;rw [Nat.add_assoc,a,b];simp [bind_assoc,pure_bind,Execution.charge,Nat.add_assoc]

def CodeAt (I : Image) (w : Nat) (ops : List Instr) : Prop :=
  ∀ i : Fin ops.length,(I.code[w+i.val]?).bind decodeInstruction=some (.base ops[i.val])
theorem pc_add (w : Nat) : pc w+4=pc (w+1) := by change addr (4096+4*w)+addr 4=addr (4096+4*(w+1));rw [←BitVec.ofNat_add];congr 1 <;> omega
theorem one {I : Image} {s : MachineState} {w : Nat} {op : Instr} (lim : w<2^40)
    (pos : s.pc=pc w) (fetched : (I.code[w]?).bind decodeInstruction=some (.base op))
    (ready : ordinaryStep s (.base op)=some (execInstrBr s op)) :
    Run I s (execInstrBr s op) 1 (instructionCycles (.base op)) := by
  have d:=wide_image_fetch I s w op lim pos fetched
  intro f c;rw [Nat.add_comm 1 f,execute_ordinary_step _ _ _ _ _ _ d ready]

def gword (s : MachineState) (a : Nat) := s.getMem (addr a)
def gbyte (s : MachineState) (a : Nat) := s.getByte (addr a)
theorem byte_word (s : MachineState) (a j : Nat) (alg : a%8=0) (lane : j<8) (fit : a+8≤2^64) :
    gbyte s (a+j)=extractByte (gword s a) j := byte_at _ _ _ alg lane fit

/-- Addresses in these areas denote aligned dword keys. -/
inductive Area where | dst | src deriving DecidableEq
inductive Expr where
  | reg (r : Reg) | mem (a : Area) (j : Nat) | lit (n : Nat)
  | add (x y : Expr) | shl (x : Expr) (n : Nat) | shr (x : Expr) (n : Nat)
  | bor (x y : Expr) | mul (x y : Expr)
deriving DecidableEq
structure Areas where
  dst : Nat
  src : Nat
  dstWords : Nat
  srcWords : Nat
def Areas.start (a : Areas) : Area → Nat | .dst=>a.dst | .src=>a.src
def Areas.words (a : Areas) : Area → Nat | .dst=>a.dstWords | .src=>a.srcWords
def Areas.key (a : Areas) (r : Area) (j : Nat) := addr (a.start r+8*j)
structure Safe (a : Areas) : Prop where
  alg : ∀r,a.start r%8=0
  room : ∀r,a.start r+8*a.words r≤MEMORY_BYTES
  disjoint : a.src+8*a.srcWords≤a.dst ∨ a.dst+8*a.dstWords≤a.src

def val (s : MachineState) (a : Areas) : Expr → Word
  | .reg r=>s.getReg r | .lit n=>addr n | .mem b j=>s.getMem (a.key b j)
  | .add x y=>val s a x+val s a y | .shl x n=>val s a x <<< n | .shr x n=>val s a x >>> n
  | .bor x y=>val s a x ||| val s a y | .mul x y=>val s a x*val s a y

structure Model where
  reg : Reg → Expr
  out : Nat → Expr
def initial : Model := ⟨.reg,.mem .dst⟩
def regSet (m : Model) (r : Reg) (x : Expr) : Model := {m with reg:=fun q=>if r=q then x else m.reg q}
def outSet (m : Model) (j : Nat) (v : Expr) : Model := {m with out:=fun k=>if j=k then v else m.out k}
def read (m : Model) : Area → Nat → Expr | .dst,j=>m.out j | .src,j=>.mem .src j

inductive Row where
  | addi (d r : Reg) (imm : Nat)
  | lui (d : Reg) (imm : Nat)
  | add (d l r : Reg) | bor (d l r : Reg) | mul (d l r : Reg)
  | shl (d r : Reg) (n : Nat) | shr (d r : Reg) (n : Nat)
  | ld (d b : Reg) (key : Area) (off : Nat)
  | sd (s b : Reg) (off : Nat)
deriving DecidableEq

def op : Row → Instr
  | .addi d r i=>.ADDI d r (BitVec.ofNat 12 i) | .lui d i=>.LUI d (BitVec.ofNat 20 i)
  | .add d l r=>.ADD d l r | .bor d l r=>.OR d l r | .mul d l r=>.MUL d l r
  | .shl d r n=>.SLLI d r (BitVec.ofNat 6 n) | .shr d r n=>.SRLI d r (BitVec.ofNat 6 n)
  | .ld d b _ j=>.LD d b (BitVec.ofNat 12 (8*j)) | .sd s b j=>.SD b s (BitVec.ofNat 12 (8*j))

def advance (m : Model) : Row → Model
  | .addi d r i=>regSet m d (.add (m.reg r) (.lit (signExtend12 (BitVec.ofNat 12 i)).toNat))
  | .lui d i=>regSet m d (.lit (((BitVec.ofNat 20 i).zeroExtend 32 <<< (12:Nat)).signExtend 64).toNat)
  | .add d l r=>regSet m d (.add (m.reg l) (m.reg r))
  | .bor d l r=>regSet m d (.bor (m.reg l) (m.reg r))
  | .mul d l r=>regSet m d (.mul (m.reg l) (m.reg r))
  | .shl d r n=>regSet m d (.shl (m.reg r) n)
  | .shr d r n=>regSet m d (.shr (m.reg r) n)
  | .ld d _ key j=>regSet m d (read m key j)
  | .sd r _ j=>outSet m j (m.reg r)

structure Layout where
  base : Area → Expr
  count : Area → Nat
def valid (L : Layout) (m : Model) : Row → Prop
  | .addi d .. | .lui d .. | .add d .. | .bor d .. | .mul d .. => d≠.x0
  | .shl d _ n | .shr d _ n=>d≠.x0 ∧ n<64
  | .ld d b a j=>d≠.x0 ∧ m.reg b=L.base a ∧ j<L.count a ∧ j<256
  | .sd _ b j=>m.reg b=L.base .dst ∧ j<L.count .dst ∧ j<256
instance (l m r) : Decidable (valid l m r) := by cases r <;> unfold valid <;> infer_instance
def checked (l : Layout) (m : Model) : List Row → Bool
  | []=>true
  | r::rs=>decide (valid l m r) && checked l (advance m r) rs
def price (rs : List Row) := (rs.map (fun r=>instructionCycles (.base (op r)))).sum

structure Tracks (s t : MachineState) (a : Areas) (m : Model) : Prop where
  reg : ∀ r,t.getReg r=val s a (m.reg r)
  out : ∀ j,j<a.dstWords → t.getMem (a.key .dst j)=val s a (m.out j)
  frame : ∀ w : Word,(∀ j,j<a.dstWords → w≠a.key .dst j) → t.getMem w=s.getMem w

theorem track_zero (s a) : Tracks s s a initial := ⟨fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
end CommitGolfCandidate.CapB
