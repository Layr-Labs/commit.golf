import CommitGolfCandidate.ChainedFastPack
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.TwoPermutationCounted

namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local irreducible] execute writeBits readBuffer

inductive Port where | child | parent | chain deriving DecidableEq
def Port.slot : Port → Slot | .child=>0 | .parent=>8 | .chain=>12
def ptr (n : Nat) (p : Port) := W (address n p.slot)
inductive Arith where
  | band (a b : Reg) | bor (a b : Reg) | shl (a : Reg) (i : BitVec 6) | shr (a : Reg) (i : BitVec 6)
def Arith.value (f : Reg→Word) : Arith→Word
  | .band a b=>f a &&& f b | .bor a b=>f a ||| f b | .shl a i=>f a <<< i.toNat | .shr a i=>f a >>> i.toNat
def Arith.op (r : Reg) : Arith→Instr
  | .band a b=>.AND r a b | .bor a b=>.OR r a b | .shl a i=>.SLLI r a i | .shr a i=>.SRLI r a i

inductive Cmd where
  | get (r : Reg) (i : Fin 8) | put (i : Fin 8) (r : Reg)
  | calc (r : Reg) (a : Arith)
  | srcChild | srcChain | dstChain | dstParent
  | tag (r : Reg) | getTop | putTop
  | hash (first last : Bool)
def Cmd.op (k : Lane) : Cmd→Instr
  | .get r i=>.LD r .x6 (childOff k i.val)
  | .put i r=>.SD .x6 r (childOff k i.val)
  | .calc r a=>a.op r
  | .srcChild=>.ADDI .x10 .x6 (childOff k 0) | .srcChain=>.ADDI .x10 .x0 224
  | .dstChain=>.ADDI .x12 .x0 224 | .dstParent=>.ADDI .x12 .x7 (parentOff k)
  | .tag r=>.SD .x0 r 256 | .getTop=>.LD .x1 .x12 24 | .putTop=>.SD .x12 .x1 24
  | .hash ..=>.ECALL

def plan (h : Low) : List Cmd :=
  [.get .x27 3,.get .x28 4,.get .x29 5,.get .x30 6,.get .x31 7] ++
  [.calc .x27 (.band .x27 .x3),.calc .x31 (.band .x31 .x3)] ++
  [.calc .x20 (.shl .x28 46),.calc .x20 (.bor .x20 .x27),
   .calc .x21 (.shr .x28 18),.calc .x1 (.shl .x29 46),.calc .x21 (.bor .x21 .x1),
   .calc .x22 (.shr .x29 18),.calc .x1 (.shl .x30 46),.calc .x22 (.bor .x22 .x1),
   .calc .x23 (.shr .x30 18),.calc .x1 (.shl .x31 46),.calc .x23 (.bor .x23 .x1),
   .calc .x24 (.shr .x31 18),.calc .x24 (.bor .x24 .x16),
   .put 3 .x20,.put 4 .x21,.put 5 .x22,.put 6 .x23,.put 7 .x24,
   .srcChild,.dstChain,.hash true false,
   .put 3 .x27,.put 4 .x28,.put 5 .x29,.put 6 .x30,.put 7 .x31,
   .srcChain,.tag .x17,.hash false false,.tag .x18,.hash false false,
   .tag .x19,.dstParent,.hash false true] ++
  (if h.val=7 then [.getTop,.calc .x1 (.band .x1 .x15),.putTop] else [])

theorem plan_op (h : Low) (k : Lane) : (plan h).map (Cmd.op k) = node h k := by
  fin_cases h <;> rfl

def Cmd.calls : Cmd→Nat | .hash ..=>1 | _=>0
def nCalls (xs : List Cmd) := (xs.map Cmd.calls).sum
theorem fourCalls (h : Low) : nCalls (plan h)=4 := by fin_cases h <;> rfl
theorem length_plan (h : Low) : (plan h).length=nodeSteps h := by fin_cases h <;> rfl

def srcPort (first : Bool) : Port := if first then .child else .chain
def dstPort (last : Bool) : Port := if last then .parent else .chain
def cslot (i : Fin 8) : Slot := ⟨i.val,by omega⟩
def putR (s : MachineState) (r : Reg) (v : Word) := (s.setReg r v).setPC (s.pc+4)
def putM (s : MachineState) (n : Nat) (i : Slot) (v : Word) := (s.setMem (W (address n i)) v).setPC (s.pc+4)
def command (n : Nat) (s : MachineState) : Cmd→OracleComp World MachineState
  | .get r i=>pure (putR s r (s.getMem (W (address n (cslot i)))))
  | .put i r=>pure (putM s n (cslot i) (s.getReg r))
  | .calc r a=>pure (putR s r (a.value s.getReg))
  | .srcChild=>pure (putR s .x10 (ptr n .child)) | .srcChain=>pure (putR s .x10 (ptr n .chain))
  | .dstChain=>pure (putR s .x12 (ptr n .chain)) | .dstParent=>pure (putR s .x12 (ptr n .parent))
  | .tag r=>pure (putM s n 16 (s.getReg r)) | .getTop=>pure (putR s .x1 (s.getMem (W (address n 11))))
  | .putTop=>pure (putM s n 11 (s.getReg .x1))
  | .hash first last=>do
    let y ← (liftM (World.query (.inr (.inl (readBuffer s (address n (srcPort first).slot) 64)))) : OracleComp World Output)
    return writeBits s (ptr n (dstPort last)) y
def trace (n : Nat) : List Cmd → MachineState→OracleComp World MachineState
  | [],s=>pure s
  | a::rest,s=>command n s a >>= trace n rest

inductive Role where | childBase | parentBase | zero | size | port (p : Port) deriving DecidableEq
def roleValue (n : Nat) (k : Lane) : Role→Word
  | .childBase=>heapAddress (2*(n+k.val)) | .parentBase=>heapAddress (n+k.val)
  | .zero=>0 | .size=>64 | .port p=>ptr n p
abbrev Known := Reg→Option Role
def startRegs : Known
  | .x6=>some .childBase | .x7=>some .parentBase | .x5|.x13=>some .zero | .x11=>some .size | _=>none
def Tracked (n : Nat) (k : Lane) (m : Known) (s : MachineState) :=
  ∀ r p, m r=some p → s.getReg r=roleValue n k p
def assign (m : Known) (r : Reg) (p : Option Role) : Known :=
  fun q=>if q=r then p else m q
def nextRegs (m : Known) : Cmd→Known
  | .get r _|.calc r _=>assign m r none
  | .getTop=>assign m .x1 none
  | .srcChild=>assign m .x10 (some (.port .child)) | .srcChain=>assign m .x10 (some (.port .chain))
  | .dstChain=>assign m .x12 (some (.port .chain)) | .dstParent=>assign m .x12 (some (.port .parent))
  | _=>m
def permits (m : Known) : Cmd→Bool
  | .get r _=>r != .x0 && m .x6==some .childBase
  | .calc r _=>r != .x0
  | .put ..|.srcChild=>m .x6==some .childBase
  | .dstParent=>m .x7==some .parentBase
  | .getTop|.putTop=>m .x12==some (.port .parent)
  | .hash f l=>m .x10==some (.port (srcPort f)) && m .x12==some (.port (dstPort l)) &&
    m .x5==some .zero && m .x11==some .size && m .x13==some .zero
  | _=>true
def checked (m : Known) : List Cmd→Bool
  | []=>true | a::xs=>permits m a && checked (nextRegs m a) xs

theorem checks (h : Low) : checked startRegs (plan h)=true := by fin_cases h <;> decide

theorem word_pc (w : Nat) : pc w + 4#64=pc (w+1) := by
  change W (4096+4*w) + W 4=W (4096+4*(w+1))
  rw [wordplus] <;> congr 1 <;> omega

theorem parent_top_addr (n : Nat) : ptr n .parent+24#64=W (address n 11) := by
  change W (heapBase+32*n+8*(8-8)) + W 24=W (heapBase+32*n+8*(11-8))
  rw [wordplus] <;> congr 1 <;> omega

end CommitGolfCandidate.Chained.Native.Fast
