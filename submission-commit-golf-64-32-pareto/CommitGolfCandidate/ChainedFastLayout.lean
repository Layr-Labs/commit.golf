import CommitGolfCandidate.ChainedFastFrontier
import CommitGolfCandidate.ChainedCommitFetch

namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

abbrev Low := Fin 8
abbrev Lane := Fin 16
def height (h : Low) : Height := ⟨h.val,by have:=h.isLt;omega⟩
def pc (i : Nat) : Word := BitVec.ofNat 64 (4096+4*i)
def imm (z : Int) := BitVec.ofInt 12 z
def childOff (k : Lane) (i : Nat) := imm ((8*i:Int)-64*k.val)
def parentOff (k : Lane) := imm (-(32*k.val : Int))

def setup : List Instr := [.ADDI .x6 .x10 0,.ADDI .x7 .x12 0,.SRLI .x4 .x19 1,
  .SD .x0 .x0 264,.SD .x0 .x0 272,.ADDI .x1 .x0 1,.SLLI .x1 .x1 63,.SD .x0 .x1 280]
def header (h : Low) : List Instr :=
  [.ADDI .x16 .x0 (BitVec.ofNat 12 h.val),.SLLI .x16 .x16 28] ++
  (if h.val=7 then [.ADDI .x15 .x0 4095,.SRLI .x15 .x15 22] else []) ++
  (if h.val=0 then [.ADDI .x3 .x0 4095,.SRLI .x3 .x3 18] else [.ADDI .x3 .x0 4095,.SRLI .x3 .x3 22]) ++
  [.ADDI .x17 .x0 (BitVec.ofNat 12 (7*h.val)),.ADDI .x18 .x0 (BitVec.ofNat 12 (7*h.val+1)),
   .ADDI .x19 .x0 (BitVec.ofNat 12 (7*h.val+2)),.ADD .x14 .x9 .x4,.ADDI .x14 .x14 4064]

def loads (k : Lane) : List Instr :=
  [.LD .x27 .x6 (childOff k 3),.LD .x28 .x6 (childOff k 4),.LD .x29 .x6 (childOff k 5),
   .LD .x30 .x6 (childOff k 6),.LD .x31 .x6 (childOff k 7)]
def childMask : List Instr := [.AND .x27 .x27 .x3,.AND .x31 .x31 .x3]
def blend : List Instr :=
  [.SLLI .x20 .x28 46,.OR .x20 .x20 .x27,.SRLI .x21 .x28 18,.SLLI .x1 .x29 46,
   .OR .x21 .x21 .x1,.SRLI .x22 .x29 18,.SLLI .x1 .x30 46,.OR .x22 .x22 .x1,
   .SRLI .x23 .x30 18,.SLLI .x1 .x31 46,.OR .x23 .x23 .x1,
   .SRLI .x24 .x31 18,.OR .x24 .x24 .x16]
def packedStores (k : Lane) : List Instr :=
  [.SD .x6 .x20 (childOff k 3),.SD .x6 .x21 (childOff k 4),.SD .x6 .x22 (childOff k 5),
   .SD .x6 .x23 (childOff k 6),.SD .x6 .x24 (childOff k 7)]
def restore (k : Lane) : List Instr :=
  [.SD .x6 .x27 (childOff k 3),.SD .x6 .x28 (childOff k 4),.SD .x6 .x29 (childOff k 5),
   .SD .x6 .x30 (childOff k 6),.SD .x6 .x31 (childOff k 7)]
def before (h : Low) (k : Lane) := loads k ++ childMask ++ blend ++ packedStores k ++
  [.ADDI .x10 .x6 (childOff k 0),.ADDI .x12 .x0 224]
def second (k : Lane) := restore k ++ [.ADDI .x10 .x0 224,.SD .x0 .x17 256]
def third : List Instr := [.SD .x0 .x18 256]
def fourth (k : Lane) : List Instr := [.SD .x0 .x19 256,.ADDI .x12 .x7 (parentOff k)]
def finish (h : Low) : List Instr :=
  if h.val=7 then [.LD .x1 .x12 24,.AND .x1 .x1 .x15,.SD .x12 .x1 24] else []
def node (h : Low) (k : Lane) :=
  before h k ++ [.ECALL] ++ second k ++ [.ECALL] ++ third ++ [.ECALL] ++ fourth k ++ [.ECALL] ++ finish h
def nodeSteps (h : Low) := (node h 0).length
def groupTail (h : Low) : List Instr := [.ADDI .x6 .x6 3072,.ADDI .x7 .x7 3584,
  .BNE .x7 .x14 (BitVec.ofNat 13 (8192-4*(16*nodeSteps h+2))),.SRLI .x4 .x4 1]
def stageWords (h : Low) := (header h).length+16*nodeSteps h+4
def levelStart (h : Low) := 45696+((List.finRange 8).take h.val |>.map stageWords).sum
def nodeStart (h : Low) (k : Lane) := levelStart h+(header h).length+k.val*nodeSteps h
def tailStart (h : Low) := levelStart h+(header h).length+16*nodeSteps h
def handoff : List Instr := [.ADDI .x10 .x0 256,.ADDI .x12 .x0 256,
  .JAL .x0 (BitVec.ofInt 21 (4*((45298:Int)-51100)))]
end CommitGolfCandidate.Chained.Native.Fast
