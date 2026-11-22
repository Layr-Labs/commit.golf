import CommitGolfCandidate.CapBPrepCode
import CommitGolfCandidate.CapBPrice
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.GroupedOpening.CapB (carryBits handlerLen)
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def startHandler (j : Nat) := 6144+16*(j%32)
def emitted (j : Nat) := decide (18≤carryBits j)
def width (j : Nat) := if emitted j then 4 else 3
def phaseDelta (p : Nat) := if p%32=31 then 2112 else 64
def srcExpr : Expr := .add (.reg .x25) (.shl (.reg .x6) 5)
def handlerLayout (j : Nat) : Layout :=
  ⟨(fun | .src=>srcExpr | .dst=>.reg .x21),(fun | .src=>4 | .dst=>width j)⟩
def handlerRows (j : Nat) : List Row :=
  let c:=carryBits j
  [.shl .x7 .x6 5,.add .x7 .x25 .x7] ++
  (List.range 3).flatMap (fun i=>[.ld .x31 .x7 .src i,.sd .x31 .x21 i]) ++
  (if c=0 then [.ld .x22 .x7 .src 3,.addi .x21 .x21 24]
   else if c<18 then [.ld .x31 .x7 .src 3,.shl .x31 .x31 c,.bor .x22 .x22 .x31,.addi .x21 .x21 24]
   else if c=18 then [.ld .x31 .x7 .src 3,.shl .x31 .x31 18,.bor .x22 .x22 .x31,.sd .x22 .x21 3,.addi .x21 .x21 32]
   else [.ld .x31 .x7 .src 3,.shl .x28 .x31 c,.bor .x22 .x22 .x28,.sd .x22 .x21 3,
         .shr .x22 .x31 (64-c),.addi .x21 .x21 32]) ++
  [.addi .x19 .x19 (phaseDelta j)]

def handlerOps (j : Nat) := (handlerRows j).map op++[Instr.JALR .x0 .x18 0]
def mergedE (j : Nat) := Expr.bor (.reg .x22) (.shl (.mem .src 3) (carryBits j))
def carryE (j : Nat) :=
  if carryBits j=0 then .mem .src 3 else if carryBits j≤18 then mergedE j else Expr.shr (.mem .src 3) (64-carryBits j)
def handlerModel (j : Nat) := (handlerRows j).foldl advance initial

theorem handler_code : ∀ j : Fin 32, Slice openingImage (startHandler j) (handlerOps j) := by decide +kernel
theorem handler_valid : ∀ j : Fin 32,
  checked (handlerLayout j) initial (handlerRows j)=true ∧
  (handlerRows j).length+1=handlerLen j ∧ price (handlerRows j)+1=handlerLen j ∧
  (handlerModel j).reg .x22=carryE j ∧
  (handlerModel j).reg .x21=.add (.reg .x21) (.lit (8*width j)) ∧
  (handlerModel j).reg .x19=.add (.reg .x19) (.lit (signExtend12 (BitVec.ofNat 12 (phaseDelta j))).toNat) ∧
  ∀ i : Fin (width j), (handlerModel j).out i.val=if i.val<3 then .mem .src i.val else mergedE j := by decide +kernel
theorem handler_keep (j : Fin 32) (r : Reg) (free : r∉[.x7,.x28,.x31,.x22,.x21,.x19]) :
  (handlerModel j).reg r=.reg r := by
  cases r <;> first | exact False.elim (free (by decide)) | (revert j;decide +kernel)

end CommitGolfCandidate.CapB
