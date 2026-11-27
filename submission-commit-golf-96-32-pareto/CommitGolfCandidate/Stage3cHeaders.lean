import CommitGolfCandidate.Stage3cPhaseTable
import CommitGolfCandidate.Stage3cHeaderInterpreter
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
set_option Elab.async false
def asmHeaders : List (List Instr) := [
[.ADDI .x6 .x0 0,.ADD .x10 .x18 .x6,.LUI .x6 196608,.ADD .x12 .x18 .x6,.LUI .x20 16],
[.LUI .x6 196608,.ADD .x10 .x18 .x6,.LUI .x6 294912,.ADD .x12 .x18 .x6,.LUI .x20 8],
[.LUI .x6 294912,.ADD .x10 .x18 .x6,.LUI .x6 344064,.ADD .x12 .x18 .x6,.LUI .x20 4],
[.LUI .x6 344064,.ADD .x10 .x18 .x6,.LUI .x6 368640,.ADD .x12 .x18 .x6,.LUI .x20 2],
[.LUI .x6 368640,.ADD .x10 .x18 .x6,.LUI .x6 380928,.ADD .x12 .x18 .x6,.LUI .x20 1],
[.LUI .x6 380928,.ADD .x10 .x18 .x6,.LUI .x6 387072,.ADD .x12 .x18 .x6,.LUI .x20 1,.ADDI .x20 .x20 2048],
[.LUI .x6 387072,.ADD .x10 .x18 .x6,.LUI .x6 390144,.ADD .x12 .x18 .x6,.ADDI .x20 .x0 1024],
[.LUI .x6 390144,.ADD .x10 .x18 .x6,.LUI .x6 391680,.ADD .x12 .x18 .x6,.ADDI .x20 .x0 512],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 2304,.OR .x29 .x29 .x6,.LUI .x30 1,.ADDI .x30 .x30 4095,.LUI .x6 391680,.ADD .x21 .x18 .x6,.LUI .x6 392448,.ADD .x22 .x18 .x6,.LUI .x20 4],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 2560,.OR .x29 .x29 .x6,.ADDI .x30 .x0 1023,.LUI .x6 392448,.ADD .x21 .x18 .x6,.LUI .x6 392832,.ADD .x22 .x18 .x6,.LUI .x20 2],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 2816,.OR .x29 .x29 .x6,.ADDI .x30 .x0 511,.LUI .x6 392832,.ADD .x21 .x18 .x6,.LUI .x6 393024,.ADD .x22 .x18 .x6,.LUI .x20 1],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3072,.OR .x29 .x29 .x6,.ADDI .x30 .x0 255,.LUI .x6 393024,.ADD .x21 .x18 .x6,.LUI .x6 393120,.ADD .x22 .x18 .x6,.LUI .x20 1,.ADDI .x20 .x20 2048],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3328,.OR .x29 .x29 .x6,.ADDI .x30 .x0 127,.LUI .x6 393120,.ADD .x21 .x18 .x6,.LUI .x6 393168,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 1024],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3584,.OR .x29 .x29 .x6,.ADDI .x30 .x0 63,.LUI .x6 393168,.ADD .x21 .x18 .x6,.LUI .x6 393192,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 512],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3840,.OR .x29 .x29 .x6,.ADDI .x30 .x0 63,.LUI .x6 393192,.ADD .x21 .x18 .x6,.LUI .x6 393204,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 256],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.OR .x29 .x29 .x6,.ADDI .x30 .x0 63,.LUI .x6 393204,.ADD .x21 .x18 .x6,.LUI .x6 393210,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 128],
[.LUI .x6 393210,.ADD .x10 .x18 .x6,.LUI .x6 393213,.ADD .x12 .x18 .x6,.ADDI .x20 .x0 1],
[.LUI .x6 393213,.ADD .x10 .x18 .x6,.LUI .x6 393215,.ADDI .x6 .x6 2048,.ADD .x12 .x18 .x6],
[.LUI .x6 393215,.ADDI .x6 .x6 2048,.ADD .x10 .x18 .x6,.LUI .x6 393215,.ADDI .x6 .x6 1024,.ADD .x12 .x18 .x6],
[.LUI .x6 393215,.ADDI .x6 .x6 1024,.ADD .x10 .x18 .x6,.LUI .x6 393216,.ADDI .x6 .x6 2560,.ADD .x12 .x18 .x6],
[.LUI .x6 393216,.ADDI .x6 .x6 2560,.ADD .x10 .x18 .x6,.LUI .x6 393216,.ADDI .x6 .x6 3328,.ADD .x12 .x18 .x6],
[.LUI .x6 393216,.ADDI .x6 .x6 3328,.ADD .x10 .x18 .x6,.LUI .x6 393216,.ADDI .x6 .x6 3712,.ADD .x12 .x18 .x6],
[.LUI .x6 393216,.ADDI .x6 .x6 3712,.ADD .x10 .x18 .x6,.LUI .x6 393216,.ADDI .x6 .x6 3904,.ADD .x12 .x18 .x6],
[.LUI .x6 393216,.ADDI .x6 .x6 3904,.ADD .x10 .x18 .x6,.LUI .x6 393216,.ADDI .x6 .x6 4000,.ADD .x12 .x18 .x6]]
def headerOps (d : Height) := asmHeaders[d.val]?.getD []
def pureEntry (d : Height) := passHeader d+(if chained d then 8 else 0)
def bodyEntry (d : Height) := if tileSize d=0 then tailPC d else mainPC d
/-- Pointer parents and the chain both load absolute bases. There is no 2048-byte tile bias. -/
def cursorBias (_ : Height) := 0
def phaseSeed : KnownRegs
  | .x0=>some 0 | .x5=>some 0 | .x9=>some 4294971392 | .x11=>some 96 | .x13=>some 0
  | .x18=>some 4294975488 | .x24=>some 7516200960
  | .x25=>some 4096 | .x26=>some 2944 | .x27=>some 0 | _=>none
def completeHeader (d : Height) := (headerOps d).foldl knownStep phaseSeed

theorem header_facts : ∀ d : Height,
    (headerOps d).all setupOp=true ∧ pureEntry d+(headerOps d).length=bodyEntry d ∧
    (chained d →
      completeHeader d .x21=some (BitVec.ofNat 64 (nodeAddress d.val 0)) ∧
      completeHeader d .x22=some (BitVec.ofNat 64 (nodeAddress (d.val+1) 0)) ∧
      completeHeader d .x20=some (BitVec.ofNat 64 (tiles d)) ∧
      completeHeader d .x29=some (BitVec.ofNat 64 (2^63+256*(d.val+1))) ∧
      completeHeader d .x30=some (BitVec.ofNat 64 (2^(wireWidth d-224)-1))) ∧
    (¬chained d →
      completeHeader d .x10=some (BitVec.ofNat 64 (nodeAddress d.val 0)) ∧
      completeHeader d .x12=some (BitVec.ofNat 64 (nodeAddress (d.val+1) 0)) ∧
      (tileSize d≠0 → completeHeader d .x20=some (BitVec.ofNat 64 (tiles d)))) := by
  decide +kernel

private theorem bound_header : ∀ d : Height,(headerOps d).length≤32 ∧ pureEntry d+(headerOps d).length<11543 := by decide +kernel
private theorem header_table : ∀ d : Height, ∀ j : Fin (headerOps d).length,
    decodeInstruction (atWord .commit ⟨pureEntry d+j.val,by change pureEntry d+j.val<11543;have h:=(bound_header d).2;have :=j.isLt;omega⟩)=
      some (.base ((headerOps d)[j.val]?.getD .EBREAK)) := by decide +kernel

def entered (s : MachineState) (d : Height) := (headerOps d).foldl execInstrBr s
theorem header_run (d : Height) (s : MachineState) (pc : s.pc=pcAt (pureEntry d)) (fuel : Nat) :
    execute commitImage (fuel+(headerOps d).length) s true=
      (do let r←execute commitImage fuel (entered s d) true;return r.charge (headerOps d).length 0) := by
  apply execute_linear .commit true (headerOps d) _ _ _ pc
  · intro op mem;exact header_straight op (List.all_eq_true.mp (header_facts d).1 op mem)
  · intro j inside
    have h:=bound_header d;let ix : Fin (headerOps d).length:=⟨j,inside⟩
    apply site (p:=.commit) (by change pureEntry d+j<11543;omega)
    have f:=header_table d ix
    simpa only [ix,List.getElem?_eq_getElem inside,Option.getD_some] using f
end CommitGolfCandidate.Chained.BinaryMachine
