import CommitGolfCandidate.S5PhaseTable
import CommitGolfCandidate.S5HeaderInterpreter
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 20000
def asmHeaders : List (List Instr) := [
[.LUI .x6 1,.ADDI .x6 .x6 2048,.ADD .x21 .x18 .x6,.LUI .x6 131073,.ADDI .x6 .x6 2112,.ADD .x22 .x18 .x6,.LUI .x20 5,.ADDI .x20 .x20 1712],
[.LUI .x6 131073,.ADDI .x6 .x6 2112,.ADD .x21 .x18 .x6,.LUI .x6 196609,.ADDI .x6 .x6 2144,.ADD .x22 .x18 .x6,.LUI .x20 3,.ADDI .x20 .x20 2904],
[.LUI .x6 196609,.ADDI .x6 .x6 2144,.ADD .x21 .x18 .x6,.LUI .x6 229377,.ADDI .x6 .x6 2208,.ADD .x22 .x18 .x6,.LUI .x20 1,.ADDI .x20 .x20 1452],
[.LUI .x6 229377,.ADDI .x6 .x6 2208,.ADD .x21 .x18 .x6,.LUI .x6 245761,.ADDI .x6 .x6 2240,.ADD .x22 .x18 .x6,.LUI .x20 1,.ADDI .x20 .x20 2774],
[.LUI .x6 245761,.ADDI .x6 .x6 2240,.ADD .x21 .x18 .x6,.LUI .x6 253953,.ADDI .x6 .x6 2304,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 1387],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 253953,.ADDI .x6 .x6 2304,.ADD .x21 .x18 .x6,.LUI .x6 258049,.ADDI .x6 .x6 2336,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 693],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 258049,.ADDI .x6 .x6 2336,.ADD .x21 .x18 .x6,.LUI .x6 260097,.ADDI .x6 .x6 2400,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 346],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 260097,.ADDI .x6 .x6 2400,.ADD .x21 .x18 .x6,.LUI .x6 261121,.ADDI .x6 .x6 2432,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 173],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 2304,.OR .x29 .x29 .x6,.LUI .x30 1,.ADDI .x30 .x30 4095,.LUI .x6 261120,.ADDI .x6 .x6 384,.ADD .x21 .x18 .x6,.LUI .x6 261632,.ADDI .x6 .x6 448,.ADD .x22 .x18 .x6,.LUI .x20 3,.ADDI .x20 .x20 2731],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 2560,.OR .x29 .x29 .x6,.ADDI .x30 .x0 1023,.LUI .x6 261632,.ADDI .x6 .x6 448,.ADD .x21 .x18 .x6,.LUI .x6 261888,.ADDI .x6 .x6 480,.ADD .x22 .x18 .x6,.LUI .x20 1,.ADDI .x20 .x20 1365],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 2816,.OR .x29 .x29 .x6,.ADDI .x30 .x0 511,.LUI .x6 261888,.ADDI .x6 .x6 480,.ADD .x21 .x18 .x6,.LUI .x6 262016,.ADDI .x6 .x6 544,.ADD .x22 .x18 .x6,.LUI .x20 1,.ADDI .x20 .x20 2731],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3072,.OR .x29 .x29 .x6,.ADDI .x30 .x0 255,.LUI .x6 262016,.ADDI .x6 .x6 544,.ADD .x21 .x18 .x6,.LUI .x6 262080,.ADDI .x6 .x6 576,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 1365],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3328,.OR .x29 .x29 .x6,.ADDI .x30 .x0 127,.LUI .x6 262080,.ADDI .x6 .x6 576,.ADD .x21 .x18 .x6,.LUI .x6 262112,.ADDI .x6 .x6 640,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 683],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3584,.OR .x29 .x29 .x6,.ADDI .x30 .x0 63,.LUI .x6 262112,.ADDI .x6 .x6 640,.ADD .x21 .x18 .x6,.LUI .x6 262128,.ADDI .x6 .x6 672,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 341],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.ADDI .x6 .x6 3840,.OR .x29 .x29 .x6,.ADDI .x30 .x0 63,.LUI .x6 262128,.ADDI .x6 .x6 672,.ADD .x21 .x18 .x6,.LUI .x6 262136,.ADDI .x6 .x6 736,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 171],
[.ADDI .x29 .x0 1,.SLLI .x29 .x29 63,.LUI .x6 1,.OR .x29 .x29 .x6,.ADDI .x30 .x0 63,.LUI .x6 262136,.ADDI .x6 .x6 736,.ADD .x21 .x18 .x6,.LUI .x6 262140,.ADDI .x6 .x6 768,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 85],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262141,.ADDI .x6 .x6 2816,.ADD .x21 .x18 .x6,.LUI .x6 262143,.ADDI .x6 .x6 2880,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 2],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262143,.ADDI .x6 .x6 2880,.ADD .x21 .x18 .x6,.LUI .x6 262144,.ADDI .x6 .x6 2912,.ADD .x22 .x18 .x6,.ADDI .x20 .x0 1],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262144,.ADDI .x6 .x6 2912,.ADD .x21 .x18 .x6,.LUI .x6 262144,.ADDI .x6 .x6 928,.ADD .x22 .x18 .x6,.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048,.ADDI .x20 .x0 22,.ADDI .x7 .x0 0],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262144,.ADDI .x6 .x6 928,.ADD .x21 .x18 .x6,.LUI .x6 262144,.ADDI .x6 .x6 1984,.ADD .x22 .x18 .x6,.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048,.ADDI .x20 .x0 11,.ADDI .x7 .x0 0],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262144,.ADDI .x6 .x6 1984,.ADD .x21 .x18 .x6,.LUI .x6 262145,.ADDI .x6 .x6 2560,.ADD .x22 .x18 .x6,.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048,.ADDI .x20 .x0 6,.ADDI .x7 .x0 0],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262145,.ADDI .x6 .x6 2560,.ADD .x21 .x18 .x6,.LUI .x6 262145,.ADDI .x6 .x6 2848,.ADD .x22 .x18 .x6,.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048,.ADDI .x20 .x0 3,.ADDI .x7 .x0 0],
[.LUI .x30 4,.ADDI .x30 .x30 4095,.LUI .x6 262145,.ADDI .x6 .x6 2848,.ADD .x21 .x18 .x6,.LUI .x6 262145,.ADDI .x6 .x6 3040,.ADD .x22 .x18 .x6,.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048,.ADDI .x20 .x0 2,.ADDI .x7 .x0 0],
[.LUI .x6 262145,.ADDI .x6 .x6 3040,.ADD .x21 .x18 .x6,.LUI .x6 262145,.ADDI .x6 .x6 3136,.ADD .x22 .x18 .x6,.ADDI .x21 .x21 2048,.ADDI .x22 .x22 2048]]
def headerOps (d : Height) := asmHeaders[d.val]?.getD []
def pureEntry (d : Height) := passHeader d+(if chained d then 8 else 0)
def bodyEntry (d : Height) := if tileSize d=0 then tailPC d else mainPC d
def cursorBias (d : Height) := if ¬chained d ∧ tileSize d≠0 then 2048 else 0
def phaseSeed : KnownRegs
  | .x0=>some 0 | .x5=>some 0 | .x9=>some 4294971392 | .x11=>some 96 | .x13=>some 0
  | .x18=>some 4294975488 | .x24=>some 7113547776 | .x25|.x26|.x27=>some 4032 | _=>none
def completeHeader (d : Height) := (headerOps d).foldl knownStep phaseSeed

theorem header_facts : ∀ d : Height,
    (headerOps d).all setupOp=true ∧ pureEntry d+(headerOps d).length=bodyEntry d ∧
    completeHeader d .x21=some (BitVec.ofNat 64 (nodeAddress d.val 0+cursorBias d)) ∧
    completeHeader d .x22=some (BitVec.ofNat 64 (nodeAddress (d.val+1) 0+cursorBias d)) ∧
    (d.val<23 → completeHeader d .x20=some (BitVec.ofNat 64 (if tileSize d=0 then remainder d else tiles d))) ∧
    (chained d → completeHeader d .x29=some (BitVec.ofNat 64 (2^63+256*(d.val+1))) ∧
      completeHeader d .x30=some (BitVec.ofNat 64 (2^(wireWidth d-224)-1))) ∧
    (tileSize d=0 → d.val<23 → completeHeader d .x7=some 0) := by decide +kernel

private theorem bound_header : ∀ d : Height,(headerOps d).length≤32 ∧ pureEntry d+(headerOps d).length<18492 := by decide +kernel
private theorem header_table : ∀ d : Height, ∀ j : Fin (headerOps d).length,
    decodeInstruction (atWord .commit ⟨pureEntry d+j.val,by change pureEntry d+j.val<18492;have h:=(bound_header d).2;have :=j.isLt;omega⟩)=
      some (.base ((headerOps d)[j.val]?.getD .EBREAK)) := by decide +kernel

def entered (s : MachineState) (d : Height) := (headerOps d).foldl execInstrBr s
theorem header_run (d : Height) (s : MachineState) (pc : s.pc=pcAt (pureEntry d)) (fuel : Nat) :
    execute commitImage (fuel+(headerOps d).length) s true=
      (do let r←execute commitImage fuel (entered s d) true;return r.charge (headerOps d).length 0) := by
  apply execute_linear .commit true (headerOps d) _ _ _ pc
  · intro op mem;exact header_straight op (List.all_eq_true.mp (header_facts d).1 op mem)
  · intro j inside
    have h:=bound_header d;let ix : Fin (headerOps d).length:=⟨j,inside⟩
    apply site (p:=.commit) (by change pureEntry d+j<18492;omega)
    have f:=header_table d ix
    simpa only [ix,List.getElem?_eq_getElem inside,Option.getD_some] using f
end CommitGolfCandidate.S5Machine
