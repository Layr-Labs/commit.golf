import CommitGolfCandidate.Stage3cCheckCopy
import CommitGolfCandidate.Stage3cCheckEdges
import CommitGolfCandidate.Stage3cCheckCalc
import CommitGolfCandidate.Stage3cClearWords
import CommitGolfCandidate.Stage3cWire
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
structure RowSite where
  batch : Bool
  height : Fin 24
deriving DecidableEq,Fintype
def RowSite.allowed (p : RowSite) := !p.batch || decide (p.height.val<15)
def rowPC (b : Bool) (h : Nat) := if b then 238+35*h else 1118+42*h
def RowSite.pc (p : RowSite) := rowPC p.batch p.height.val
def RowSite.radix (p : RowSite) := Geo.radix p.height.val
def RowSite.header (p : RowSite) : List Sym.Calc :=
  [.andi .x4 .x14 1,.srli .x14 .x14 1,.slli .x6 .x4 5,.add .x6 .x25 .x6]
def currentCopy : CopySpec :=⟨.x7,.x27,.x6,0,0⟩
def normalCopy : CopySpec :=⟨.x7,.x19,.x6,0,0⟩
def RowSite.peerOps (p : RowSite) : List Sym.Calc:=
  [.xori .x4 .x4 1,.slli .x6 .x4 5,.add (if p.batch then .x10 else .x6) .x25 .x6]
def RowSite.peerPC (p : RowSite) (peer : Nat):=p.pc+24+(if p.batch then 6 else 13)*peer
def RowSite.hashPC (p : RowSite) := rowPC p.batch (p.height.val+1)-6
def RowSite.hashOps (p : RowSite) : List Sym.Calc:=
  [.addi .x10 .x25 0,.addi .x12 .x27 0,.addi .x29 .x0 (BitVec.ofNat 12 (p.height.val+1)),
   .addi .x30 .x0 (BitVec.ofNat 12 (calls (Pw.height p.height.val))),
   .addi .x31 .x0 (BitVec.ofNat 12 (Pw.bits (p.height.val+1)))]
def RowSite.valid (p : RowSite) : Prop :=
  ZeroSites .x25 p.pc 12 ∧ Sym.Listed p.header (p.pc+12) ∧ CopySites currentCopy (p.pc+16) 4 ∧
  Sym.Listed p.hashOps p.hashPC ∧ JumpSite (p.hashPC+5) 173 .x1 ∧ p.hashPC+6=rowPC p.batch (p.height.val+1) ∧
  ∀ k : Fin 2,k.val<p.radix-1 →
    let s:=p.peerPC k.val
    let a:=s+p.peerOps.length
    Sym.Listed p.peerOps s ∧
      (if p.batch then
        matchesWord .check (a,.ADDI .x11 .x0 (BitVec.ofNat 12 (Pw.bits p.height.val))) ∧ JumpSite (a+1) 21 .x1
      else CopySites normalCopy a 4 ∧ matchesWord .check (a+8,.ADDI .x19 .x19 32)) ∧
      (if p.batch then a+2 else a+9)=(if k.val+1<p.radix-1 then p.peerPC (k.val+1) else p.hashPC)
instance (p : RowSite) : Decidable p.valid:=by unfold RowSite.valid ZeroSites CopySites;infer_instance
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem row_sites : ∀ p : RowSite,p.allowed=true → p.valid := by decide +kernel
theorem kernel_immediates : ∀ h : Fin 24,
    signExtend12 (BitVec.ofNat 12 (h.val+1))=Open.W (h.val+1) ∧
    signExtend12 (BitVec.ofNat 12 (calls (Pw.height h.val)))=Open.W (calls (Pw.height h.val)) ∧
    signExtend12 (BitVec.ofNat 12 (Pw.bits (h.val+1)))=Open.W (Pw.bits (h.val+1)) ∧
    signExtend12 (BitVec.ofNat 12 (Pw.bits h.val))=Open.W (Pw.bits h.val) := by decide +kernel
end CommitGolfCandidate.Chained.BinaryMachine.Check
