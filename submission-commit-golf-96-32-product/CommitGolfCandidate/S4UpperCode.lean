import CommitGolfCandidate.S4TableHash
import CommitGolfCandidate.S4PadUpper
import CommitGolfCandidate.S4LeafLayout
import CommitGolfCandidate.S4ZeroRow
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def li2 (r : Reg) (n : Nat) : List Sym.Calc :=
  [.addi r .x0 (BitVec.ofNat 12 (n/2048)),.slli r r 11,.addi r r (BitVec.ofNat 12 (n%2048))]
def upperHeader (k : Nat) := ([4510,4554,4591,4635,4672,4716,4753,4797] : List Nat)[k]?.getD 4833
def upperLoop (k : Nat) := ([4524,4561,4605,4642,4686,4723,4767,4804] : List Nat)[k]?.getD 0
def needsPad (k : Nat) := decide (width (16+k)%2=1)
def nextWidth (k : Nat) := width (17+k)
def cutUpper (k : Nat) := projected (17+k)
def upperHeaderOps (k : Nat) := li2 .x29 16384 ++ li2 .x30 16384 ++
  (if needsPad k then li2 .x14 (upperAddr (width (16+k))) else [])
def numOp (k : Nat) := ptrCode .x19 (nextWidth k)
def addUpper : List Sym.Calc := [.addi .x29 .x29 64,.addi .x30 .x30 32,.addi .x19 .x19 4095]
def copyUpper := ptrCode .x14 512::doubleCopies .x29 .x14 0 0 8
def afterHash (k : Nat) := upperLoop k+21+(2+callSteps (cutUpper k))
def paddingPC (k : Nat) := upperHeader k+(upperHeaderOps k).length
def countPC (k : Nat) := paddingPC k+(if needsPad k then 4 else 0)
structure UpperSites (k : Nat) : Prop where
  setup : (Fragment.arithmetic (upperHeaderOps k)).valid .check (upperHeader k) (paddingPC k)
  pad : needsPad k=true → Matches .check (paddingPC k) (padWords 4)
  count : stands .check (countPC k) (numOp k)
  loop : countPC k+1=upperLoop k
  copy : Matches .check (upperLoop k) copyUpper
  zeros : Matches .check (upperLoop k+17) (zeroOps 4)
  compress : Matches .check (upperLoop k+21) (tableHashCode (cutUpper k))
  advance : (Fragment.arithmetic addUpper).valid .check (afterHash k) (afterHash k+3)
  last : conditional .check (afterHash k+3) (afterHash k+5) .x19 .x0 true
  more : directs .check (afterHash k+4) (upperLoop k)
  next : afterHash k+5=upperHeader (k+1)
  small : upperHeader (k+1)≤Code.check.count

set_option maxRecDepth 8500
set_option maxHeartbeats 2200000
private theorem sites0 : UpperSites 0 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4553 4524; exact checkEdgeValid 4553 (by decide)),by decide,by decide⟩
  intro _;exact matchesListed (by decide)
private theorem sites1 : UpperSites 1 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4590 4561; exact checkEdgeValid 4590 (by decide)),by decide,by decide⟩
  intro h;exact False.elim ((by decide : ¬needsPad 1=true) h)
private theorem sites2 : UpperSites 2 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4634 4605; exact checkEdgeValid 4634 (by decide)),by decide,by decide⟩
  intro _;exact matchesListed (by decide)
private theorem sites3 : UpperSites 3 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4671 4642; exact checkEdgeValid 4671 (by decide)),by decide,by decide⟩
  intro h;exact False.elim ((by decide : ¬needsPad 3=true) h)
private theorem sites4 : UpperSites 4 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4715 4686; exact checkEdgeValid 4715 (by decide)),by decide,by decide⟩
  intro _;exact matchesListed (by decide)
private theorem sites5 : UpperSites 5 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4752 4723; exact checkEdgeValid 4752 (by decide)),by decide,by decide⟩
  intro h;exact False.elim ((by decide : ¬needsPad 5=true) h)
private theorem sites6 : UpperSites 6 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4796 4767; exact checkEdgeValid 4796 (by decide)),by decide,by decide⟩
  intro _;exact matchesListed (by decide)
private theorem sites7 : UpperSites 7 := by
  refine ⟨by decide,?_,by decide,by decide,matchesListed (by decide),matchesListed (by decide),
    matchesListed (by decide),by decide,by decide,(by change directs .check 4832 4804; exact checkEdgeValid 4832 (by decide)),by decide,by decide⟩
  intro h;exact False.elim ((by decide : ¬needsPad 7=true) h)
theorem upperSites (k : Fin 8) : UpperSites k.val := by
  rcases k with ⟨k,b⟩;interval_cases k
  · exact sites0
  · exact sites1
  · exact sites2
  · exact sites3
  · exact sites4
  · exact sites5
  · exact sites6
  · exact sites7
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem upperGeometry (k : Fin 8) :
    nextWidth k≤86 ∧ width (16+k.val)≤171 ∧
    ((needsPad k)=false → width (16+k.val)=2*nextWidth k) ∧
    signExtend12 (BitVec.ofNat 12 (nextWidth k))=W (nextWidth k) ∧
    (upperHeaderOps k).all (fun c=>[Reg.x29,.x30,.x14].contains c.dst) ∧
    (upperHeaderOps k).all (fun c=>c.dst != .x0) ∧ Sym.requirements Sym.original (upperHeaderOps k)=[] ∧
    ((upperHeaderOps k).foldl Sym.bump Sym.original) .x29=.lit (W 16384) ∧
    ((upperHeaderOps k).foldl Sym.bump Sym.original) .x30=.lit (W 16384) ∧
    (needsPad k=true → ((upperHeaderOps k).foldl Sym.bump Sym.original) .x14=.lit (W (upperAddr (width (16+k.val))))) ∧
    (upperHeaderOps k).length≤9 :=by fin_cases k <;> decide
end CommitGolfCandidate.S4.Machine
