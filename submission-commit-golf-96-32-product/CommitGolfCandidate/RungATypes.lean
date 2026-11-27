import CommitGolfCandidate.RungAArithmetic
import CommitGolfCandidate.RungAGroup
import CommitGolfCandidate.TruncMask
set_option Elab.async false
set_option maxHeartbeats 1500000
attribute [local irreducible] CommitGolf.Riscv.readBuffer
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open S4.Machine (W Code Runs Safe)
open Late (pcAt nodeAddress rowAddress levelCount Digest)
def inputAddr (h j : Nat) := if h=0 then finalRowAddress j else rowAddress (h-1) j
def masked (h : Nat) := decide (2≤h)
def hashLength (h : Nat) := if masked h then 2 else 1
def hashCycles (h : Nat) := if masked h then 9 else 8
def hashSite (site h : Nat) : Prop :=
    site+hashLength h≤Code.opening.count ∧ S4.Machine.stands .opening site .ECALL ∧
    (masked h=true → S4.Machine.stands .opening (site+1) (.SH .x12 .x0 30))
instance (site h : Nat) : Decidable (hashSite site h):=inferInstanceAs (Decidable (_ ∧ _ ∧ (_ → _)))
def inputBlock (H : Compression) (td : Late.Trapdoor) (h j : Nat) : Late.Block :=
  if h=0 then Late.slice td (finalRowAddress j) 96 else
    let u:=h-1
    let lane:=fun k=>if k<S4.radix u ∧ S4.radix u*j+k<levelCount u then rebuildDigest H td u (S4.radix u*j+k)
      else Late.slice td (Late.unusedSlotAddr u j k) 32
    lane 2++lane 1++lane 0

end CommitGolfCandidate.RungA
