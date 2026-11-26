import CommitGolfCandidate.S4OpenFields
import CommitGolfCandidate.S4Edges
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (Fragment stands)
def recordPC (b : Bool) (lane : Nat) := if b then ([8, 554, 1210, 1792, 2448, 2994, 3650, 4232] : List Nat)[lane]?.getD 0 else 5281
def fieldPC (b : Bool) (lane : Nat) : Nat→Nat
  | 0=>recordPC b lane
  | q+1=>fieldPC b lane q+fieldSize b lane q
def movePC (b : Bool) (l q : Nat) := fieldPC b l q+(prepare b l q).length
def bumpPC (b : Bool) (l q : Nat) := movePC b l q+2*(moves b l q).widths.length
def fieldValid (b : Bool) (lane q : Nat) : Bool :=
  (Fragment.arithmetic (prepare b lane q)).valid .opening (fieldPC b lane q) (movePC b lane q) &&
  (Fragment.copy (moves b lane q)).valid .opening (movePC b lane q) (bumpPC b lane q) &&
  stands .opening (bumpPC b lane q) (advance b q)
theorem nextField (b : Bool) (l q : Nat) : fieldPC b l (q+1)=bumpPC b l q+1 := by
  simp only [fieldPC,fieldSize,bumpPC,movePC,Nat.add_assoc]
def totalCost (b : Bool) (l : Nat) : Nat→Nat | 0=>0 | k+1=>totalCost b l k+fieldCost b l k
theorem fieldLimit : ∀ b : Bool,∀ l : Fin 8,∀ q : Fin 26,q.val<fieldsIn b →
  (b=true ∨ l.val=0) → bumpPC b l q<17856 := by decide
theorem recordEnd : ∀ l : Fin 8,fieldPC true l 17+2=(if l.val+1<8 then recordPC true (l.val+1) else 4888) := by decide
theorem normalEnd : fieldPC false 0 26=5868 := by decide
end CommitGolfCandidate.S4.Open
