import CommitGolfCandidate.S4CodecCode
namespace CommitGolfCandidate.S4.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (pieces)

def listedByte (d : Bool) (k : Nat) : Prop :=
  stands (program d) (bytePC d k) (beginByte d k).instr ∧
  (d=true → stands .check (bytePC true (k+1)-1) (endByte k)) ∧
  ∀ p : Fin 4,p.val<pieces k → listed (program d) (piecePC d k p) (sequence d k p)
instance (d : Bool) (k : Nat) : Decidable (listedByte d k) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
private theorem falseBlock0 : ∀ w : Fin 30,listedByte false (30*0+w.val) := by decide
private theorem falseBlock1 : ∀ w : Fin 30,listedByte false (30*1+w.val) := by decide
private theorem falseBlock2 : ∀ w : Fin 30,listedByte false (30*2+w.val) := by decide
private theorem falseBlock3 : ∀ w : Fin 30,listedByte false (30*3+w.val) := by decide
private theorem falseBlock4 : ∀ w : Fin 30,listedByte false (30*4+w.val) := by decide
private theorem falseBlock5 : ∀ w : Fin 30,listedByte false (30*5+w.val) := by decide
private theorem falseBlock6 : ∀ w : Fin 30,listedByte false (30*6+w.val) := by decide
private theorem falseBlock7 : ∀ w : Fin 30,listedByte false (30*7+w.val) := by decide
private theorem falseBlock8 : ∀ w : Fin 30,listedByte false (30*8+w.val) := by decide
private theorem falseBlock9 : ∀ w : Fin 30,listedByte false (30*9+w.val) := by decide
private theorem falseBlock10 : ∀ w : Fin 30,listedByte false (30*10+w.val) := by decide
private theorem trueBlock0 : ∀ w : Fin 30,listedByte true (30*0+w.val) := by decide
private theorem trueBlock1 : ∀ w : Fin 30,listedByte true (30*1+w.val) := by decide
private theorem trueBlock2 : ∀ w : Fin 30,listedByte true (30*2+w.val) := by decide
private theorem trueBlock3 : ∀ w : Fin 30,listedByte true (30*3+w.val) := by decide
private theorem trueBlock4 : ∀ w : Fin 30,listedByte true (30*4+w.val) := by decide
private theorem trueBlock5 : ∀ w : Fin 30,listedByte true (30*5+w.val) := by decide
private theorem trueBlock6 : ∀ w : Fin 30,listedByte true (30*6+w.val) := by decide
private theorem trueBlock7 : ∀ w : Fin 30,listedByte true (30*7+w.val) := by decide
private theorem trueBlock8 : ∀ w : Fin 30,listedByte true (30*8+w.val) := by decide
private theorem trueBlock9 : ∀ w : Fin 30,listedByte true (30*9+w.val) := by decide
private theorem trueBlock10 : ∀ w : Fin 30,listedByte true (30*10+w.val) := by decide

theorem byteSites (d : Bool) (k : Nat) (hk : k<330) : listedByte d k := by
  let j:=k/30
  let w : Fin 30:=⟨k%30,by omega⟩
  have hx : k=30*j+w.val:=by dsimp [j,w];omega
  have h : j<11:=by dsimp [j];omega
  rw [hx]
  cases d <;> interval_cases j
  · exact falseBlock0 w
  · exact falseBlock1 w
  · exact falseBlock2 w
  · exact falseBlock3 w
  · exact falseBlock4 w
  · exact falseBlock5 w
  · exact falseBlock6 w
  · exact falseBlock7 w
  · exact falseBlock8 w
  · exact falseBlock9 w
  · exact falseBlock10 w
  · exact trueBlock0 w
  · exact trueBlock1 w
  · exact trueBlock2 w
  · exact trueBlock3 w
  · exact trueBlock4 w
  · exact trueBlock5 w
  · exact trueBlock6 w
  · exact trueBlock7 w
  · exact trueBlock8 w
  · exact trueBlock9 w
  · exact trueBlock10 w
end CommitGolfCandidate.S4.Codec
