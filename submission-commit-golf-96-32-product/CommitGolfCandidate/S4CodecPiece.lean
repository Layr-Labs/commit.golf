import CommitGolfCandidate.S4CodecStep
namespace CommitGolfCandidate.S4.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (group carrier prev pieces)
open Late (pcAt)
abbrev CodeLaw := ∀ d k,k<330 →
  stands (program d) (bytePC d k) (beginByte d k).instr ∧
  (d=true → stands .check (bytePC true (k+1)-1) (endByte k)) ∧
  ∀ p : Fin 4,p.val<pieces k → listed (program d) (piecePC d k p) (sequence d k p)

theorem runPiece (law : CodeLaw) (d : Bool) (s : MachineState) (base k p : Nat) (hk : k<330) (hp : p<pieces k)
    (pc : s.pc=pcAt (piecePC d k p)) (ptr : s.getReg .x21=W (base+Carry.prev (group k p)))
    (room : base+70410≤MEMORY_BYTES) :
    ∃ t,PieceResult d s t k p (base+carrier (group k p)) := by
  have p4 : p<4:=by unfold pieces at hp;split at hp <;> omega
  exact runPieceAt d s base k p hk hp pc ptr room (matchesListed ((law d k hk).2.2 ⟨p,p4⟩ hp))
end CommitGolfCandidate.S4.Codec
