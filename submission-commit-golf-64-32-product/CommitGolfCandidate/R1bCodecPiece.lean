import CommitGolfCandidate.R1bCodecStep
namespace CommitGolfCandidate.R1b.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (group carrier prev pieces)
open R1bPC (pcAt)
abbrev CodeLaw := ∀ d k,k<352 →
  stands (program d) (bytePC d k) (beginByte d k).instr ∧
  (d=true → stands .check (bytePC true (k+1)-1) (endByte k)) ∧
  ∀ p : Fin 4,p.val<pieces k → listed (program d) (piecePC d k p) (sequence d k p)

theorem runPiece (law : CodeLaw) (d : Bool) (s : MachineState) (base k p : Nat) (hk : k<352) (hp : p<pieces k)
    (pc : s.pc=pcAt (piecePC d k p)) (ptr : s.getReg .x21=W (base+Carry.prev (group k p)))
    (room : base+67840≤MEMORY_BYTES) :
    ∃ t,PieceResult d s t k p (base+carrier (group k p)) := by
  have p4 : p<4:=by unfold pieces at hp;split at hp <;> omega
  exact runPieceAt d s base k p hk hp pc ptr room (matchesListed ((law d k hk).2.2 ⟨p,p4⟩ hp))
end CommitGolfCandidate.R1b.Codec
