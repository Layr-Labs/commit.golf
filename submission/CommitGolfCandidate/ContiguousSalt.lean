import CommitGolfCandidate.CursorSaltExecution
import CommitGolfCandidate.NonceSaltExecution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
abbrev ContiguousSaltFetched := NonceSaltFetched

theorem contiguous_salt_execute (image : Image) (fetched : ContiguousSaltFetched image)
    (state : MachineState) (pc : state.pc=4456)
    (sourceValid : ∀ word : Fin 4,accessValid (state.getReg .x18+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid (state.getReg .x10+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) :
    execute image (7+fuel) state true=
      (do let result ← execute image fuel ((cursorSaltCopyState state).setPC 4484) true
          return result.charge 7 0) := by
  have run := nonce_salt_execute image fetched state pc
    (fun word : Fin 3 => sourceValid ⟨word.val,by omega⟩) destinationValid fuel
  rw [nonce_salt_virtual,show nonceVirtualSaltState state=cursorSaltCopyState state from rfl] at run
  simpa only [pc,show (4456:Word)+28=4484 by decide] using run
end CommitGolfCandidate
