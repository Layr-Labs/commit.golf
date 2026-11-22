import CommitGolfCandidate.Layout2Views
import CommitGolfCandidate.Layout2Invariant
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def clobbers : Block → List Reg
  | .entry => []
  | .guard => [.x6]
  | .empty => []
  | .init => [.x8, .x9, .x20, .x21]
  | .choose => []
  | .full => [.x18, .x19, .x31]
  | .next => [.x8, .x9]
  | .tail => []
  | .one => [.x5]
  | .two => [.x5]
  | .three => [.x18, .x5]
  | .pair => [.x18, .x5]
  | .single => [.x18, .x5]
  | .callTail => [.x19, .x31]
  | .clearHead => [.x5, .x6]
  | .clearCell => [.x5]
  | .restore => [.x5, .x7, .x28, .x29, .x30, .x31, .x8, .x9, .x18, .x19, .x20, .x21, .x6]
  | .copyHead => [.x5, .x6, .x7]
  | .copyByte => [.x28, .x5, .x6]
  | .writeHead => [.x5]
  | .byteHead => [.x6, .x28]
  | .bitStep => [.x29, .x30, .x6, .x19, .x28]
  | .emitByte => [.x5]
  | .ret => []

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
theorem kept_of_regs {b : Block} {s t : MachineState} (h : ∀ r, t.getReg r=regOut s r b) :
    Kept (clobbers b) s t := by
  intro r free
  rw [h]
  cases b <;> cases r <;> first | exact (free (by decide)).elim | rfl

end CommitGolfCandidate.Layout2
