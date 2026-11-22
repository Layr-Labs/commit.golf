import CommitGolfCandidate.Layout2EffectsControl
import CommitGolfCandidate.Layout2EffectsTail
import CommitGolfCandidate.Layout2EffectsClear
import CommitGolfCandidate.Layout2EffectsCopy
import CommitGolfCandidate.Layout2EffectsBits
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
theorem effects (b : Block) (s : MachineState) (here : s.pc=pc b.start) :
    (∀ r, (after b s).getReg r=regOut s r b) ∧ (after b s).mem=(memOut s b).mem ∧
    (after b s).pc=pcOut s b ∧ (Ready s b.ops ↔ accessible s b) := by
  cases b with
  | entry => exact effects_entry s here
  | guard => exact effects_guard s here
  | empty => exact effects_empty s here
  | init => exact effects_init s here
  | choose => exact effects_choose s here
  | full => exact effects_full s here
  | next => exact effects_next s here
  | tail => exact effects_tail s here
  | one => exact effects_one s here
  | two => exact effects_two s here
  | three => exact effects_three s here
  | pair => exact effects_pair s here
  | single => exact effects_single s here
  | callTail => exact effects_callTail s here
  | clearHead => exact effects_clearHead s here
  | clearCell => exact effects_clearCell s here
  | restore => exact effects_restore s here
  | copyHead => exact effects_copyHead s here
  | copyByte => exact effects_copyByte s here
  | writeHead => exact effects_writeHead s here
  | byteHead => exact effects_byteHead s here
  | bitStep => exact effects_bitStep s here
  | emitByte => exact effects_emitByte s here
  | ret => exact effects_ret s here
end CommitGolfCandidate.Layout2
