import CommitGolfCandidate.NonceRecordMemory
import CommitGolfCandidate.NonceCompactReady

/-! The exact compacted record and frame are consequences of the actual
image's two real word-copy calls, under its established buffer invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_record_move_transfer (source target : Nat)
    (before after before' after' : MachineState)
    (effect : NonceRecordMove source target before after)
    (first : before.mem=before'.mem) (last : after.mem=after'.mem) :
    NonceRecordMove source target before' after' := by
  constructor
  · intro index inside
    simpa only [MachineState.getMem, first, last] using effect.copied index inside
  · intro location outside
    simpa only [MachineState.getMem, first, last] using effect.frame location outside

theorem nonce_compact_actual_record_memory (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    NonceRecordMove (base+544*(count-remaining)) (base+536*(count-remaining))
      state (nonceCompactRecordState state) := by
  have nonceReady:=nonce_compact_nonce_ready base count remaining state ready
  have siblingsReady:=nonce_compact_siblings_ready base count remaining state ready
  have moves:=nonce_compact_record_moves state _ _ nonceReady siblingsReady
  have window:=ready.window
  have remainingLe:=ready.remaining_le
  have positive:=ready.positive
  have composed:=nonce_record_moves_compose
    (base+544*(count-remaining)) (base+536*(count-remaining))
    state (nonceCompactNonceCopied state) (nonceCompactSiblingsCopied state)
    (by omega) (by omega) (by omega) moves.1 moves.2.1
  exact nonce_record_move_transfer _ _ state (nonceCompactSiblingsCopied state)
    state (nonceCompactRecordState state) composed rfl moves.2.2.symm

end CommitGolfCandidate
