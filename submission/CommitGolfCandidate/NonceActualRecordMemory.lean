import CommitGolfCandidate.NonceRecordMemory
import CommitGolfCandidate.NonceCompactReady

/-! The exact compacted record and frame are consequences of the actual
image's straight-line record block, under its established buffer invariant.
Pairs are executed in increasing word order, so every source word is read
before any store can reach it. -/
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

/-- Memory after the first `count` load/store pairs of a block. -/
structure NonceRecordPairsMemory (source target count : Nat) (before after : MachineState) : Prop where
  copied : ∀ index < count,
    after.getMem (address target index)=before.getMem (address source (nonceRecordSourceWord index))
  frame : ∀ location, (∀ index < count, location ≠ address target index) →
    after.getMem location=before.getMem location

private theorem address_ne_of_ne (base left right : Nat) (different : left ≠ right)
    (small : base+8*left<2^64 ∧ base+8*right<2^64) :
    address base left ≠ address base right := by
  rcases Nat.lt_or_gt_of_ne different with less | greater
  · exact address_ne (by omega) small.2
  · exact Ne.symm (address_ne (by omega) small.1)

theorem nonce_record_pairs_memory (source target : Nat) (state : MachineState)
    (window : NonceRecordWindow source target state) (count : Nat) (bounded : count ≤ 67) :
    NonceRecordPairsMemory source target count state (nonceRecordPairs state count) := by
  have sourceWindow:=window.source_window
  have ordered:=window.ordered
  induction count with
  | zero =>
    constructor
    · intro index inside
      omega
    · intro location _
      rfl
  | succ count ih =>
    have previous:=ih (by omega)
    let current := nonceRecordPairs state count
    have sourceReg : current.getReg .x23=BitVec.ofNat 64 source :=
      (nonce_record_pairs_register state count .x23 (by decide)).trans window.source
    have targetReg : current.getReg .x25=BitVec.ofNat 64 target :=
      (nonce_record_pairs_register state count .x25 (by decide)).trans window.target
    have sourceBound:=nonce_record_source_le count
    have memory : (nonceRecordPairs state (count+1)).mem=
        (current.setMem (address target count)
          (current.getMem (address source (nonceRecordSourceWord count)))).mem := by
      change (nonceRecordPair current count).mem=_
      rw [nonce_record_pair_memory,
        nonce_record_target_address current target count targetReg (by omega),
        nonce_record_source_address current source count sourceReg (by omega)]
    have unread : current.getMem (address source (nonceRecordSourceWord count))=
        state.getMem (address source (nonceRecordSourceWord count)) := by
      apply previous.frame
      intro index inside
      apply Ne.symm
      apply address_ne (by omega)
      norm_num [MEMORY_BYTES] at sourceWindow
      omega
    have read (location : Word) : (nonceRecordPairs state (count+1)).getMem location=
        (current.setMem (address target count)
          (current.getMem (address source (nonceRecordSourceWord count)))).getMem location := by
      simp only [MachineState.getMem, memory]
    constructor
    · intro index inside
      rw [read]
      by_cases last : index=count
      · subst index
        rw [MachineState.getMem_setMem_eq, unread]
      · rw [MachineState.getMem_setMem_ne]
        · exact previous.copied index (by omega)
        · apply address_ne_of_ne target index count last
          norm_num [MEMORY_BYTES] at sourceWindow
          omega
    · intro location outside
      rw [read, MachineState.getMem_setMem_ne (outside count (by omega))]
      exact previous.frame location (fun index inside => outside index (by omega))

theorem nonce_record_pairs_move (source target : Nat) (before after : MachineState)
    (pairs : NonceRecordPairsMemory source target 67 before after) :
    NonceRecordMove source target before after :=
  ⟨fun index inside => pairs.copied index inside, fun location outside => pairs.frame location outside⟩

theorem nonce_compact_record_mem (state : MachineState) :
    (nonceRecordPairs state 67).mem=(nonceCompactRecordState state).mem :=
  (nonce_record_tail_memory (nonceRecordPairs state 67)).symm

theorem nonce_compact_actual_record_memory (base count remaining : Nat) (state : MachineState)
    (ready : NonceCompactRecordReady base count remaining state) :
    NonceRecordMove (base+544*(count-remaining)) (base+536*(count-remaining))
      state (nonceCompactRecordState state) :=
  nonce_record_move_transfer _ _ state (nonceRecordPairs state 67) state (nonceCompactRecordState state)
    (nonce_record_pairs_move _ _ state _
      (nonce_record_pairs_memory _ _ state (nonce_compact_record_window base count remaining state ready)
        67 (Nat.le_refl 67)))
    rfl (nonce_compact_record_mem state)

end CommitGolfCandidate
