import CommitGolfCandidate.TwoPermutationPackedLeafFetch

namespace TwoPermutationPrototype.RV64.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 12000
set_option maxHeartbeats 720000

def chainPermInput (s : MachineState) : BitVec PERMUTATION_WIDTH := readBuffer s (s.getReg .x10).toNat 200
def chainPermReply (s : MachineState) (y : BitVec PERMUTATION_WIDTH) := writeBits s (s.getReg .x12) y

/-- Selector, width and primitive of the forward permutation call. -/
def ChainPermReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 200 ∧ state.getReg .x13 = 1

/-- The permutation width simplifies without expanding the byte reader. -/
theorem chain_read_width (state : MachineState) (address kind : Nat) (one : kind = 1) :
    BitVec.setWidth 1600 (readBuffer state address
      (((if kind = 0 then 512 else 1600) + 7) / 8)) =
      readBuffer state address 200 := by
  subst one
  exact BitVec.setWidth_eq _

/-- The real `oracleInput` accepts an aligned 200-byte window and an aligned 200-byte reply. -/
theorem chain_oracle_input (state : MachineState) (ready : ChainPermReady state)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceBound : (state.getReg .x10).toNat + 200 ≤ MEMORY_BYTES)
    (destinationBound : (state.getReg .x12).toNat + 200 ≤ MEMORY_BYTES) :
    oracleInput state = some (.inr (.inl (chainPermInput state))) := by
  rcases ready with ⟨_, width, kind⟩
  have kindNat : (state.getReg .x13).toNat = 1 := by rw [kind]; rfl
  have widthNat : (state.getReg .x11).toNat = 200 := by rw [width]; rfl
  simp [oracleInput, kindNat, widthNat, rangeValid, sourceAligned, destinationAligned,
    sourceBound, destinationBound, PERMUTATION_WIDTH, COMPRESSION_INPUT_LENGTH, chainPermInput]
  exact chain_read_width state _ _ kindNat

/-- One forward permutation syscall: eight cycles, one query, any 1600-bit reply. -/
theorem chain_perm_call (image : Image) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (fetched : fetch image state = some (.base .ECALL))
    (ready : ChainPermReady state)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceBound : (state.getReg .x10).toNat + 200 ≤ MEMORY_BYTES)
    (destinationBound : (state.getReg .x12).toNat + 200 ≤ MEMORY_BYTES) :
    execute image (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inr (.inl (chainPermInput state))))
          let result ← execute image fuel (chainPermReply state answer) allowCoins
          return result.charge 8 1) := by
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos ready.1,
    chain_oracle_input state ready sourceAligned destinationAligned sourceBound destinationBound]
  rfl

end TwoPermutationPrototype.RV64.Chain
