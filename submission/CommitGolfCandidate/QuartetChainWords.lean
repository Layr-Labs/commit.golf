import CommitGolfCandidate.NonceChainSyscall

/-! Fixed artifact words for the paired generator. Kept separate from execution
lemmas so an execution-proof repair does not recheck80000 unchanged words. -/
namespace TwoPermutationPrototype.QuartetChain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.QuartetCommit (image codeWord fetch_decoded wordPC)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
abbrev unroll : Nat := 16000

/-! ### Instruction facts -/

def packetOp (k : Nat) : Instr :=
  if k=0 ∨ k=2 then .ECALL else if k=3 then .ADDI .x10 .x10 352 else .ADDI .x12 .x12 176

private def packetWord (k : Nat) : BitVec 32 :=
  if k=0 ∨ k=2 then 115 else if k=3 then 369427731 else 184944147

private theorem packet_word_decoded (k : Fin 5) :
    TwoPermutationPrototype.RV64.Manifest.decodeBase (packetWord k.val) = some (packetOp k.val) := by
  fin_cases k <;> decide +kernel

private def BlockTile (tile : Nat) : Prop :=
  ∀ u : Fin 256, ∀ k : Fin 5, 256*tile+u.val < unroll →
    codeWord (178364+5*(256*tile+u.val)+k.val) = packetWord k.val

set_option maxRecDepth 200000 in
private theorem tiles : ∀ tile : Fin 63, BlockTile tile.val := by
  intro tile
  unfold BlockTile
  fin_cases tile <;> decide +kernel

theorem nonce_chain_packet (e k : Nat) (he : e < unroll) (hk : k < 5) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(178364+5*e+k))) :
    fetch image s = some (.base (packetOp k)) := by
  have tile := tiles ⟨e/256, by unfold unroll at he; omega⟩ ⟨e%256, by omega⟩ ⟨k, hk⟩
    (by simp only []; omega)
  have pos : 256*(e/256)+e%256 = e := by omega
  simp only [pos] at tile
  apply fetch_decoded s (178364+5*e+k) (by unfold unroll at he; omega) pc
  rw [tile]
  exact packet_word_decoded ⟨k, hk⟩

theorem nonce_chain_latch (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*258364)) :
    fetch image s=some (.base (.BGEU .x12 .x7 8)) :=
  fetch_decoded s 258364 (by decide) pc _ (by decide +kernel)

theorem nonce_chain_back (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*258365)) :
    fetch image s=some (.base (.JAL .x0 1777148)) :=
  fetch_decoded s 258365 (by decide) pc _ (by decide +kernel)

end TwoPermutationPrototype.QuartetChain
