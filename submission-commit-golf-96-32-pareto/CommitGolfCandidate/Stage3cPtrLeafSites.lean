import CommitGolfCandidate.Stage3cPtrLeafGeom

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
set_option Elab.async false

theorem tile_at_call : ∀ j : Fin 128, ∀ c : Fin 4, ∀ p : Fin 3,
    tileOp (localIndex j.val + 3 * c.val + p.val) = callInstr j.val c.val p.val := by
  decide +kernel

theorem call_decoded (j : Fin 128) (c : Fin 4) (p : Fin 3) :
    decoded (4123 + localIndex j.val + 3 * c.val + p.val) =
      some (.base (callInstr j.val c.val p.val)) := by
  have bound : localIndex j.val + 3 * c.val + p.val < 1555 := by
    have fit := local_fits j
    have := c.isLt
    have := p.isLt
    omega
  have dec := tile_decode ⟨localIndex j.val + 3 * c.val + p.val, bound⟩
  rw [← Nat.add_assoc, ← Nat.add_assoc] at dec
  simpa [tile_at_call j c p] using dec

theorem call_sites (k : Nat) (c : Fin 4) :
    let j : Fin 128 := ⟨k % 128, Nat.mod_lt k (by decide)⟩
    let n := leafPC k + 3 * c.val
    Site .commit n (.ADDI .x10 (srcReg c.val) (BitVec.ofNat 12 (immRaw (srcOff j.val c.val)))) ∧
    Site .commit (n + 1) (.ADDI .x12 (dstReg c.val) (BitVec.ofNat 12 (immRaw (dstOff j.val c.val)))) ∧
    Site .commit (n + 2) .ECALL := by
  let j : Fin 128 := ⟨k % 128, Nat.mod_lt k (by decide)⟩
  have pc := leaf_pc_local k
  have inside : leafPC k + 3 * c.val + 2 < 11543 := by
    have slot := leaf_pc_slot k
    have := c.isLt
    omega
  refine ⟨decoded_site (by omega) ?_, decoded_site (by omega) ?_, decoded_site inside ?_⟩
  · have h := call_decoded j c ⟨0, by decide⟩
    simpa [pc, callInstr, srcReg] using h
  · have h := call_decoded j c ⟨1, by decide⟩
    simpa [pc, callInstr, dstReg] using h
  · have h := call_decoded j c ⟨2, by decide⟩
    simpa [pc, callInstr] using h

def tailAt (j e : Nat) : Instr := tileOp (localIndex j + 12 + e)

theorem tail_classified : ∀ j : Fin 128,
    ((j.val + 1) % 16 = 0 → tailAt j.val 0 = .ADD .x21 .x21 .x25) ∧
    ((j.val + 1) % 32 = 0 →
      tailAt j.val 1 = .ADD .x22 .x22 .x26 ∧
      tailAt j.val 2 = .ADDI .x23 .x23 (BitVec.ofNat 12 1536)) ∧
    ((j.val + 1) % 128 = 0 →
      tailAt j.val 3 = .ADDI .x20 .x20 (BitVec.ofNat 12 4095) ∧
      tailAt j.val 4 = .BEQ .x20 .x0 (BitVec.ofNat 13 8) ∧
      tailAt j.val 5 = .JAL .x0 (BitVec.ofNat 21 2090936)) := by
  decide +kernel

theorem tail_site (j : Fin 128) (e : Nat) (he : e < 6) :
    Site .commit (4123 + localIndex j.val + 12 + e) (tailAt j.val e) := by
  have bound : localIndex j.val + 12 + e < 1555 := by
    have fit := local_fits j
    omega
  have inside : 4123 + localIndex j.val + 12 + e < 11543 := by omega
  have dec := tile_decode ⟨localIndex j.val + 12 + e, bound⟩
  rw [← Nat.add_assoc, ← Nat.add_assoc] at dec
  exact decoded_site inside (by simpa [tailAt] using dec)

end CommitGolfCandidate.Chained.BinaryMachine
