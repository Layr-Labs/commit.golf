import CommitGolfCandidate.NonceChainSyscall

/-! The nonce expansion loop, including its latch after every 64th call. -/
namespace TwoPermutationPrototype.RV64.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev nonceChainBase : Nat := 5637148704
abbrev nonceChainCount : Nat := 1525248
def nonceChainDest (j : Nat) := nonceChainBase + 176*j
def nonceChainSource (j : Nat) := (nonceChainBase - 176) + 176*j
def nonceChainPC (j : Nat) := if j = nonceChainCount then 937516 else 936744 + 12*(j%64)
def nonceChainSteps (j : Nat) := 3*j + j/64
def nonceChainCycles (j : Nat) := 10*j + j/64

def chainAdvance (s : MachineState) (j : Nat) (y : BitVec 1600) : MachineState :=
  let after := writeBits s (s.getReg .x12) y
  let inc := execInstrBr (execInstrBr after (.ADDI .x10 .x10 176)) (.ADDI .x12 .x12 176)
  inc.setPC (BitVec.ofNat 64 (nonceChainPC (j+1)))

def chainRun (j : Nat) (s : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure s
  | n+1 => do
    let y ← World.query (.inr (.inr (.inl (chainPermInput s))))
    chainRun (j+1) (chainAdvance s j y) n

structure NonceChainFrame (s : MachineState) (j : Nat) : Prop where
  pc : s.pc = BitVec.ofNat 64 (nonceChainPC j)
  ready : ChainPermReady s
  input : s.getReg .x10 = BitVec.ofNat 64 (nonceChainSource j)
  output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest j)
  limit : s.getReg .x7 = BitVec.ofNat 64 (nonceChainDest nonceChainCount)

theorem chain_advance_register (s : MachineState) (j : Nat) (y : BitVec 1600) (r : Reg)
    (ha : r ≠ .x10) (hb : r ≠ .x12) : (chainAdvance s j y).getReg r = s.getReg r := by
  simp only [chainAdvance,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ ha.symm,
    MachineState.getReg_setReg_ne _ _ _ _ hb.symm,writeBits_register]

theorem chain_advance_frame (s : MachineState) (j : Nat) (y : BitVec 1600)
    (h : NonceChainFrame s j) : NonceChainFrame (chainAdvance s j y) (j+1) := by
  have keep (r : Reg) (ha : r ≠ .x10 := by decide) (hb : r ≠ .x12 := by decide) :=
    chain_advance_register s j y r ha hb
  refine ⟨rfl, ⟨(keep .x5).trans h.ready.1, (keep .x11).trans h.ready.2.1,
    (keep .x13).trans h.ready.2.2⟩, ?_, ?_, (keep .x7).trans h.limit⟩
  · change _ + 176#64 = _
    rw [writeBits_register,h.input]
    unfold nonceChainSource
    rw [show nonceChainBase-176+176*(j+1) = nonceChainBase-176+176*j+176 by omega]
    simp only [BitVec.ofNat_add]
  · change _ + 176#64 = _
    change (writeBits s (s.getReg .x12) y).getReg .x12 + 176#64 = _
    rw [writeBits_register,h.output]
    unfold nonceChainDest
    rw [show nonceChainBase+176*(j+1) = nonceChainBase+176*j+176 by omega]
    simp only [BitVec.ofNat_add]

private def triple (k : Nat) : Instr :=
  if k=0 then .ECALL else if k=1 then .ADDI .x10 .x10 176 else .ADDI .x12 .x12 176

private theorem triple_words : ∀ u : Fin 64, ∀ k : Fin 3,
    Manifest.decodeBase (packed_wideCodeWord (233162+3*u.val+k.val)) = some (triple k.val) := by decide +kernel

theorem nonce_chain_triple (j k : Nat) (hj : j < 64) (hk : k < 3) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (936744+12*j+4*k)) :
    fetch packedWideCommitImage s = some (.base (triple k)) := by
  apply packed_wide_fetch_decoded s (233162+3*j+k) (by omega) _ _ (triple_words ⟨j,hj⟩ ⟨k,hk⟩)
  rw [pc]
  congr 1
  omega

theorem nonce_chain_latch (s : MachineState) (pc : s.pc=937512) :
    fetch packedWideCommitImage s=some (.base (.BLTU .x12 .x7 7424)) :=
  packed_wide_fetch_decoded s 233354 (by decide) pc _ (by decide +kernel)

def nonceIncrements (s : MachineState) := execInstrBr
  (execInstrBr s (.ADDI .x10 .x10 176)) (.ADDI .x12 .x12 176)

theorem nonce_increments_execute (j : Nat) (hj : j < 64) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (936744+12*j+4)) (fuel : Nat) :
    execute packedWideCommitImage (2+fuel) s true =
      (do let r ← execute packedWideCommitImage fuel (nonceIncrements s) true
          return r.charge 2 0) := by
  let mid := execInstrBr s (.ADDI .x10 .x10 176)
  have first := nonce_chain_triple j 1 hj (by decide) s pc
  have mp : mid.pc = BitVec.ofNat 64 (936744+12*j+4*2) := by
    change s.pc+4=_
    rw [pc,show 936744+12*j+4*2 = (936744+12*j+4)+4 by omega]
    simp only [BitVec.ofNat_add]
    rfl
  have second := nonce_chain_triple j 2 hj (by decide) mid mp
  rw [show 2+fuel = (fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ mid _ _ first rfl,
    execute_ordinary_step _ _ _ (nonceIncrements s) _ _ second rfl]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro r
  simp [Execution.charge,instructionCycles,triple] <;> omega

theorem nonce_latch_pc (s : MachineState) (j : Nat) (endGroup : j%64=63)
    (hj : j < nonceChainCount) (pc : s.pc=937512)
    (output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest (j+1)))
    (limit : s.getReg .x7 = BitVec.ofNat 64 (nonceChainDest nonceChainCount)) :
    execInstrBr s (.BLTU .x12 .x7 7424) = s.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := by
  have comp : (s.getReg .x12).ult (s.getReg .x7) = decide (j+1<nonceChainCount) := by
    rw [output,limit]
    simp only [BitVec.ult, BitVec.toNat_ofNat,nonceChainDest]
    rw [Nat.mod_eq_of_lt (by dsimp [nonceChainBase,nonceChainCount] at *; omega),
      Nat.mod_eq_of_lt (by decide)]
    simp only [Nat.add_lt_add_iff_left,Nat.mul_lt_mul_left (by decide : 0<176)]
  simp only [execInstrBr,comp,pc,nonceChainPC]
  by_cases last : j+1=nonceChainCount
  · simp [last] <;> rfl
  · have take : j+1<nonceChainCount := by omega
    have slot : (j+1)%64 = 0 := by omega
    simp [take,last,slot] <;> rfl

theorem nonce_reply_pc (s : MachineState) (y : BitVec PERMUTATION_WIDTH) :
    (chainPermReply s y).pc = s.pc + 4 := rfl

theorem nonce_increments_pc (s : MachineState) : (nonceIncrements s).pc = s.pc+4+4 := rfl

theorem chain_advance_eq (s : MachineState) (j : Nat) (y : BitVec PERMUTATION_WIDTH) :
    chainAdvance s j y = (nonceIncrements (chainPermReply s y)).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := rfl

end TwoPermutationPrototype.RV64.Chain
