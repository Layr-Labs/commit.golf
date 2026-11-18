import CommitGolfCandidate.NonceChainSyscall

/-! The chain loop of variant B', in the form of submission c28dd9ca's `NonceChainLoop` (dadon):
27,731 unrolled copies of `ecall; addi a0,a0,176; addi a2,a2,176` at words 178364-261556, entered
at copy 3 so that the 1,525,202 calls end exactly at the block's end; each block end is
`bgeu a2,t2,8; jal zero,BLOCK`, the branch being taken after the last call. -/
namespace TwoPermutationPrototype.QuartetChain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64.Chain (chainPermInput chainPermReply ChainPermReady chain_perm_call)
open TwoPermutationPrototype.QuartetCommit (image codeWord fetch_decoded wordPC)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev nonceChainBase : Nat := 6979325984
abbrev nonceChainCount : Nat := 1525202
abbrev unroll : Nat := 27731
def nonceChainDest (j : Nat) := nonceChainBase + 176*j
def nonceChainSource (j : Nat) := (nonceChainBase - 176) + 176*j
/-- Block copy executing call `j`. -/
def copyOf (j : Nat) := (j+3) % unroll
def nonceChainPC (j : Nat) := if j = nonceChainCount then 4096+4*261559 else 4096+4*(178364+3*copyOf j)
/-- Control instructions after call `j`: none inside a block, `bgeu; jal` at a block end, `bgeu` after the last. -/
def extra (j : Nat) := if copyOf j = unroll-1 then (if j+1 = nonceChainCount then 1 else 2) else 0
def nonceChainSteps (j : Nat) := 3*j + 2*((j+3)/unroll) - (if j = nonceChainCount then 1 else 0)
def nonceChainCycles (j : Nat) := 10*j + 2*((j+3)/unroll) - (if j = nonceChainCount then 1 else 0)

def chainAdvance (s : MachineState) (j : Nat) (y : BitVec 1600) : MachineState :=
  let after := writeBits s (s.getReg .x12) y
  let inc := execInstrBr (execInstrBr after (.ADDI .x10 .x10 176)) (.ADDI .x12 .x12 176)
  inc.setPC (BitVec.ofNat 64 (nonceChainPC (j+1)))

def chainRun (j : Nat) (s : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure s
  | n+1 => do
    let y ← World.query (.inr (.inr (.inl (chainPermInput s))))
    chainRun (j+1) (chainAdvance s j y) n

/-- `t2` holds `T + 2^28`; `a2` reaches it only after the last call. -/
def chainLimit : Nat := nonceChainBase + 268435456

structure NonceChainFrame (s : MachineState) (j : Nat) : Prop where
  pc : s.pc = BitVec.ofNat 64 (nonceChainPC j)
  ready : ChainPermReady s
  input : s.getReg .x10 = BitVec.ofNat 64 (nonceChainSource j)
  output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest j)
  limit : s.getReg .x7 = BitVec.ofNat 64 chainLimit

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

/-! ### Instruction facts -/

def triple (k : Nat) : Instr :=
  if k=0 then .ECALL else if k=1 then .ADDI .x10 .x10 176 else .ADDI .x12 .x12 176

private def BlockTile (tile : Nat) : Prop :=
  ∀ u : Fin 256, ∀ k : Fin 3, 256*tile+u.val < unroll →
    TwoPermutationPrototype.RV64.Manifest.decodeBase (codeWord (178364+3*(256*tile+u.val)+k.val)) = some (triple k.val)

set_option maxRecDepth 200000 in
private theorem tiles : ∀ tile : Fin 109, BlockTile tile.val := by
  intro tile
  unfold BlockTile
  fin_cases tile <;> decide +kernel

theorem nonce_chain_triple (e k : Nat) (he : e < unroll) (hk : k < 3) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(178364+3*e+k))) :
    fetch image s = some (.base (triple k)) := by
  have tile := tiles ⟨e/256, by unfold unroll at he; omega⟩ ⟨e%256, by omega⟩ ⟨k, hk⟩
    (by simp only []; omega)
  have pos : 256*(e/256)+e%256 = e := by omega
  simp only [pos] at tile
  exact fetch_decoded s (178364+3*e+k) (by unfold unroll at he; omega) pc _ tile

theorem nonce_chain_latch (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*261557)) :
    fetch image s=some (.base (.BGEU .x12 .x7 8)) :=
  fetch_decoded s 261557 (by decide) pc _ (by decide +kernel)

theorem nonce_chain_back (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*261558)) :
    fetch image s=some (.base (.JAL .x0 1764376)) :=
  fetch_decoded s 261558 (by decide) pc _ (by decide +kernel)

def nonceIncrements (s : MachineState) := execInstrBr
  (execInstrBr s (.ADDI .x10 .x10 176)) (.ADDI .x12 .x12 176)

theorem nonce_increments_execute (e : Nat) (he : e < unroll) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(178364+3*e+1))) (fuel : Nat) :
    execute image (2+fuel) s true =
      (do let r ← execute image fuel (nonceIncrements s) true
          return r.charge 2 0) := by
  let mid := execInstrBr s (.ADDI .x10 .x10 176)
  have first := nonce_chain_triple e 1 he (by decide) s pc
  have mp : mid.pc = BitVec.ofNat 64 (4096+4*(178364+3*e+2)) := by
    change s.pc+4=_
    rw [pc,show 4096+4*(178364+3*e+2) = (4096+4*(178364+3*e+1))+4 by omega]
    simp only [BitVec.ofNat_add]
    rfl
  have second := nonce_chain_triple e 2 he (by decide) mid mp
  rw [show 2+fuel = (fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ mid _ _ first rfl,
    execute_ordinary_step _ _ _ (nonceIncrements s) _ _ second rfl]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro r
  simp [Execution.charge,instructionCycles,triple] <;> omega

theorem nonce_reply_pc (s : MachineState) (y : BitVec PERMUTATION_WIDTH) :
    (chainPermReply s y).pc = s.pc + 4 := rfl

theorem nonce_increments_pc (s : MachineState) : (nonceIncrements s).pc = s.pc+4+4 := rfl

theorem chain_advance_eq (s : MachineState) (j : Nat) (y : BitVec PERMUTATION_WIDTH) :
    chainAdvance s j y = (nonceIncrements (chainPermReply s y)).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := rfl

/-- At a block end, `bgeu a2,t2,8` falls through unless the last call has been made. -/
theorem latch_compare (s : MachineState) (j : Nat) (hj : j < nonceChainCount)
    (output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest (j+1)))
    (limit : s.getReg .x7 = BitVec.ofNat 64 chainLimit) :
    (s.getReg .x12).ult (s.getReg .x7) = decide (j+1<nonceChainCount) := by
  rw [output,limit]
  simp only [BitVec.ult, BitVec.toNat_ofNat,nonceChainDest,chainLimit]
  rw [Nat.mod_eq_of_lt (by dsimp [nonceChainBase,nonceChainCount] at *; omega),
    Nat.mod_eq_of_lt (by decide)]
  by_cases last : j+1 < nonceChainCount
  · simp only [last, decide_true]
    apply decide_eq_true
    dsimp [nonceChainCount] at last
    omega
  · simp only [last, decide_false]
    apply decide_eq_false
    dsimp [nonceChainCount] at last hj
    omega

end TwoPermutationPrototype.QuartetChain
