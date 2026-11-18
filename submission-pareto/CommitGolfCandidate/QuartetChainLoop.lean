import CommitGolfCandidate.QuartetChainWords

/-! Paired salt expansion: each five-word packet makes two permutation calls.
The first call reads and writes S, the second reads S and writes S+176.
After the pair both cursors point at S+352: the last reply's hidden192-bit key
is followed by untouched zero bytes. 16000 packets are visited48 times, with
5399 packets skipped on the first visit. -/
namespace TwoPermutationPrototype.QuartetChain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64.Chain (chainPermInput chainPermReply ChainPermReady chain_perm_call)
open TwoPermutationPrototype.QuartetCommit (image codeWord fetch_decoded wordPC)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev nonceChainBase : Nat := 6979325984
abbrev nonceChainCount : Nat := 1525202
def nonceChainDest (j : Nat) := nonceChainBase + 176*j
def nonceChainSource (j : Nat) := nonceChainBase + 352*(j/2)
/-- Block copy executing call `j`. -/
def copyOf (j : Nat) := (j/2+5399) % unroll
def nonceChainPC (j : Nat) := if j = nonceChainCount then 4096+4*258366 else 4096+4*(178364+5*copyOf j+2*(j%2))
/-- Control instructions after call `j`: none inside a block, `bgeu; jal` at a block end, `bgeu` after the last. -/
def extra (j : Nat) := if j%2=1 ∧ copyOf j = unroll-1 then (if j+1 = nonceChainCount then 1 else 2) else 0
def nonceChainSteps (j : Nat) := 5*(j/2)+2*(j%2) + 2*((j/2+5399)/unroll) - (if j = nonceChainCount then 1 else 0)
def nonceChainCycles (j : Nat) := 19*(j/2)+9*(j%2) + 2*((j/2+5399)/unroll) - (if j = nonceChainCount then 1 else 0)

def nonceIncrements (s : MachineState) (j : Nat) :=
  if j%2=0 then execInstrBr s (.ADDI .x12 .x12 176)
  else execInstrBr (execInstrBr s (.ADDI .x10 .x10 352)) (.ADDI .x12 .x12 176)

def chainAdvance (s : MachineState) (j : Nat) (y : BitVec 1600) : MachineState :=
  (nonceIncrements (chainPermReply s y) j).setPC (BitVec.ofNat 64 (nonceChainPC (j+1)))

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
  unfold chainAdvance nonceIncrements
  split <;> simp only [execInstrBr,MachineState.getReg_setPC,chainPermReply,
    MachineState.getReg_setReg_ne _ _ _ _ ha.symm,
    MachineState.getReg_setReg_ne _ _ _ _ hb.symm]
  all_goals exact writeBits_register ..

theorem chain_advance_frame (s : MachineState) (j : Nat) (y : BitVec 1600)
    (h : NonceChainFrame s j) : NonceChainFrame (chainAdvance s j y) (j+1) := by
  have keep (r : Reg) (ha : r ≠ .x10 := by decide) (hb : r ≠ .x12 := by decide) :=
    chain_advance_register s j y r ha hb
  refine ⟨rfl, ⟨(keep .x5).trans h.ready.1, (keep .x11).trans h.ready.2.1,
    (keep .x13).trans h.ready.2.2⟩, ?_, ?_, (keep .x7).trans h.limit⟩
  · by_cases even : j%2=0
    · have same : (j+1)/2=j/2 := by omega
      simp only [chainAdvance,nonceIncrements,if_pos even]
      change (writeBits s (s.getReg .x12) y).getReg .x10 = _
      rw [writeBits_register,h.input]
      simp only [nonceChainSource,same]
    · have next : (j+1)/2=j/2+1 := by omega
      simp only [chainAdvance,nonceIncrements,if_neg even]
      change (writeBits s (s.getReg .x12) y).getReg .x10 + 352#64 = _
      rw [writeBits_register,h.input]
      unfold nonceChainSource
      rw [next,show nonceChainBase+352*(j/2+1)=nonceChainBase+352*(j/2)+352 by omega]
      simp only [BitVec.ofNat_add]
  · have address : nonceChainDest (j+1)=nonceChainDest j+176 := by unfold nonceChainDest;omega
    unfold chainAdvance nonceIncrements
    split <;> change (writeBits s (s.getReg .x12) y).getReg .x12+176#64=_
    all_goals rw [writeBits_register,h.output,address,BitVec.ofNat_add]

theorem nonce_increments_execute (e j : Nat) (he : e < unroll) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(178364+5*e+2*(j%2)+1))) (fuel : Nat) :
    execute image ((1+j%2)+fuel) s true =
      (do let r ← execute image fuel (nonceIncrements s j) true
          return r.charge (1+j%2) 0) := by
  by_cases even : j%2=0
  · have first := nonce_chain_packet e 1 he (by decide) s (by simpa only [even] using pc)
    rw [even]
    simpa only [nonceIncrements,if_pos even,packetOp,instructionCycles,
      show 1+fuel=fuel+1 by omega] using
      (execute_ordinary_step image (.base (.ADDI .x12 .x12 176)) s
        (execInstrBr s (.ADDI .x12 .x12 176)) fuel true first rfl)
  · have odd : j%2=1 := by omega
    let mid := execInstrBr s (.ADDI .x10 .x10 352)
    have first := nonce_chain_packet e 3 he (by decide) s (by simpa only [odd] using pc)
    have mp : mid.pc = BitVec.ofNat 64 (4096+4*(178364+5*e+4)) := by
      change s.pc+4=_
      rw [pc,odd,show 4096+4*(178364+5*e+4)=(4096+4*(178364+5*e+2*1+1))+4 by omega]
      simp only [BitVec.ofNat_add]
      rfl
    have second := nonce_chain_packet e 4 he (by decide) mid mp
    rw [odd,show (1+1)+fuel=(fuel+1)+1 by omega,
      execute_ordinary_step _ _ _ mid _ _ first rfl,
      execute_ordinary_step _ _ _ (nonceIncrements s j) _ _ second (by simp only [nonceIncrements,if_neg even]; rfl)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro r
    simp [Execution.charge,instructionCycles,packetOp] <;> omega

theorem nonce_reply_pc (s : MachineState) (y : BitVec PERMUTATION_WIDTH) :
    (chainPermReply s y).pc = s.pc + 4 := rfl

theorem nonce_increments_pc (s : MachineState) (j : Nat) :
    (nonceIncrements s j).pc = s.pc+BitVec.ofNat 64 (4*(1+j%2)) := by
  by_cases even : j%2=0
  · simp only [nonceIncrements,if_pos even,even]; rfl
  · have odd : j%2=1 := by omega
    simp only [nonceIncrements,if_neg even,odd]
    change s.pc+4+4=s.pc+8
    rw [BitVec.add_assoc]
    rfl

theorem chain_advance_eq (s : MachineState) (j : Nat) (y : BitVec PERMUTATION_WIDTH) :
    chainAdvance s j y = (nonceIncrements (chainPermReply s y) j).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := rfl

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
