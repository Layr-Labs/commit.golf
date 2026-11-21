import CommitGolfCandidate.QuadCommitExecution
import CommitGolfCandidate.TwoPermutationCommitSetup

/-! Paired salt generator of the quad3 commit image (NoncePair recurrence, retargeted).
Words 247902..248069: x12 := x22, x7 := x22 + 0x10002000, then 762624 paired
permutation calls (32 five-word packets per latch, 64 calls per latch), then
x10 := x18, x12 := x9 and a jump back to word 18.

Each five-word packet makes two permutation calls: the first reads/writes S,
the second reads S (the first reply) and writes S+176.  After the pair both
cursors sit at S+352: the last reply's hidden 192-bit key is followed by
untouched zero bytes, so the next packet's first call reads
`seedState (hiddenKey previousReply)` — the NoncePair `inputTransform`. -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### The permutation syscall -/

def chainPermInput (s : MachineState) : BitVec PERMUTATION_WIDTH := readBuffer s (s.getReg .x10).toNat 200
def chainPermReply (s : MachineState) (y : BitVec PERMUTATION_WIDTH) := writeBits s (s.getReg .x12) y

/-- Selector, width and primitive of the forward permutation call. -/
def ChainPermReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 200 ∧ state.getReg .x13 = 1

theorem chain_read_width (state : MachineState) (address kind : Nat) (one : kind = 1) :
    BitVec.setWidth 1600 (readBuffer state address
      (((if kind = 0 then 512 else 1600) + 7) / 8)) =
      readBuffer state address 200 := by
  subst one
  exact BitVec.setWidth_eq _

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

/-! ### Fetching the generator and the patched setup words -/

def genOps : List Instr :=
  [.ADDI .x12 .x22 0,.LUI .x7 65538,.ADDI .x7 .x7 0,.ADD .x7 .x7 .x22] ++
  (List.replicate 32 [.ECALL,.ADDI .x12 .x12 176,.ECALL,.ADDI .x10 .x10 352,.ADDI .x12 .x12 176]).flatten ++
  [.BLTU .x12 .x7 7552,.ADDI .x10 .x18 0,.ADDI .x12 .x9 0,.JAL .x0 1104948]

/-- Words 0..18 of the NonceChain image (seed destination now `nonceChainSource 0` = base). -/
def nonceSetupOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,
   .LUI .x20 65537,.ADDI .x20 .x20 1768,.ADD .x20 .x9 .x20,
   .LUI .x22 442369,.ADDI .x22 .x22 0,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 0,.ADDI .x11 .x0 24,.ADDI .x11 .x11 0,
   .ECALL,
   .ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.JAL .x0 991540,.SLLI .x7 .x13 11]

private theorem gen_decoded : ∀ j : Fin 168,
    (genWords[j.val]?).bind decodeInstruction = some (.base ((genOps[j.val]?).getD .EBREAK)) := by
  decide +kernel

private theorem nonce_setup_decoded : ∀ i : Fin 19,
    (setupWords[i.val]?).bind decodeInstruction = some (.base ((nonceSetupOps[i.val]?).getD .EBREAK)) := by
  decide +kernel

/-- The 11 root copy/HALT words preceding the generator inside `rootWords`. -/
def rootCoreWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073]

def genPrefix := parentPrefix++parentCode++parentLatchWords++rootCoreWords

theorem gen_prefix_length : genPrefix.length=247902 := by
  unfold genPrefix
  simp only [List.length_append]
  rw [parent_prefix_length,parent_code_length]
  rfl

attribute [local irreducible] image leafCode quadCode quad2Code quad3Code parentCode decodeInstruction

theorem fetch_gen (j : Nat) (inside : j<168) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(247902+j))) :
    fetch image s=some (.base ((genOps[j]?).getD .EBREAK)) := by
  apply fetch_code_index s (247902+j) (by omega) pc
  have atIndex := code_segment_at genPrefix genWords []
    (by unfold image genPrefix parentPrefix quad3Prefix quad2Prefix quadPrefix rootWords rootCoreWords;simp only [List.append_assoc,List.append_nil]) j
    (Nat.lt_of_lt_of_le inside (by decide))
  rw [gen_prefix_length] at atIndex
  rw [atIndex]
  exact gen_decoded ⟨j,inside⟩

theorem fetch_nonce_setup (i : Nat) (inside : i<19) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) :
    fetch image s=some (.base ((nonceSetupOps[i]?).getD .EBREAK)) := by
  apply fetch_code_index s i (by omega) pc
  have word := code_segment_at [] setupWords
    (leafCode++leafLatchWords++quadSetupWords++quadCode++quadLatchWords++quad2SetupWords++quad2Code++quadLatchWords++
      quad3SetupWords++quad3Code++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords)
    (by unfold image;simp only [List.nil_append,List.append_assoc]) i inside
  simp only [List.length_nil,Nat.zero_add] at word
  rw [word]
  exact nonce_setup_decoded ⟨i,inside⟩

/-! ### The paired loop -/

abbrev nonceChainBase : Nat := 6106914848
abbrev nonceChainCount : Nat := 1525248
def nonceChainDest (j : Nat) := nonceChainBase + 176*j
def nonceChainSource (j : Nat) := nonceChainBase + 352*(j/2)
/-- Block copy executing call `j` (packet index within the latch). -/
def copyOf (j : Nat) := (j/2) % 32
def nonceChainPC (j : Nat) :=
  if j = nonceChainCount then 4096+4*248067
  else 4096+4*(247906+5*copyOf j+2*(j%2))
/-- Control instructions after call `j`: none inside a packet, `bgeu;jal` at a packet end. -/
def extra (j : Nat) := if j%2=1 ∧ copyOf j = 31 then (if j+1 = nonceChainCount then 1 else 2) else 0
def nonceChainSteps (j : Nat) := 5*(j/2)+2*(j%2) + j/64
def nonceChainCycles (j : Nat) := 19*(j/2)+9*(j%2) + j/64

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

/-- `x7` holds `T + 0x10002000`; `x12` reaches it only after the last call. -/
def chainLimit : Nat := nonceChainDest nonceChainCount

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

private def packet (k : Nat) : Instr :=
  if k=0 then .ECALL else if k=1 then .ADDI .x12 .x12 176
  else if k=2 then .ECALL else if k=3 then .ADDI .x10 .x10 352 else .ADDI .x12 .x12 176

private theorem packet_ops : ∀ u : Fin 32, ∀ k : Fin 5,
    (genOps[4+5*u.val+k.val]?).getD .EBREAK = packet k.val := by decide +kernel

theorem nonce_chain_packet (j k : Nat) (hj : j < 32) (hk : k < 5) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (995720+20*j+4*k)) :
    fetch image s = some (.base (packet k)) := by
  have fetched := fetch_gen (4+5*j+k) (by omega) s (by rw [pc];congr 1;omega)
  rw [fetched]
  exact congrArg (fun i => some (Instruction.base i)) (packet_ops ⟨j,hj⟩ ⟨k,hk⟩)

theorem nonce_chain_latch (s : MachineState) (pc : s.pc=996360) :
    fetch image s=some (.base (.BLTU .x12 .x7 7552)) :=
  fetch_gen 164 (by decide) s pc

def nonceIncrementsEven (s : MachineState) := execInstrBr s (.ADDI .x12 .x12 176)
def nonceIncrementsOdd (s : MachineState) :=
  execInstrBr (execInstrBr s (.ADDI .x10 .x10 352)) (.ADDI .x12 .x12 176)

theorem nonce_increments_execute (j : Nat) (hj : j < 32) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (995720+20*j+4)) (fuel : Nat) :
    execute image (1+fuel) s true =
      (do let r ← execute image fuel (nonceIncrementsEven s) true
          return r.charge 1 0) := by
  have first := nonce_chain_packet j 1 hj (by decide) s pc
  rw [show 1+fuel = fuel+1 by omega,
    execute_ordinary_step _ _ _ (nonceIncrementsEven s) _ _ first rfl]
  simp [Execution.charge, instructionCycles, packet]

theorem nonce_latch_pc (s : MachineState) (j : Nat) (endGroup : j%64=63)
    (hj : j < nonceChainCount) (pc : s.pc=996360)
    (output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest (j+1)))
    (limit : s.getReg .x7 = BitVec.ofNat 64 chainLimit) :
    execInstrBr s (.BLTU .x12 .x7 7552) = s.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := by
  have comp : (s.getReg .x12).ult (s.getReg .x7) = decide (j+1<nonceChainCount) := by
    rw [output,limit]
    simp only [BitVec.ult, BitVec.toNat_ofNat,nonceChainDest,chainLimit]
    rw [Nat.mod_eq_of_lt (by dsimp [nonceChainBase,nonceChainCount] at *;omega),
      Nat.mod_eq_of_lt (by decide)]
    simp only [Nat.add_lt_add_iff_left,Nat.mul_lt_mul_left (by decide : 0<176)]
  simp only [execInstrBr,comp,pc,nonceChainPC]
  by_cases last : j+1=nonceChainCount
  · simp [last] <;> rfl
  · have take : j+1<nonceChainCount := by omega
    have slot : (j+1)%64 = 0 := by omega
    have cop : copyOf (j+1) = 0 := by unfold copyOf; omega
    have par : (j+1)%2 = 0 := by omega
    simp [take,last,slot,cop,par] <;> rfl

theorem nonce_reply_pc (s : MachineState) (y : BitVec PERMUTATION_WIDTH) :
    (chainPermReply s y).pc = s.pc + 4 := rfl

theorem nonce_increments_pc (s : MachineState) : (nonceIncrementsEven s).pc = s.pc+4 := rfl

theorem chain_advance_eq (s : MachineState) (j : Nat) (y : BitVec PERMUTATION_WIDTH) :
    chainAdvance s j y = (nonceIncrements (chainPermReply s y) j).setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := rfl


theorem nonce_increments_execute_odd (j : Nat) (hj : j < 32) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (995720+20*j+12)) (fuel : Nat) :
    execute image (2+fuel) s true =
      (do let r ← execute image fuel (nonceIncrementsOdd s) true
          return r.charge 2 0) := by
  let mid := execInstrBr s (.ADDI .x10 .x10 352)
  have first := nonce_chain_packet j 3 hj (by decide) s pc
  have midPC : mid.pc = BitVec.ofNat 64 (995720+20*j+16) := by
    simp only [mid, execInstrBr, MachineState.getReg_setPC, MachineState.setPC]
    rw [pc]
    have hnat : (995720 + 20 * j + 12) + 4 = 995720 + 20 * j + 16 := by omega
    have hlt : 995720 + 20 * j + 12 < 2 ^ 64 := by omega
    have hlt2 : 995720 + 20 * j + 16 < 2 ^ 64 := by omega
    have hlt3 : (995720 + 20 * j + 12) + 4 < 2 ^ 64 := by omega
    have h4 : (4 : BitVec 64).toNat = 4 := by simp [BitVec.toNat_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [h4, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt3]
  have second := nonce_chain_packet j 4 hj (by decide) mid midPC
  rw [show 2+fuel = (fuel+1)+1 by omega,
    execute_ordinary_step _ _ _ mid _ _ first rfl,
    execute_ordinary_step _ _ _ (nonceIncrementsOdd s) _ _ second rfl]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro r
  simp [Execution.charge, instructionCycles, packet, nonceIncrementsOdd, mid] <;> omega

end TwoPermutationPrototype.Quad.Commit.Chain
