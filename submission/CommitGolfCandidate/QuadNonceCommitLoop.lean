import CommitGolfCandidate.QuadCommitExecution
import CommitGolfCandidate.TwoPermutationCommitSetup

/-! NonceChain generator of the quad commit image (31727a8's loop, retargeted).
Words 157224..157423: x12 := x22, x7 := x22 + 0x10002000, then 1525248 forward permutation
calls (64 per latch), then x10 := x18, x12 := x9 and a jump back to word 18. -/
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

/-- Generator setup: x12 := x22, x7 := x22 + 0x10002000. -/
def genHeadOps : List Instr :=
  [.ADDI .x12 .x22 0,.LUI .x7 65538,.ADDI .x7 .x7 0,.ADD .x7 .x7 .x22]

/-- Tile end and return: `bgeu a2,t2,8; jal TILE; addi a0,s2,0; addi a2,s1,0; jal 18`. -/
def genTailOps : List Instr :=
  [.BGEU .x12 .x7 8,.JAL .x0 1779388,.ADDI .x10 .x18 0,.ADDI .x12 .x9 0,.JAL .x0 1150536]

/-- Words 0..18 of the NonceChain image (word 10 seeds the first pair block in place). -/
def nonceSetupOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,
   .LUI .x20 65537,.ADDI .x20 .x20 1768,.ADD .x20 .x9 .x20,
   .LUI .x22 442369,.ADDI .x22 .x22 0,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 0,.ADDI .x11 .x0 24,.ADDI .x11 .x11 0,
   .ECALL,
   .ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.JAL .x0 628828,.SLLI .x7 .x13 12]

def packetOp (k : Nat) : Instr :=
  if k=0 ∨ k=2 then .ECALL else if k=3 then .ADDI .x10 .x10 352 else .ADDI .x12 .x12 176

private theorem gen_head_decoded : ∀ j : Fin 4,
    (genHeadWords[j.val]?).bind decodeInstruction = some (.base ((genHeadOps[j.val]?).getD .EBREAK)) := by
  decide +kernel

private theorem gen_tail_decoded : ∀ j : Fin 5,
    (genTailWords[j.val]?).bind decodeInstruction = some (.base ((genTailOps[j.val]?).getD .EBREAK)) := by
  decide +kernel

private theorem pair_decoded : ∀ k : Fin 5,
    (pairWords[k.val]?).bind decodeInstruction = some (.base (packetOp k.val)) := by
  decide +kernel

private theorem nonce_setup_decoded : ∀ i : Fin 19,
    (setupWords[i.val]?).bind decodeInstruction = some (.base ((nonceSetupOps[i.val]?).getD .EBREAK)) := by
  decide +kernel

/-- The 11 root copy/HALT words preceding the generator inside `rootWords`. -/
def rootCoreWords : List (BitVec 32) :=
  [0x0204bf83, 0x01f43023, 0x0284bf83, 0x01f43423, 0x0304bf83, 0x01f43823, 0x0384bf83, 0x01f43c23, 0x00100293, 0x00000513, 0x00000073]

def genPrefix := parentPrefix++parentCode++parentLatchWords++rootCoreWords

theorem gen_prefix_length : genPrefix.length=157224 := by
  unfold genPrefix
  simp only [List.length_append]
  rw [parent_prefix_length,parent_code_length]
  rfl

theorem pair_code_length : pairCode.length=79440 := by
  simp only [pairCode,List.length_flatten,List.map_replicate,List.sum_replicate]
  rfl

attribute [local irreducible] image leafCode quadCode parentCode pairCode decodeInstruction

private theorem image_gen_split : image.code = genPrefix ++ genHeadWords ++ pairCode ++ genTailWords := by
  unfold image genPrefix parentPrefix quadPrefix rootWords rootCoreWords genWords
  simp only [List.append_assoc,List.append_nil]

theorem fetch_gen_head (j : Nat) (inside : j<4) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(157224+j))) :
    fetch image s=some (.base ((genHeadOps[j]?).getD .EBREAK)) := by
  apply fetch_code_index s (157224+j) (by omega) pc
  have atIndex := code_segment_at genPrefix genHeadWords (pairCode ++ genTailWords)
    (by rw [image_gen_split];simp only [List.append_assoc]) j (by simpa [genHeadWords] using inside)
  rw [gen_prefix_length] at atIndex
  rw [atIndex]
  exact gen_head_decoded ⟨j,inside⟩

theorem fetch_gen_pair (e k : Nat) (he : e<15888) (hk : k<5) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(157228+5*e+k))) :
    fetch image s=some (.base (packetOp k)) := by
  apply fetch_code_index s (157228+5*e+k) (by omega) pc
  have atIndex := code_segment_at (genPrefix ++ genHeadWords) pairCode genTailWords
    (by rw [image_gen_split]) (5*e+k) (by rw [pair_code_length];omega)
  rw [List.length_append,gen_prefix_length,show genHeadWords.length=4 from rfl,
    show 157224+4+(5*e+k)=157228+5*e+k by omega] at atIndex
  rw [atIndex]
  unfold pairCode
  have repeated := repeated_code_at pairWords 15888 e k he (by simpa [pairWords] using hk)
  change ((List.replicate 15888 pairWords).flatten)[5*e+k]?=pairWords[k]? at repeated
  rw [repeated]
  exact pair_decoded ⟨k,hk⟩

theorem fetch_gen_tail (j : Nat) (inside : j<5) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(236668+j))) :
    fetch image s=some (.base ((genTailOps[j]?).getD .EBREAK)) := by
  apply fetch_code_index s (236668+j) (by omega) pc
  have atIndex := code_segment_at (genPrefix ++ genHeadWords ++ pairCode) genTailWords []
    (by rw [image_gen_split];simp only [List.append_nil]) j (by simpa [genTailWords] using inside)
  rw [List.length_append,List.length_append,gen_prefix_length,pair_code_length,
    show genHeadWords.length=4 from rfl,show 157224+4+79440+j=236668+j by omega] at atIndex
  rw [atIndex]
  exact gen_tail_decoded ⟨j,inside⟩

theorem fetch_nonce_setup (i : Nat) (inside : i<19) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*i)) :
    fetch image s=some (.base ((nonceSetupOps[i]?).getD .EBREAK)) := by
  apply fetch_code_index s i (by omega) pc
  have word := code_segment_at [] setupWords
    (leafCode++leafLatchWords++quadSetupWords++quadCode++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords)
    (by unfold image;simp only [List.nil_append,List.append_assoc]) i inside
  simp only [List.length_nil,Nat.zero_add] at word
  rw [word]
  exact nonce_setup_decoded ⟨i,inside⟩

/-! ### The paired loop (after dadon's `20182e74`)

Each five-word packet makes two permutation calls: the first reads and writes `S`, the second
reads `S` and writes `S+176`; afterwards both cursors are at `S+352`. 15888 packets per tile,
48 tile visits, `bgeu; jal` at the tile end. -/

abbrev unroll : Nat := 15888
abbrev nonceChainBase : Nat := 6106914848
abbrev nonceChainCount : Nat := 1525248
def nonceChainDest (j : Nat) := nonceChainBase + 176*j
def nonceChainSource (j : Nat) := nonceChainBase + 352*(j/2)
def copyOf (j : Nat) := (j/2) % unroll
def nonceChainPC (j : Nat) := if j = nonceChainCount then 950776 else 633008 + 20*copyOf j + 8*(j%2)
def extra (j : Nat) := if j%2=1 ∧ copyOf j = unroll-1 then (if j+1 = nonceChainCount then 1 else 2) else 0
def nonceChainSteps (j : Nat) := 5*(j/2)+2*(j%2) + 2*((j/2)/unroll) - (if j = nonceChainCount then 1 else 0)
def nonceChainCycles (j : Nat) := 19*(j/2)+9*(j%2) + 2*((j/2)/unroll) - (if j = nonceChainCount then 1 else 0)

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

structure NonceChainFrame (s : MachineState) (j : Nat) : Prop where
  pc : s.pc = BitVec.ofNat 64 (nonceChainPC j)
  ready : ChainPermReady s
  input : s.getReg .x10 = BitVec.ofNat 64 (nonceChainSource j)
  output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest j)
  limit : s.getReg .x7 = BitVec.ofNat 64 (nonceChainDest nonceChainCount)

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
    (pc : s.pc = BitVec.ofNat 64 (4096+4*(157228+5*e+2*(j%2)+1))) (fuel : Nat) :
    execute image ((1+j%2)+fuel) s true =
      (do let r ← execute image fuel (nonceIncrements s j) true
          return r.charge (1+j%2) 0) := by
  by_cases even : j%2=0
  · have first := fetch_gen_pair e 1 he (by decide) s (by simpa only [even] using pc)
    rw [even]
    simpa only [nonceIncrements,if_pos even,packetOp,instructionCycles,
      show 1+fuel=fuel+1 by omega] using
      (execute_ordinary_step image (.base (.ADDI .x12 .x12 176)) s
        (execInstrBr s (.ADDI .x12 .x12 176)) fuel true first rfl)
  · have odd : j%2=1 := by omega
    let mid := execInstrBr s (.ADDI .x10 .x10 352)
    have first := fetch_gen_pair e 3 he (by decide) s (by simpa only [odd] using pc)
    have mp : mid.pc = BitVec.ofNat 64 (4096+4*(157228+5*e+4)) := by
      change s.pc+4=_
      rw [pc,odd,show 4096+4*(157228+5*e+4)=(4096+4*(157228+5*e+2*1+1))+4 by omega]
      simp only [BitVec.ofNat_add]
      rfl
    have second := fetch_gen_pair e 4 he (by decide) mid mp
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

/-- At a tile end, `bgeu a2,t2,8` falls through unless the last call has been made. -/
theorem latch_compare (s : MachineState) (j : Nat) (hj : j < nonceChainCount)
    (output : s.getReg .x12 = BitVec.ofNat 64 (nonceChainDest (j+1)))
    (limit : s.getReg .x7 = BitVec.ofNat 64 (nonceChainDest nonceChainCount)) :
    (s.getReg .x12).ult (s.getReg .x7) = decide (j+1<nonceChainCount) := by
  rw [output,limit]
  simp only [BitVec.ult, BitVec.toNat_ofNat,nonceChainDest]
  rw [Nat.mod_eq_of_lt (by dsimp [nonceChainBase,nonceChainCount] at *; omega),
    Nat.mod_eq_of_lt (by decide)]
  by_cases last : j+1 < nonceChainCount
  · simp only [last, decide_true]
    apply decide_eq_true
    dsimp [nonceChainBase,nonceChainCount] at last ⊢
    omega
  · simp only [last, decide_false]
    apply decide_eq_false
    dsimp [nonceChainBase,nonceChainCount] at last hj ⊢
    omega

end TwoPermutationPrototype.Quad.Commit.Chain
