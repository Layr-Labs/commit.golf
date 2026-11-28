import CommitGolfCandidate.TwoPermutationPackedOpeningWordCode
import CommitGolfCandidate.OpeningWordCopyFieldMemory

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.OpeningWordCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000
attribute [local irreducible] CommitGolf.Riscv.execute

/-- Preconditions used only at a word-aligned field. The public layout leaves
much more than one doubleword between the source heap/tape and proof buffer. -/
structure FastInputs (site : CopySite) (state : MachineState) (source target : Nat) : Prop where
  pc : state.pc=BitVec.ofNat 64 (4096+4*site.start)
  src : state.getReg .x7=BitVec.ofNat 64 source
  dst : state.getReg .x21=BitVec.ofNat 64 target
  sourceAligned : source%4=0
  targetAligned : target%4=0
  sourceGap : source+2*site.halfwords+8≤target
  targetFit : target+2*site.halfwords≤MEMORY_BYTES

def fastCopyState (site : CopySite) (fast : site.fast=true) (state : MachineState) : MachineState :=
  finishState site.halfwords (wordField (fastWordCode site fast) state)

private theorem FastInputs.ready {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FastInputs site state source target) (fast : site.fast=true) :
    WordReady (fastWordCode site fast) state source target 0 := by
  have gap := input.sourceGap
  have fit := input.targetFit
  have width := fast_width site
  have pairs : 4*(site.halfwords/2)≤2*site.halfwords := by omega
  refine ⟨?_,input.src,input.dst,?_,?_,input.sourceAligned,input.targetAligned⟩
  · simpa only [fastWordCode,Nat.mul_zero,Nat.add_zero] using input.pc
  · change source+4*(site.halfwords/2)≤MEMORY_BYTES
    omega
  · change target+4*(site.halfwords/2)≤MEMORY_BYTES
    omega

private theorem valid_halfword (address : Nat) (fit : address+2≤MEMORY_BYTES) (even : address%2=0) :
    accessValid (BitVec.ofNat 64 address) 2=true := by
  have limit : MEMORY_BYTES<2^64 := by decide
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : address<2^64),
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨fit,even⟩

theorem FastInputs.execute {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FastInputs site state source target) (fast : site.fast=true) (fuel : Nat) (coins : Bool) :
    CommitGolf.Riscv.execute openingImage (site.cycles+fuel) state coins = do
      let result ← CommitGolf.Riscv.execute openingImage fuel (fastCopyState site fast state) coins
      return result.charge site.cycles 0 := by
  let code := fastWordCode site fast
  let middle := wordField code state
  have width := fast_width site
  have prefixPC : middle.pc=BitVec.ofNat 64 (4096+4*(site.start+2*(site.halfwords/2))) := by
    change (wordRun 0 (site.halfwords/2) state).pc=_
    rw [word_run_pc,input.pc,←BitVec.ofNat_add]
    congr 1
    omega
  have middleSrc : middle.getReg .x7=BitVec.ofNat 64 source :=
    (word_run_register state 0 (site.halfwords/2) .x7 (by decide)).trans input.src
  have middleDst : middle.getReg .x21=BitVec.ofNat 64 target :=
    (word_run_register state 0 (site.halfwords/2) .x21 (by decide)).trans input.dst
  have readable : site.halfwords=15 → accessValid (middle.getReg .x7+28) 2=true := by
    intro length
    rw [middleSrc,show (28:Word)=BitVec.ofNat 64 28 by rfl,←BitVec.ofNat_add]
    have gap := input.sourceGap
    have fit := input.targetFit
    have aligned := input.sourceAligned
    rw [length] at gap fit
    exact valid_halfword _ (by omega) (by omega)
  have writable : site.halfwords=15 → accessValid (middle.getReg .x21+28) 2=true := by
    intro length
    rw [middleDst,show (28:Word)=BitVec.ofNat 64 28 by rfl,←BitVec.ofNat_add]
    have fit := input.targetFit
    have aligned := input.targetAligned
    rw [length] at fit
    exact valid_halfword _ (by omega) (by omega)
  have suffix := finish_execute openingImage site.start site.halfwords width
    (fast_suffix_fetch site fast) middle prefixPC readable writable fuel coins
  have wordTrace := word_run_execute code state source target 0 code.words (input.ready fast) (by omega)
    ((finishInstructions site.halfwords).length+fuel) coins
  simp only [code,fastWordCode] at wordTrace
  have cost : site.cycles=2*(site.halfwords/2)+(finishInstructions site.halfwords).length := by
    simp [CopySite.cycles,fast,finish_cost _ width]
  rw [cost,Nat.add_assoc,wordTrace]
  change (do let result ← CommitGolf.Riscv.execute openingImage ((finishInstructions site.halfwords).length+fuel) middle coins
             return result.charge (2*(site.halfwords/2)) 0) = _
  rw [suffix]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add]
  congr 1
  funext result
  congr 2
  omega

theorem fast_copy_register (site : CopySite) (fast : site.fast=true) (state : MachineState)
    (reg : Reg) (kept : reg≠.x31) :
    (fastCopyState site fast state).getReg reg=state.getReg reg :=
  (finish_register site.halfwords (fast_width site)
    (wordField (fastWordCode site fast) state) reg kept).trans
    (word_run_register state 0 (site.halfwords/2) reg kept)

theorem FastInputs.final_pc {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FastInputs site state source target) (fast : site.fast=true) :
    (fastCopyState site fast state).pc=BitVec.ofNat 64 (4096+4*(site.start+2*site.halfwords)) := by
  unfold fastCopyState wordField
  rw [finish_pc _ (fast_width site),word_run_pc,input.pc,←BitVec.ofNat_add,←BitVec.ofNat_add]
  congr 1
  change 4096+4*site.start+8*(site.halfwords/2)+4*(2*site.halfwords-2*(site.halfwords/2)) = _
  have pairs : 2*(site.halfwords/2)≤2*site.halfwords := by omega
  omega

theorem FastInputs.memory {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FastInputs site state source target) (fast : site.fast=true) :
    (fastCopyState site fast state).mem =
      (ProjectedHalfword.copyLoopMemory false site.halfwords state
        (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)).mem := by
  let middle := wordField (fastWordCode site fast) state
  have width := fast_width site
  have pairs : 4*(site.halfwords/2)≤2*site.halfwords := by omega
  have gap := input.sourceGap
  have fit := input.targetFit
  have limit : MEMORY_BYTES<2^64 := by decide
  have wordTrace : middle.mem=(halfMemory (2*(site.halfwords/2)) state
      (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)).mem := by
    have m := word_run_memory state source target 0 (site.halfwords/2) input.src input.dst
    simp only [Nat.mul_zero,Nat.add_zero] at m
    change middle.mem=(wordMemory (site.halfwords/2) state
      (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)).mem at m
    rw [m,wordMemory_as_halves _ _ _ _ input.sourceAligned input.targetAligned (by omega) (by omega)]
  have src : middle.getReg .x7=BitVec.ofNat 64 source :=
    (word_run_register state 0 (site.halfwords/2) .x7 (by decide)).trans input.src
  have dst : middle.getReg .x21=BitVec.ofNat 64 target :=
    (word_run_register state 0 (site.halfwords/2) .x21 (by decide)).trans input.dst
  change (finishState site.halfwords middle).mem=_
  rw [finish_memory _ width,←halfMemory_projected]
  rcases width with width | width | width
  · rw [width] at wordTrace ⊢
    exact wordTrace
  · rw [width] at wordTrace ⊢
    norm_num at wordTrace ⊢
    rw [src,dst]
    have tail := halfMemory_congr 1 middle
      (halfMemory 14 state (BitVec.ofNat 64 source) (BitVec.ofNat 64 target))
      (BitVec.ofNat 64 source+BitVec.ofNat 64 28) (BitVec.ofNat 64 target+BitVec.ofNat 64 28) wordTrace
    rw [show 15=14+1 by rfl,halfMemory_add]
    have first : (halfMemory 1 middle
        (BitVec.ofNat 64 source+BitVec.ofNat 64 28) (BitVec.ofNat 64 target+BitVec.ofNat 64 28)).mem =
        (middle.setHalfword (BitVec.ofNat 64 target+BitVec.ofNat 64 28)
          (middle.getHalfword (BitVec.ofNat 64 source+BitVec.ofNat 64 28))).mem := by rfl
    simpa only [Nat.reduceMul] using first.symm.trans tail
  · rw [width] at wordTrace ⊢
    exact wordTrace

end TwoPermutationPrototype.PackedOpening
