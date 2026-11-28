import CommitGolfCandidate.OpeningWordCopyMemory
import CommitGolfCandidate.Execution

namespace CommitGolfCandidate.OpeningWordCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 1100000
attribute [local irreducible] execute

structure WordCode where
  image : Image
  start : Nat
  words : Nat
  offsetBound : 4*words ≤ 64
  load : ∀ j, j<words → ∀ state : MachineState,
    state.pc=BitVec.ofNat 64 (4096+4*(start+2*j)) →
      fetch image state=some (.base (.LWU .x31 .x7 (BitVec.ofNat 12 (4*j))))
  store : ∀ j, j<words → ∀ state : MachineState,
    state.pc=BitVec.ofNat 64 (4096+4*(start+2*j+1)) →
      fetch image state=some (.base (.SW .x21 .x31 (BitVec.ofNat 12 (4*j))))

structure WordReady (code : WordCode) (state : MachineState) (source target j : Nat) : Prop where
  pc : state.pc=BitVec.ofNat 64 (4096+4*(code.start+2*j))
  src : state.getReg .x7=BitVec.ofNat 64 source
  dst : state.getReg .x21=BitVec.ofNat 64 target
  srcBound : source+4*code.words ≤ MEMORY_BYTES
  dstBound : target+4*code.words ≤ MEMORY_BYTES
  srcAligned : source%4=0
  dstAligned : target%4=0

def wordLoad (state : MachineState) (j : Nat) :=
  (state.setReg .x31 ((state.getWord32 (state.getReg .x7+BitVec.ofNat 64 (4*j))).zeroExtend 64)).setPC (state.pc+4)

def wordStep (state : MachineState) (j : Nat) :=
  let loaded := wordLoad state j
  (loaded.setWord32 (state.getReg .x21+BitVec.ofNat 64 (4*j))
    ((loaded.getReg .x31).truncate 32)).setPC (loaded.pc+4)

def wordRun : Nat → Nat → MachineState → MachineState
  | _, 0, state => state
  | j, n+1, state => wordRun (j+1) n (wordStep state j)

def wordField (code : WordCode) (state : MachineState) := wordRun 0 code.words state

private theorem small_sign (n : Nat) (bounded : n<64) :
    signExtend12 (BitVec.ofNat 12 n)=BitVec.ofNat 64 n := by
  interval_cases n <;> rfl

theorem word_step_register (state : MachineState) (j : Nat) (r : Reg) (kept : r≠.x31) :
    (wordStep state j).getReg r=state.getReg r := by
  have store (s : MachineState) (a : Word) (v : BitVec 32) : (s.setWord32 a v).getReg r=s.getReg r :=
    by cases r <;> rfl
  simp only [wordStep, MachineState.getReg_setPC, store, wordLoad,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept)]

private theorem valid_word (address : Nat) (bounded : address+4≤MEMORY_BYTES) (aligned : address%4=0) :
    accessValid (BitVec.ofNat 64 address) 4=true := by
  have limit : MEMORY_BYTES<2^64 := by decide
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : address<2^64),
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨bounded,aligned⟩

private theorem word_step_execute (code : WordCode) (state : MachineState) (source target j : Nat)
    (ready : WordReady code state source target j) (bounded : j<code.words) (fuel : Nat) (coins : Bool) :
    execute code.image (2+fuel) state coins = do
      let result ← execute code.image fuel (wordStep state j) coins
      return result.charge 2 0 := by
  have size := code.offsetBound
  have sw := ready.srcBound
  have tw := ready.dstBound
  have sal := ready.srcAligned
  have tal := ready.dstAligned
  have sa : state.getReg .x7+BitVec.ofNat 64 (4*j)=BitVec.ofNat 64 (source+4*j) := by
    rw [ready.src,←BitVec.ofNat_add]
  have da : state.getReg .x21+BitVec.ofNat 64 (4*j)=BitVec.ofNat 64 (target+4*j) := by
    rw [ready.dst,←BitVec.ofNat_add]
  have validSrc := valid_word (source+4*j) (by omega) (by omega)
  have validDst := valid_word (target+4*j) (by omega) (by omega)
  have sign := small_sign (4*j) (by omega)
  let loaded := wordLoad state j
  have stepL : ordinaryStep state (.base (.LWU .x31 .x7 (BitVec.ofNat 12 (4*j))))=some loaded := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,sign,sa,validSrc,↓reduceIte,
      execInstrBr,loaded,wordLoad]
  have lpc : loaded.pc=BitVec.ofNat 64 (4096+4*(code.start+2*j+1)) := by
    change state.pc+4=_
    rw [ready.pc,show (4:Word)=BitVec.ofNat 64 4 by rfl,←BitVec.ofNat_add]
    congr 1
  have stepS : ordinaryStep loaded (.base (.SW .x21 .x31 (BitVec.ofNat 12 (4*j))))=
      some (wordStep state j) := by
    have destL : loaded.getReg .x21=state.getReg .x21 := by
      simp only [loaded, wordLoad, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31≠.x21)]
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,sign,destL,da,validDst,↓reduceIte,execInstrBr]
    simp only [da,wordStep,loaded]
  have first := execute_ordinary_step code.image _ state loaded (fuel+1) coins (code.load _ bounded _ ready.pc) stepL
  have second := execute_ordinary_step code.image _ loaded (wordStep state j) fuel coins (code.store _ bounded _ lpc) stepS
  rw [show 2+fuel=(fuel+1)+1 by omega,first,second]
  simp only [instructionCycles,bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]

private theorem word_step_ready (code : WordCode) (state : MachineState) (source target j : Nat)
    (ready : WordReady code state source target j) :
    WordReady code (wordStep state j) source target (j+1) := by
  refine ⟨?_,(word_step_register _ _ _ (by decide)).trans ready.src,
    (word_step_register _ _ _ (by decide)).trans ready.dst,ready.srcBound,
    ready.dstBound,ready.srcAligned,ready.dstAligned⟩
  change state.pc+4+4=_
  rw [ready.pc,BitVec.add_assoc,show (4:Word)+4=BitVec.ofNat 64 8 by rfl,←BitVec.ofNat_add]
  congr 1

private theorem word_step_memory (state : MachineState) (source target j : Nat)
    (src : state.getReg .x7=BitVec.ofNat 64 source)
    (dst : state.getReg .x21=BitVec.ofNat 64 target) :
    (wordStep state j).mem =
      (state.setWord32 (BitVec.ofNat 64 (target+4*j)) (state.getWord32 (BitVec.ofNat 64 (source+4*j)))).mem := by
  have da : state.getReg .x21+BitVec.ofNat 64 (4*j)=BitVec.ofNat 64 (target+4*j) := by
    rw [dst,←BitVec.ofNat_add]
  have sa : state.getReg .x7+BitVec.ofNat 64 (4*j)=BitVec.ofNat 64 (source+4*j) := by
    rw [src,←BitVec.ofNat_add]
  have value : ((wordLoad state j).getReg .x31).truncate 32 = state.getWord32 (BitVec.ofNat 64 (source+4*j)) := by
    simp only [wordLoad,sa,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide : Reg.x31≠.x0)]
    generalize state.getWord32 (BitVec.ofNat 64 (source+4*j))=x
    simp [BitVec.truncate, BitVec.zeroExtend]
  change ((wordLoad state j).setWord32 _ _).mem=_
  rw [da,value]
  rfl

theorem word_run_execute (code : WordCode) (state : MachineState) (source target j n : Nat)
    (ready : WordReady code state source target j) (bounded : j+n≤code.words) (fuel : Nat) (coins : Bool) :
    execute code.image (2*n+fuel) state coins = do
      let result ← execute code.image fuel (wordRun j n state) coins
      return result.charge (2*n) 0 := by
  induction n generalizing state j with
  | zero => simp [wordRun,Execution.charge]
  | succ n ih =>
    rw [show 2*(n+1)+fuel=2+(2*n+fuel) by omega,word_step_execute code state source target j ready (by omega),
      ih _ _ (word_step_ready _ _ _ _ _ ready) (by omega)]
    simp only [wordRun,bind_assoc,pure_bind,Execution.charge,Nat.zero_add]
    congr 1
    funext result
    congr 2
    omega

theorem word_run_register (state : MachineState) (j n : Nat) (reg : Reg) (kept : reg≠.x31) :
    (wordRun j n state).getReg reg=state.getReg reg := by
  induction n generalizing j state with
  | zero => rfl
  | succ n ih => exact (ih (wordStep state j) (j+1)).trans (word_step_register state j reg kept)

theorem word_run_pc (state : MachineState) (j n : Nat) :
    (wordRun j n state).pc=state.pc+BitVec.ofNat 64 (8*n) := by
  induction n generalizing j state with
  | zero => simp [wordRun]
  | succ n ih =>
    rw [wordRun, ih]
    change state.pc+4+4+BitVec.ofNat 64 (8*n)=_
    have plus8 : state.pc+4+4=state.pc+BitVec.ofNat 64 8 := by
      rw [BitVec.add_assoc]
      rfl
    rw [plus8, BitVec.add_assoc, ←BitVec.ofNat_add]
    congr 2
    omega

theorem wordMemory_congr (n : Nat) (left right : MachineState) (source target : Word)
    (same : left.mem=right.mem) :
    (wordMemory n left source target).mem=(wordMemory n right source target).mem := by
  induction n generalizing left right source target with
  | zero => exact same
  | succ n ih =>
    apply ih
    simp only [MachineState.setWord32,MachineState.setMem,MachineState.getWord32,MachineState.getMem,same]

theorem word_run_memory (state : MachineState) (source target j n : Nat)
    (src : state.getReg .x7=BitVec.ofNat 64 source)
    (dst : state.getReg .x21=BitVec.ofNat 64 target) :
    (wordRun j n state).mem=
      (wordMemory n state (BitVec.ofNat 64 (source+4*j)) (BitVec.ofNat 64 (target+4*j))).mem := by
  induction n generalizing state j with
  | zero => rfl
  | succ n ih =>
    rw [wordRun, ih _ _ ((word_step_register _ _ _ (by decide)).trans src)
      ((word_step_register _ _ _ (by decide)).trans dst), wordMemory]
    have adv (base : Nat) : BitVec.ofNat 64 (base+4*j)+4=BitVec.ofNat 64 (base+4*(j+1)) := by
      rw [show (4:Word)=BitVec.ofNat 64 4 by rfl,←BitVec.ofNat_add]
      congr 1
    rw [adv,adv]
    exact wordMemory_congr _ _ _ _ _ (word_step_memory _ _ _ _ src dst)

end CommitGolfCandidate.OpeningWordCopy
