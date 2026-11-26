import CommitGolfCandidate.TruncUpperEntry
import CommitGolfCandidate.TruncCheckPad
import CommitGolfCandidate.TruncCapGuard
import CommitGolfCandidate.TruncMask
import CommitGolfCandidate.TruncModel
namespace CommitGolfCandidate.Trunc.Check
open CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
private theorem word_ofNat_toNat (w : Word) : w=BitVec.ofNat 64 w.toNat := by simp
set_option maxRecDepth 13000
set_option maxHeartbeats 350000


theorem restoredCap (state : MachineState) (pc : state.pc = loc 1058)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (4 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel
            (top_checkCapParentLatchState state) allowCoins
          return result.charge 4 0) := by
  let s1 := (state.setReg .x10 (state.getReg .x10 - 64)).setPC 5556
  let atJump:=(state.setReg .x10 (state.getReg .x10-64)).setPC (loc 1059)
  let s2 := (s1.setReg .x12 (state.getReg .x12 - 32)).setPC 5560
  have f0 : fetch (Trunc.wireImage true) state = some (.base (.ADDI .x10 .x10 4032)) := by
    apply fetchAt _ _ 1058 _ (by decide) pc;rfl
  have f1 : fetch (Trunc.wireImage true) s1 = some (.base (.ADDI .x12 .x12 4064)) := by
    apply sharedFetch _ 365 _ (by unfold untouched; decide) rfl; rfl
  have f2 : fetch (Trunc.wireImage true) s2 = some (.base (.BNE .x12 .x22 8180)) := by
    apply sharedFetch _ 366 _ (by unfold untouched; decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x10 .x10 4032)) = some atJump := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, atJump, pc,loc,
      BitVec.sub_eq_add_neg]
  have st1 : ordinaryStep s1 (.base (.ADDI .x12 .x12 4064)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have st2 : ordinaryStep s2 (.base (.BNE .x12 .x22 8180)) = some (top_checkCapParentLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s1, s2,
      top_checkCapParentLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  have j:=jumpAt (Trunc.wireImage true) atJump 1059 365 2094376 (by decide) rfl (by rfl) (by decide)
  rw [show 4+fuel=(1+(2+fuel))+1 by omega,execute_ordinary_step _ _ _ _ _ _ f0 st0,j]
  change (do let a ← (do let r ← execute (Trunc.wireImage true) (2+fuel) s1 allowCoins;return r.charge 1 0)
             return a.charge 1 0)=_
  rw [Nat.add_comm 2 fuel]
  simp only [execute,f1,st1,f2,st2,instructionCycles,bind_assoc,pure_bind]
  simp [Execution.charge,← Nat.add_assoc]

def upperReply (s : MachineState) (a : Digest) := if s.getReg .x12=544 then a else padLow a
def top_checkCapParentStepState (s : MachineState) (a : Digest) := PairCap.top_checkCapParentStepState s (upperReply s a)

theorem upperCleared (s : MachineState) (a : Digest) (bound : (s.getReg .x12).toNat+32≤2^64) (align : (s.getReg .x12).toNat%8=0) :
    let written:=paddedCompressionState s a
    (if written.getReg .x12=544 then written else CapGuard.cleared written)=paddedCompressionState s (upperReply s a) := by
  dsimp only
  have dst : (paddedCompressionState s a).getReg .x12=s.getReg .x12 := padded_compression_register s a .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [dst,upperReply]
  by_cases eqn : s.getReg .x12=544
  · rw [if_pos eqn,if_pos eqn]
  · rw [if_neg eqn,if_neg eqn,CapGuard.cleared,dst]
    unfold paddedCompressionState
    generalize s.getReg .x12=w at align bound ⊢
    conv_lhs => rw [word_ofNat_toNat w]
    rw [show (30 : Word)=BitVec.ofNat 64 30 by decide,← BitVec.ofNat_add]
    exact (clearedReply _ w.toNat a align bound).trans (by rw [←word_ofNat_toNat])

theorem runUpperLatch (s : MachineState) (pc : s.pc=5552) (valid : accessValid (s.getReg .x12+30) 2)
    (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (10+fuel) s coins=
     (do let r←execute (Trunc.wireImage true) fuel (top_checkCapParentLatchState (if s.getReg .x12=544 then s else CapGuard.cleared s)) coins
         return r.charge 10 0) := by
  rw [show 10+fuel=6+(4+fuel) by omega,CapGuard.runCap s pc valid _ coins,restoredCap _ rfl]
  have ignore (t : MachineState) : PairCap.top_checkCapParentLatchState (t.setPC (loc 1058))=PairCap.top_checkCapParentLatchState t := rfl
  simp only [ignore,bind_assoc,pure_bind];simp [Execution.charge,←Nat.add_assoc]


theorem top_cap_parent_step_registers (state : MachineState) (answer : BitVec 256) :
    (top_checkCapParentStepState state answer).getReg .x10 = state.getReg .x10 - 64 ∧
    (top_checkCapParentStepState state answer).getReg .x12 = state.getReg .x12 - 32 ∧
    ∀ reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31],
      (top_checkCapParentStepState state answer).getReg reg = state.getReg reg := PairCap.top_cap_parent_step_registers state (upperReply state answer) 

theorem top_cap_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (top_checkCapParentStepState state answer).pc =
      if state.getReg .x12 - 32 = state.getReg .x22 then 5564 else 5548 := PairCap.top_cap_parent_step_pc state (upperReply state answer) 

def top_checkCapParentLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
      top_checkCapParentLoop (top_checkCapParentStepState state answer) count

theorem top_check_cap_parent_loop (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (pc : 0 < count → state.pc = 5548)
    (r5 : state.getReg .x5 = 0) (r13 : state.getReg .x13 = 0)
    (r22 : state.getReg .x22 = 512)
    (r10 : state.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count))
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (27 * count + fuel) state allowCoins =
      (do let finished ← top_checkCapParentLoop state count
          let result ← execute (Trunc.wireImage true) fuel finished allowCoins
          return result.charge (34 * count) count) := by
  induction count generalizing state with
  | zero => simp [top_checkCapParentLoop, Execution.charge]
  | succ count ih =>
    have r10Nat : (state.getReg .x10).toNat = 512 + 64 * (count + 1) := by
      rw [r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have r12Nat : (state.getReg .x12).toNat = 512 + 32 * (count + 1) := by
      rw [r12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have srcValid : rangeValid (state.getReg .x10) 96 = true := by
      simp only [rangeValid, r10Nat, MEMORY_BYTES, decide_eq_true_eq]; omega
    have dstValid : rangeValid (state.getReg .x12) 32 = true := by
      simp only [rangeValid, r12Nat, MEMORY_BYTES, decide_eq_true_eq]; omega
    have call := rec_padding_call true state 363 (Or.inr rfl) (pc (by omega))
      r5 r13 srcValid dstValid (by rw [r10Nat]; omega) (by rw [r12Nat]; omega)
      (by rw [r10Nat, r12Nat]; omega) (10 + (27 * count + fuel)) allowCoins
    rw [show 27 * (count + 1) + fuel = 17 + (10 + (27 * count + fuel)) by omega]
    erw [call]
    simp only [top_checkCapParentLoop, bind_assoc, pure_bind]
    apply congrArg (fun k =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))) :
        OracleComp World (BitVec 256)) >>= k)
    funext answer
    change BitVec 256 at answer
    have afterPC : (paddedCompressionState state answer).pc = 5552 := by
      rw [padded_compression_pc, pc (by omega)]; rfl
    have next10 : (top_checkCapParentStepState state answer).getReg .x10 =
        BitVec.ofNat 64 (512 + 64 * count) := by
      rw [(top_cap_parent_step_registers state answer).1, r10]
      change BitVec.ofNat 64 (512 + 64 * (count + 1)) - BitVec.ofNat 64 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next12 : (top_checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(top_cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have nextPC : 0 < count → (top_checkCapParentStepState state answer).pc = 5548 := by
      intro pos
      rw [top_cap_parent_step_pc, ← (top_cap_parent_step_registers state answer).2.1, next12, r22, if_neg]
      intro eq
      have n := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 512 + 32 * count < 2^64)] at n
      change 512 + 32 * count = 512 at n
      omega
    have dstSame : (paddedCompressionState state answer).getReg .x12=state.getReg .x12 :=
      padded_compression_register state answer .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have valid2 : accessValid ((paddedCompressionState state answer).getReg .x12+30) 2 := by
      rw [dstSame,r12]
      exact (show ∀ t : Fin 127,accessValid (BitVec.ofNat 64 (512+32*(t.val+1))+30) 2 by decide) ⟨count,by omega⟩
    have stepDef : top_checkCapParentLatchState (paddedCompressionState state (upperReply state answer))=top_checkCapParentStepState state answer := rfl
    rw [runUpperLatch _ afterPC valid2,upperCleared state answer (by omega) (by rw [r12Nat];omega),stepDef,
      ih (by omega) (top_checkCapParentStepState state answer) nextPC
        (((top_cap_parent_step_registers state answer).2.2 .x5 (by decide)).trans r5)
        (((top_cap_parent_step_registers state answer).2.2 .x13 (by decide)).trans r13)
        (((top_cap_parent_step_registers state answer).2.2 .x22 (by decide)).trans r22)
        next10 next12]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro finished
    apply bind_congr
    intro res
    congr 1
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    constructor <;> omega

theorem upperSupport (s t : MachineState) (n : Nat) (h : t∈support (top_checkCapParentLoop s n)) :
    t∈support (PairCap.top_checkCapParentLoop s n) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    rw [top_checkCapParentLoop,mem_support_bind_iff] at h
    obtain ⟨a,_,tail⟩:=h
    rw [PairCap.top_checkCapParentLoop,mem_support_bind_iff]
    exact ⟨upperReply s a,by simp <;> exact Set.mem_univ _,ih _ tail⟩

theorem top_cap_parent_loop_finished (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (r22 : state.getReg .x22 = 512)
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (finished : MachineState) (reached : finished ∈ support (top_checkCapParentLoop state count)) :
    (0 < count → finished.pc = 5564) ∧
    ∀ reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := PairCap.top_cap_parent_loop_finished count bounded state r22 r12 finished (upperSupport state finished count reached)

theorem top_cap_parent_loop_support_outside (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (finished : MachineState) (reached : finished ∈ support (top_checkCapParentLoop state count))
    (address : Word)
    (outside : address.toNat < 544 ∨ 512 + 32 * (count + 1) ≤ address.toNat) :
    finished.getMem address = state.getMem address := PairCap.top_cap_parent_loop_support_outside count bounded state r12 finished (upperSupport state finished count reached) address outside

theorem top_check_cap_root_setup (state : MachineState) (pc : state.pc = 5564)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (2 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel
            (top_checkCapRootSetupState state) allowCoins
          return result.charge 2 0) := by
  let s1 := (state.setReg .x21 (state.getReg .x22 + 32)).setPC 5568
  have f0 : fetch (Trunc.wireImage true) state = some (.base (.ADDI .x21 .x22 32)) := by
    apply sharedFetch _ 367 _ (by unfold untouched; decide) pc; rfl
  have f1 : fetch (Trunc.wireImage true) s1 = some (.base (.ADDI .x23 .x26 0)) := by
    apply sharedFetch _ 368 _ (by unfold untouched; decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x21 .x22 32)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x23 .x26 0)) = some (top_checkCapRootSetupState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1,
      top_checkCapRootSetupState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, st0, f1, st1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem top_cap_parent_loop_heap (oracle : Oracle) (state : MachineState)
    (cap : Nat → Digest) (count : Nat) (bounded : count ≤ 127)
    (r10 : state.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count))
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (above : ∀ slot, count < slot → slot < 256 →
      readBuffer state (512 + 32 * slot) 32 = Trunc.referenceHeap oracle.compression 128 cap slot) :
    ∀ slot, 0 < slot → slot < 256 →
      readBuffer (checkEvaluation oracle (top_checkCapParentLoop state count)).1 (512 + 32 * slot) 32 =
        Trunc.referenceHeap oracle.compression 128 cap slot := by
  induction count generalizing state with
  | zero =>
    intro slot pos hi
    rw [top_checkCapParentLoop, check_evaluation_pure]
    exact above slot pos hi
  | succ count ih =>
    have r10Nat : (state.getReg .x10).toNat = 512 + 64 * (count + 1) := by
      rw [r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h64 : readBuffer state (state.getReg .x10).toNat 64 =
        Trunc.referenceHeap oracle.compression 128 cap (2 * (count + 1) + 1) ++
          Trunc.referenceHeap oracle.compression 128 cap (2 * (count + 1)) := by
      rw [r10Nat, read_compression_halves state _ (by omega)]
      have leftAddr : 512 + 64 * (count + 1) = 512 + 32 * (2 * (count + 1)) := by omega
      have rightAddr : 512 + 64 * (count + 1) + 32 = 512 + 32 * (2 * (count + 1) + 1) := by omega
      rw [rightAddr, leftAddr,
        above (2 * (count + 1) + 1) (by omega) (by omega),
        above (2 * (count + 1)) (by omega) (by omega)]
    let answer : BitVec 256 := oracle.compression (padInput (readBuffer state (state.getReg .x10).toNat 64))
    have maskEq : upperReply state answer=storeNode (count+1) answer := by
      unfold upperReply storeNode
      by_cases e : count=0
      · subst count;rw [r12,if_pos (by decide),if_neg (by decide)]
      · have ne : state.getReg .x12≠544 := by rw [r12];intro eqn;have num:=congrArg BitVec.toNat eqn;rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 512+32*(count+1)<2^64)] at num;change _=544 at num;omega
        rw [if_neg ne,if_pos (by unfold masked;omega)]
    have answerEq : upperReply state answer=Trunc.referenceHeap oracle.compression 128 cap (count+1) := by
      rw [maskEq,Trunc.reference_heap_parent _ _ _ _ (by omega) (by omega)]
      unfold answer parent combine
      rw [h64]
    let next := top_checkCapParentStepState state answer
    have next10 : next.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count) := by
      rw [(top_cap_parent_step_registers state answer).1, r10]
      change BitVec.ofNat 64 (512 + 64 * (count + 1)) - BitVec.ofNat 64 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next12 : next.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(top_cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have nextMem : next.mem = (writeBits state (BitVec.ofNat 64 (512 + 32 * (count + 1))) (upperReply state answer)).mem := by
      dsimp only [next]
      rw [top_checkCapParentStepState,PairCap.top_cap_parent_step_mem, padded_compression_memory state (upperReply state answer), r12]
    have nextAbove (slot : Nat) (lo : count < slot) (hi : slot < 256) :
        readBuffer next (512 + 32 * slot) 32 = Trunc.referenceHeap oracle.compression 128 cap slot := by
      rw [read_buffer_memory_congr _ _ nextMem]
      by_cases eq : slot = count + 1
      · subst slot
        have w := write_bits_digest (bits := 256) state (512 + 32 * (count + 1)) 0 (upperReply state answer) (by decide) (by decide)
        rw [← answerEq]
        exact w.trans (by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          rw [BitVec.getLsbD_extractLsb']
          simp [hi])
      · have preserved := write_bits_read_outside (bits := 256) state (upperReply state answer) (512 + 32 * (count + 1))
          (512 + 32 * slot) 32 (by omega) (by omega) (Or.inr (by omega))
        exact preserved.trans (above slot (by omega) hi)
    intro slot pos hi
    rw [top_checkCapParentLoop, check_evaluation_public_bind]
    exact ih next (by omega) next10 next12 nextAbove slot pos hi

end CommitGolfCandidate.Trunc.Check
