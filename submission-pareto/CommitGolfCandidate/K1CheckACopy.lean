import CommitGolfCandidate.TwoPermutationPackedRecordLeafCalls

/-! # Straight-line doubleword copies of the K1 A routine

Words 524–555 copy `v[0..128)` (`ld x31,(8k-56)(x10); sd x31,(200+8k)(x12)`, k < 16) and words
556–559 copy the salt (`ld x31,8k(x4); sd x31,(328+8k)(x12)`, k < 2). `DCopy` describes such a run of
`LD x31`/`SD` pairs in the K1 check image; `dcopyRun` is its exact effect: the `count` destination
words receive the source words, `x31` is clobbered, nothing else changes. -/
namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

structure DCopy where
  start : Nat
  count : Nat
  source : Reg
  dest : Reg
  srcImm : Nat → BitVec 12
  dstImm : Nat → BitVec 12
  sourceTemp : source ≠ .x31
  destTemp : dest ≠ .x31
  load : ∀ j, j < count → ∀ s : MachineState, s.pc = BitVec.ofNat 64 (4096+4*(start+2*j)) →
    fetch packedImage s = some (.base (.LD .x31 source (srcImm j)))
  store : ∀ j, j < count → ∀ s : MachineState, s.pc = BitVec.ofNat 64 (4096+4*(start+2*j+1)) →
    fetch packedImage s = some (.base (.SD dest .x31 (dstImm j)))

/-- Ready for pair `j`: the PC is at the pair's load, every pair's addresses are the aligned
words `src+k` and `dst+k`, and the source and destination ranges are disjoint. -/
structure DReady (c : DCopy) (s : MachineState) (src dst j : Nat) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*(c.start+2*j))
  srcAddr : ∀ k < c.count, s.getReg c.source + signExtend12 (c.srcImm k) = wordAddress (src+k)
  dstAddr : ∀ k < c.count, s.getReg c.dest + signExtend12 (c.dstImm k) = wordAddress (dst+k)
  srcBound : src + c.count ≤ 2^33
  dstBound : dst + c.count ≤ 2^33
  apart : src + c.count ≤ dst ∨ dst + c.count ≤ src

/-- One pair: the load and the store, as the machine executes them. -/
def dstep (c : DCopy) (s : MachineState) (j : Nat) : MachineState :=
  execInstrBr (execInstrBr s (.LD .x31 c.source (c.srcImm j))) (.SD c.dest .x31 (c.dstImm j))

def dcopyRun (c : DCopy) : Nat → Nat → MachineState → MachineState
  | _, 0, s => s
  | j, n+1, s => dcopyRun c (j+1) n (dstep c s j)

/-- All `count` pairs from pair 0. -/
def dcopy (c : DCopy) (s : MachineState) : MachineState := dcopyRun c 0 c.count s

private theorem dstep_load_reg (c : DCopy) (s : MachineState) (j : Nat) (r : Reg) (kept : r ≠ .x31) :
    (execInstrBr s (.LD .x31 c.source (c.srcImm j))).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept)]

private theorem dstep_reg (c : DCopy) (s : MachineState) (j : Nat) (r : Reg) (kept : r ≠ .x31) :
    (dstep c s j).getReg r = s.getReg r := by
  have st (u : MachineState) (a v : Word) : (u.setMem a v).getReg r = u.getReg r := by cases r <;> rfl
  have load := dstep_load_reg c s j r kept
  simp only [dstep, execInstrBr] at load ⊢
  simp only [MachineState.getReg_setPC, st]
  exact load

private theorem dstep_pc (c : DCopy) (s : MachineState) (j : Nat) :
    (dstep c s j).pc = s.pc + 4 + 4 := rfl

private theorem dstep_ready (c : DCopy) (s : MachineState) (src dst j : Nat) (ready : DReady c s src dst j) :
    DReady c (dstep c s j) src dst (j+1) := by
  refine ⟨?_, ?_, ?_, ready.srcBound, ready.dstBound, ready.apart⟩
  · rw [dstep_pc, ready.pc, BitVec.add_assoc, show (4:Word)+4 = BitVec.ofNat 64 8 by rfl, ← BitVec.ofNat_add]
    congr 1
  · intro k hk
    rw [dstep_reg _ _ _ _ c.sourceTemp]
    exact ready.srcAddr k hk
  · intro k hk
    rw [dstep_reg _ _ _ _ c.destTemp]
    exact ready.dstAddr k hk

private theorem dstep_execute (c : DCopy) (s : MachineState) (src dst j : Nat)
    (ready : DReady c s src dst j) (bounded : j < c.count) (fuel : Nat) (coins : Bool) :
    execute packedImage (2+fuel) s coins = do
      let result ← execute packedImage fuel (dstep c s j) coins
      return result.charge 2 0 := by
  have sb := ready.srcBound
  have db := ready.dstBound
  have validSrc := aligned_access (src+j) (by omega)
  have validDst := aligned_access (dst+j) (by omega)
  have sa := ready.srcAddr j bounded
  have da := ready.dstAddr j bounded
  let l := execInstrBr s (.LD .x31 c.source (c.srcImm j))
  have stepL : ordinaryStep s (.base (.LD .x31 c.source (c.srcImm j))) = some l := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, sa, validSrc, ↓reduceIte, l]
  have lpc : l.pc = BitVec.ofNat 64 (4096+4*(c.start+2*j+1)) := by
    change s.pc+4 = _
    rw [ready.pc, show (4:Word) = BitVec.ofNat 64 4 by rfl, ← BitVec.ofNat_add]
    congr 1
  have stepS : ordinaryStep l (.base (.SD c.dest .x31 (c.dstImm j))) = some (dstep c s j) := by
    have destL : l.getReg c.dest = s.getReg c.dest := dstep_load_reg c s j c.dest c.destTemp
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, destL, da, validDst, ↓reduceIte]
    rfl
  have first := execute_ordinary_step packedImage _ s l (fuel+1) coins (c.load _ bounded _ ready.pc) stepL
  have second := execute_ordinary_step packedImage _ l (dstep c s j) fuel coins (c.store _ bounded _ lpc) stepS
  rw [show 2+fuel = (fuel+1)+1 by omega, first, second]
  simp only [instructionCycles, bind_assoc, pure_bind, Execution.charge, Nat.zero_add, ← Nat.add_assoc]

private theorem drun_execute (c : DCopy) (s : MachineState) (src dst j n : Nat)
    (ready : DReady c s src dst j) (bounded : j+n ≤ c.count) (fuel : Nat) (coins : Bool) :
    execute packedImage (2*n+fuel) s coins = do
      let result ← execute packedImage fuel (dcopyRun c j n s) coins
      return result.charge (2*n) 0 := by
  induction n generalizing s j with
  | zero => simp [dcopyRun, Execution.charge]
  | succ n ih =>
    rw [show 2*(n+1)+fuel = 2+(2*n+fuel) by omega, dstep_execute c s src dst j ready (by omega),
      ih _ _ (dstep_ready _ _ _ _ _ ready) (by omega)]
    simp only [dcopyRun, bind_assoc, pure_bind, Execution.charge, Nat.zero_add]
    congr 1
    funext result
    congr 2
    omega

private theorem dstep_view (c : DCopy) (s : MachineState) (src dst j : Nat)
    (ready : DReady c s src dst j) (bounded : j < c.count) (i : Nat) (small : i < 2^61) :
    memoryView (dstep c s j) i = writeWord (memoryView s) (dst+j) (memoryView s (src+j)) i := by
  have db := ready.dstBound
  have destL : (execInstrBr s (.LD .x31 c.source (c.srcImm j))).getReg c.dest = s.getReg c.dest :=
    dstep_load_reg c s j c.dest c.destTemp
  have value : (execInstrBr s (.LD .x31 c.source (c.srcImm j))).getReg .x31 = memoryView s (src+j) := by
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
      ready.srcAddr j bounded]
    rfl
  have address := ready.dstAddr j bounded
  have unfolded : memoryView (dstep c s j) i =
      memoryView ((execInstrBr s (.LD .x31 c.source (c.srcImm j))).setMem (wordAddress (dst+j))
        ((execInstrBr s (.LD .x31 c.source (c.srcImm j))).getReg .x31)) i := by
    change ((execInstrBr s (.LD .x31 c.source (c.srcImm j))).setMem
      ((execInstrBr s (.LD .x31 c.source (c.srcImm j))).getReg c.dest + signExtend12 (c.dstImm j))
      ((execInstrBr s (.LD .x31 c.source (c.srcImm j))).getReg .x31)).getMem (wordAddress i) = _
    rw [destL, address]
    rfl
  rw [unfolded, memory_at_store (by omega) small, value]
  rfl

private theorem drun_view (c : DCopy) (s : MachineState) (src dst j n : Nat)
    (ready : DReady c s src dst j) (fits : j+n ≤ c.count) (w : Nat) (bounded : w < 2^33) :
    memoryView (dcopyRun c j n s) w =
      if dst + j ≤ w ∧ w < dst + j + n then memoryView s (src + (w - dst)) else memoryView s w := by
  induction n generalizing s j with
  | zero =>
    have no : ¬ (dst + j ≤ w ∧ w < dst + j + 0) := by omega
    simp only [dcopyRun, no, ite_false]
  | succ n ih =>
    have sb := ready.srcBound
    have db := ready.dstBound
    have apart := ready.apart
    have next := ih (dstep c s j) (j+1) (dstep_ready _ _ _ _ _ ready) (by omega)
    simp only [dcopyRun]
    rw [next]
    by_cases inside : dst + (j+1) ≤ w ∧ w < dst + (j+1) + n
    · have source : src + (w - dst) < 2^61 := by omega
      have yes : dst + j ≤ w ∧ w < dst + j + (n+1) := by omega
      have other : src + (w - dst) ≠ dst + j := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true inside), ite_eq_left_of_eq_true _ _ (eq_true yes), dstep_view c s src dst j ready (by omega) _ source]
      simp only [writeWord, other, ite_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false inside), dstep_view c s src dst j ready (by omega) _ (by omega)]
      by_cases here : w = dst + j
      · have yes : dst + j ≤ w ∧ w < dst + j + (n+1) := by omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true yes)]
        simp only [writeWord, here, ite_true]
        congr 1
        omega
      · have no : ¬ (dst + j ≤ w ∧ w < dst + j + (n+1)) := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false no)]
        simp only [writeWord, here, ite_false]

theorem dcopy_execute (c : DCopy) (s : MachineState) (src dst : Nat) (ready : DReady c s src dst 0)
    (fuel : Nat) (coins : Bool) :
    execute packedImage (2*c.count+fuel) s coins = do
      let result ← execute packedImage fuel (dcopy c s) coins
      return result.charge (2*c.count) 0 := by
  have run := drun_execute c s src dst 0 c.count ready (by omega) fuel coins
  simpa only [dcopy] using run

theorem dcopy_pc (c : DCopy) (s : MachineState) (src dst : Nat) (ready : DReady c s src dst 0) :
    (dcopy c s).pc = BitVec.ofNat 64 (4096+4*(c.start+2*c.count)) := by
  have aux (j n : Nat) (st : MachineState) (r : DReady c st src dst j) :
      (dcopyRun c j n st).pc = BitVec.ofNat 64 (4096+4*(c.start+2*(j+n))) := by
    induction n generalizing j st with
    | zero => simpa only [dcopyRun, Nat.add_zero] using r.pc
    | succ n ih =>
      simpa only [dcopyRun, show j+1+n = j+(n+1) by omega] using ih _ _ (dstep_ready _ _ _ _ _ r)
  simpa only [dcopy, Nat.zero_add] using aux 0 c.count s ready

theorem dcopy_register (c : DCopy) (s : MachineState) (r : Reg) (kept : r ≠ .x31) :
    (dcopy c s).getReg r = s.getReg r := by
  have aux (j n : Nat) (st : MachineState) : (dcopyRun c j n st).getReg r = st.getReg r := by
    induction n generalizing j st with
    | zero => rfl
    | succ n ih => exact (ih (j+1) (dstep c st j)).trans (dstep_reg c st j r kept)
  exact aux _ _ _

theorem dcopy_view (c : DCopy) (s : MachineState) (src dst : Nat) (ready : DReady c s src dst 0)
    (w : Nat) (bounded : w < 2^33) :
    memoryView (dcopy c s) w =
      if dst ≤ w ∧ w < dst + c.count then memoryView s (src + (w - dst)) else memoryView s w := by
  have run := drun_view c s src dst 0 c.count ready (by omega) w (by omega)
  simpa only [dcopy, Nat.add_zero] using run

end TwoPermutationPrototype.Packed.RecordLeaf
