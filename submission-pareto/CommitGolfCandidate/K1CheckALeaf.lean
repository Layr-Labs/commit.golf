import CommitGolfCandidate.K1CheckDispatch
import CommitGolfCandidate.K1CheckACopy
import CommitGolfCandidate.QuartetCheckBlock

/-! # The K1 A-leaf routine (check words 500–566)

On a rank-0 position the dispatcher branches to word 500. With `v` the opened value at word `src+5`
and the scratch `S = 9216` (word 1152):

* 500–504: `x28 = 4056 + 256 i`, `x10 = v + 56`, `x11 = 200`, `x13 = 1`;
* 505–520: the 16 salt bytes of the record to `[12272, 12288)` (as words 28–43);
* 521–523: `x12 = S`; first call `π (v[56..256))`, reply at `[S, S+200)`;
* 524–559: `v[0..128)` to `[S+200, S+328)`, the salt to `[S+328, S+344)`;
* 560–564: the tag `4040 + 256 i` at `S+160`; second call on `[S+144, S+344)`, reply at 12288.

The window of the second call is `reply[144..160) ‖ tag ‖ reply[168..200) ‖ v[0..128) ‖ salt`, the A
branch of `pinnedSecondInput`. Words 565–566 are the record's words 58–59 (`x21 += 16`, jump to 367),
so the quartet block runs from the state with its PC moved to word 58 (`execute_a_enter`). -/
namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem a_mem_set_reg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl
@[local simp] private theorem a_mem_set_pc (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl
@[local simp] private theorem a_pc_set_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc = pc := rfl
private theorem a_mem_set_mem (s : MachineState) (a v : Word) :
    (s.setMem a v).mem = fun a' => if a' == a then v else s.mem a' := rfl

/-! ### Words 500–504 -/

def aSetupCode : List Instr :=
  [.SLLI .x28 .x6 8, .ADD .x28 .x3 .x28, .ADDI .x10 .x19 96, .ADDI .x11 .x0 200, .ADDI .x13 .x0 1]

def aSetupPrefix (e : MachineState) (n : Nat) : MachineState := (aSetupCode.take n).foldl execInstrBr e

def aSetup (e : MachineState) : MachineState := aSetupPrefix e 5

theorem execute_a_setup (e : MachineState) (pc : e.pc = BitVec.ofNat 64 (4096+4*500)) :
    GroupHop e (aSetup e) 5 := by
  intro fuel
  apply execute_unit_steps (states := aSetupPrefix e)
  intro i bounded
  refine ⟨.base (aSetupCode[i]?.getD .EBREAK), fetch_at _ (500+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> (simp [aSetupPrefix, aSetupCode, execInstrBr, pc]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem a_setup_post (e : MachineState) :
    let t := aSetup e
    t.pc = e.pc + 20 ∧ t.mem = e.mem ∧ t.getReg .x28 = e.getReg .x3 + (e.getReg .x6 <<< 8) ∧
      t.getReg .x10 = e.getReg .x19 + 96 ∧ t.getReg .x11 = 200 ∧ t.getReg .x13 = 1 ∧
      ∀ r, r ≠ .x28 → r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → t.getReg r = e.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr, BitVec.add_assoc] <;> rfl
  · simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr]
  · simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr] <;> rfl
  · simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr, signExtend12] <;> rfl
  · simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr, signExtend12] <;> rfl
  · simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr, signExtend12] <;> rfl
  · intro r a b c d
    simp [aSetup, aSetupPrefix, aSetupCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

/-! ### Words 505–520: the salt, as words 28–43 -/

def aNonceCode : CopyCode :=
  ⟨packedImage, 505, 8, .x21, .x4, 0, by decide, by decide, by decide,
   fun j bounded s pc => by
     apply fetch_at s (505+2*j) _ (by omega) pc
     interval_cases j <;> rfl,
   fun j bounded s pc => by
     apply fetch_at s (505+2*j+1) _ (by omega) pc
     interval_cases j <;> rfl⟩

def aStaged (e : MachineState) : MachineState := copyField aNonceCode (aSetup e)

/-- `field_bytes` for any copy code. -/
theorem code_bytes (c : CopyCode) (s : MachineState) (source target : Nat)
    (ready : CopyReady c s source target 0) (order : target ≤ source) :
    let t := copyField c s
    (∀ i<2*c.count, t.getByte (BitVec.ofNat 64 (target+i))=s.getByte (BitVec.ofNat 64 (source+i))) ∧
    (∀ q : Word, (∀ i<2*c.count, q≠BitVec.ofNat 64 (target+i)) → t.getByte q=s.getByte q) := by
  have sb : source+2*c.count≤MEMORY_BYTES := ready.srcBound
  have tb : target+2*c.count≤MEMORY_BYTES := ready.dstBound
  have lim : MEMORY_BYTES<2^64 := by decide
  have mem := copy_field_memory _ _ _ _ ready
  have bytes := ProjectedHalfword.forward_memory c.count s source target order (by omega) (by omega)
        ready.srcAligned ready.dstAligned
  simpa only [MachineState.getByte, MachineState.getMem,mem] using bytes

/-! ### Words 521–522: the scratch pointer -/

def aScratchCode : List Instr := [.LUI .x12 2, .ADDI .x12 .x12 1024]

def aScratchPrefix (t : MachineState) (n : Nat) : MachineState := (aScratchCode.take n).foldl execInstrBr t

/-- The state at the first call (word 523). -/
def aCallOne (e : MachineState) : MachineState := aScratchPrefix (aStaged e) 2

theorem execute_a_scratch (t : MachineState) (pc : t.pc = BitVec.ofNat 64 (4096+4*521)) :
    GroupHop t (aScratchPrefix t 2) 2 := by
  intro fuel
  apply execute_unit_steps (states := aScratchPrefix t)
  intro i bounded
  refine ⟨.base (aScratchCode[i]?.getD .EBREAK), fetch_at _ (521+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> (simp [aScratchPrefix, aScratchCode, execInstrBr, pc]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem a_scratch_post (t : MachineState) :
    let u := aScratchPrefix t 2
    u.pc = t.pc + 8 ∧ u.mem = t.mem ∧ u.getReg .x12 = wordAddress 1152 ∧
      ∀ r, r ≠ .x12 → u.getReg r = t.getReg r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [aScratchPrefix, aScratchCode, execInstrBr, BitVec.add_assoc] <;> rfl
  · simp [aScratchPrefix, aScratchCode, execInstrBr]
  · simp [aScratchPrefix, aScratchCode, execInstrBr, signExtend12, wordAddress] <;> decide
  · intro r a
    simp [aScratchPrefix, aScratchCode, execInstrBr, Ne.symm a]

/-! ### The first reply and the two copies (words 524–559) -/

def aFirstReply (e : MachineState) (a : Block) : MachineState := writeBits (aCallOne e) (wordAddress 1152) a

def aMsgCopy : DCopy where
  start := 524
  count := 16
  source := .x10
  dest := .x12
  srcImm k := BitVec.ofNat 12 (4040+8*k)
  dstImm k := BitVec.ofNat 12 (200+8*k)
  sourceTemp := by decide
  destTemp := by decide
  load j bounded s pc := by
    apply fetch_at s (524+2*j) _ (by omega) pc
    interval_cases j <;> rfl
  store j bounded s pc := by
    apply fetch_at s (524+2*j+1) _ (by omega) pc
    interval_cases j <;> rfl

def aSaltCopy : DCopy where
  start := 556
  count := 2
  source := .x4
  dest := .x12
  srcImm k := BitVec.ofNat 12 (8*k)
  dstImm k := BitVec.ofNat 12 (328+8*k)
  sourceTemp := by decide
  destTemp := by decide
  load j bounded s pc := by
    apply fetch_at s (556+2*j) _ (by omega) pc
    interval_cases j <;> rfl
  store j bounded s pc := by
    apply fetch_at s (556+2*j+1) _ (by omega) pc
    interval_cases j <;> rfl

def aCopied (e : MachineState) (a : Block) : MachineState := dcopy aSaltCopy (dcopy aMsgCopy (aFirstReply e a))

/-! ### Words 560–563: the tag and the second-call registers -/

def aTailCode : List Instr := [.ADDI .x31 .x28 4080, .SD .x12 .x31 160, .ADDI .x10 .x12 144, .ADDI .x12 .x23 0]

def aTailPrefix (t : MachineState) (n : Nat) : MachineState := (aTailCode.take n).foldl execInstrBr t

/-- The state at the second call (word 564). -/
def aCallTwo (e : MachineState) (a : Block) : MachineState := aTailPrefix (aCopied e a) 4

def aSecondReply (e : MachineState) (a b : Block) : MachineState := writeBits (aCallTwo e a) (wordAddress 1536) b

theorem execute_a_tail (t : MachineState) (pc : t.pc = BitVec.ofNat 64 (4096+4*560))
    (store : accessValid (t.getReg .x12 + signExtend12 160) 8 = true) :
    GroupHop t (aTailPrefix t 4) 4 := by
  intro fuel
  apply execute_unit_steps (states := aTailPrefix t)
  intro i bounded
  refine ⟨.base (aTailCode[i]?.getD .EBREAK), fetch_at _ (560+i) _ (by omega) ?_ ?_, ?_, ?_⟩
  · interval_cases i <;> (simp [aTailPrefix, aTailCode, execInstrBr, pc]) <;> (try rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, aTailPrefix, aTailCode,
      execInstrBr] <;> simpa using store
  · interval_cases i <;> rfl

theorem a_tail_post (t : MachineState) :
    let u := aTailPrefix t 4
    u.pc = t.pc + 16 ∧ u.getReg .x10 = t.getReg .x12 + 144 ∧ u.getReg .x12 = t.getReg .x23 ∧
      u.mem = (t.setMem (t.getReg .x12 + signExtend12 160) (t.getReg .x28 + signExtend12 4080)).mem ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x31 → u.getReg r = t.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [aTailPrefix, aTailCode, execInstrBr, BitVec.add_assoc] <;> rfl
  · simp [aTailPrefix, aTailCode, execInstrBr, signExtend12] <;> rfl
  · simp [aTailPrefix, aTailCode, execInstrBr, signExtend12]
  · simp [aTailPrefix, aTailCode, execInstrBr, a_mem_set_mem]
  · intro r a b c
    simp [aTailPrefix, aTailCode, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

/-! ### Words 565–566: the record's words 58–59 at another PC -/

def aEnterCode : List Instr := [.ADDI .x21 .x21 16, .JAL .x0 0x1ffce4]

theorem a_enter_eq (w : MachineState) (pc : w.pc = BitVec.ofNat 64 (4096+4*565)) :
    (aEnterCode.take 2).foldl execInstrBr w = straight qEnterCode (w.setPC 0x10e8) 2 := by
  have target : w.pc + 4 + signExtend21 0x1ffce4 = (0x10e8 : Word) + 4 + signExtend21 1232 := by
    rw [pc]; decide
  change execInstrBr (execInstrBr w (.ADDI .x21 .x21 16)) (.JAL .x0 0x1ffce4) =
    execInstrBr (execInstrBr (w.setPC 0x10e8) (.ADDI .x21 .x21 16)) (.JAL .x0 1232)
  change ((w.setReg .x21 (w.getReg .x21 + signExtend12 16)).setPC (w.pc + 4 + signExtend21 0x1ffce4)) =
    ((w.setReg .x21 (w.getReg .x21 + signExtend12 16)).setPC ((0x10e8 : Word) + 4 + signExtend21 1232))
  rw [target]

theorem execute_a_enter (w : MachineState) (pc : w.pc = BitVec.ofNat 64 (4096+4*565)) (fuel : Nat) :
    execute packedImage (2+fuel) w false = execute packedImage (2+fuel) (w.setPC 0x10e8) false := by
  have here : (w.setPC 0x10e8).pc = 0x10e8 := rfl
  rw [execute_q_enter (w.setPC 0x10e8) here fuel]
  have run := execute_unit_steps packedImage 2 fuel (fun i => (aEnterCode.take i).foldl execInstrBr w) false (by
    intro i bounded
    refine ⟨.base (aEnterCode[i]?.getD .EBREAK), fetch_at _ (565+i) _ (by omega) ?_ ?_, ?_, ?_⟩
    · interval_cases i <;> (simp [aEnterCode, execInstrBr, pc]) <;> (try rfl)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl)
  simp only [List.take_zero, List.foldl_nil] at run
  rw [run, a_enter_eq w pc]

end TwoPermutationPrototype.Packed.RecordLeaf
