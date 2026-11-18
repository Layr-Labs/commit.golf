import CommitGolfCandidate.K3CUUnits
import CommitGolfCandidate.TwoPermutationPackedParentMask
import CommitGolfCandidate.TwoPermutationPackedParentControl

/-!
# One level-21 parent

A level-21 parent compresses the 64 bytes `[s_u, s_u + 64)` of unit `u` (its two group nodes)
into heap node `2^21 + u` (all 32 bytes kept), then moves `x10` one unit down and `x12` one node
down: `ecall; addi x10,x10,-8*unitStride; addi x12,x12,-32`.

Positions count the parents still to run: at position `p` the next parent is unit `p - 1`, so the
loop starts at position `2^21` and stops at position `0` (`x10` one unit below unit 0, the value
kept in `x7`).
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open CommitGolfCandidate (writeBits_register)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

/-- Word held by `x10` at position `p`: the base of unit `p - 1`. -/
def l21Source (p : Nat) : Nat := unitFirst - unitStride + unitStride*p
/-- Heap node written at position `p` (by the parent of unit `p - 1`). -/
def l21Node (p : Nat) : Nat := 2097151+p
/-- The `x10` step `-8*unitStride` as a 12-bit immediate. -/
def l21Imm : BitVec 12 := BitVec.ofNat 12 (4096-8*unitStride)
/-- Address of parent slot `slot` of a level-21 pass starting at `base` (3 words per parent). -/
def l21PC (base : Word) (slot : Nat) : Word := base+BitVec.ofNat 64 (12*slot)

theorem l21_source_unit (U : Nat) : l21Source (U+1) = unitBase U := by
  unfold l21Source unitBase unitFirst cellFirst unitStride; omega

structure L21WordsAt (image : Image) (pc : Word) : Prop where
  call : ∀ s : MachineState, s.pc=pc → fetch image s=some (.base .ECALL)
  source : ∀ s : MachineState, s.pc=pc+4 → fetch image s=some (.base (.ADDI .x10 .x10 l21Imm))
  target : ∀ s : MachineState, s.pc=pc+8 → fetch image s=some (.base (.ADDI .x12 .x12 4064))

structure L21Regs (s : MachineState) (p : Nat) : Prop where
  source : s.getReg .x10 = wordAddress (l21Source p)
  target : s.getReg .x12 = wordAddress (treeWord (l21Node p))
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  heap : s.getReg .x9 = wordAddress (treeWord 0)
  stop : s.getReg .x7 = wordAddress (l21Source 0)

def l21Input (s : MachineState) (p : Nat) : BitVec 512 := readBuffer s (8*l21Source p) 64

def l21After (s : MachineState) (p : Nat) (answer : BitVec 256) :=
  execInstrBr (execInstrBr (parentWritten s (l21Node p) answer) (.ADDI .x10 .x10 l21Imm)) (.ADDI .x12 .x12 4064)

theorem l21_after_pc (s : MachineState) (p : Nat) (answer : BitVec 256) :
    (l21After s p answer).pc=s.pc+12 := by
  change (parentWritten s (l21Node p) answer).pc+4+4=s.pc+12
  rw [parentWritten,written_pc,BitVec.add_assoc,BitVec.add_assoc]
  rfl

theorem l21_pc_succ (base : Word) (slot : Nat) : l21PC base slot+12=l21PC base (slot+1) := by
  change base+BitVec.ofNat 64 (12*slot)+BitVec.ofNat 64 12 = base+BitVec.ofNat 64 (12*(slot+1))
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 12*slot+12=12*(slot+1) by omega]

/-- Memory after a level-21 parent: the full reply at its heap node. -/
theorem l21_after_memory (s : MachineState) (p : Nat) (answer : BitVec 256) :
    (l21After s p answer).mem=(parentWritten s (l21Node p) answer).mem := rfl

attribute [local irreducible] parentWritten

theorem l21_keeps_register (s : MachineState) (p : Nat) (answer : BitVec 256) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg) :
    (l21After s p answer).getReg reg=s.getReg reg := by
  simp only [l21After,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ keptSource,MachineState.getReg_setReg_ne _ _ _ _ keptTarget]
  rw [parentWritten,writeBits_register]

theorem l21_next_regs (s : MachineState) (p : Nat) (answer : BitVec 256)
    (regs : L21Regs s (p+1)) : L21Regs (l21After s (p+1) answer) p := by
  have holds (reg : Reg) : (parentWritten s (l21Node (p+1)) answer).getReg reg=s.getReg reg := by
    rw [parentWritten,writeBits_register]
  constructor
  · change (parentWritten s (l21Node (p+1)) answer).getReg .x10 + signExtend12 l21Imm = _
    rw [holds,regs.source]
    have advance : l21Source (p+1)=l21Source p+unitStride := by unfold l21Source unitStride; omega
    rw [advance,wordAddress_add,BitVec.add_assoc,
      show wordAddress unitStride+signExtend12 l21Imm=0 by decide]
    exact BitVec.add_zero _
  · change (parentWritten s (l21Node (p+1)) answer).getReg .x12 + signExtend12 4064 = _
    rw [holds,regs.target]
    have advance : treeWord (l21Node (p+1))=treeWord (l21Node p)+4 := by unfold treeWord l21Node;omega
    rw [advance,wordAddress_add,BitVec.add_assoc,
      show wordAddress 4+signExtend12 4064=0 by decide]
    exact BitVec.add_zero _
  · exact (l21_keeps_register s _ answer .x5 (by decide) (by decide)).trans regs.selector
  · exact (l21_keeps_register s _ answer .x11 (by decide) (by decide)).trans regs.size
  · exact (l21_keeps_register s _ answer .x13 (by decide) (by decide)).trans regs.primitive
  · exact (l21_keeps_register s _ answer .x9 (by decide) (by decide)).trans regs.heap
  · exact (l21_keeps_register s _ answer .x7 (by decide) (by decide)).trans regs.stop

private theorem l21_call_at (image : Image) (s : MachineState) (p fuel : Nat)
    (bound : p ≤ 2097152) (regs : L21Regs s p)
    (fetched : fetch image s=some (.base .ECALL)) :
    execute image (fuel+1) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (l21Input s p)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (parentWritten s (l21Node p) answer) true
          return result.charge 8 1) := by
  have source := word_address_value (word := l21Source p) (by unfold l21Source unitFirst cellFirst unitStride; omega)
  have target := word_address_value (word := treeWord (l21Node p)) (by unfold treeWord l21Node; omega)
  have inputRange : 8*l21Source p+64 ≤ MEMORY_BYTES := by
    unfold l21Source unitFirst cellFirst unitStride MEMORY_BYTES; omega
  have outputRange : 8*treeWord (l21Node p)+32 ≤ MEMORY_BYTES := by
    unfold treeWord l21Node MEMORY_BYTES; omega
  have query : oracleInput s=some (.inl (l21Input s p)) := by
    have kind : (s.getReg .x13).toNat=0 := by rw [regs.primitive]; rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [regs.source,regs.target,regs.size,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      rangeValid,source,target,inputRange,outputRange,l21Input]
  simp [execute,fetched,regs.selector,query,writeOracleAnswer,regs.target,parentWritten,
    oracleCycles,COMPRESSION_CYCLES]
  rfl

theorem l21_parent_step (image : Image) (s : MachineState) (p fuel : Nat) (pc : Word)
    (here : s.pc=pc) (bound : p ≤ 2097152) (regs : L21Regs s p)
    (fetched : L21WordsAt image pc) :
    execute image (3+fuel) s true =
      (do let answer ← (liftM (World.query (.inr (.inl (l21Input s p)))) : OracleComp World (BitVec 256))
          let result ← execute image fuel (l21After s p answer) true
          return result.charge 10 1) := by
  rw [show 3+fuel=(fuel+2)+1 by omega,l21_call_at image s p _ bound regs (fetched.call s here)]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let first := parentWritten s (l21Node p) answer
  let moved := execInstrBr first (.ADDI .x10 .x10 l21Imm)
  have firstPC : first.pc=pc+4 := by simp only [first,parentWritten,written_pc,here]
  have movedPC : moved.pc=pc+8 := by
    change first.pc+4=_
    rw [firstPC,BitVec.add_assoc]
    rfl
  rw [CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.source first firstPC)
      (show ordinaryStep first _=some moved from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetched.target moved movedPC)
      (show ordinaryStep moved _=some (l21After s p answer) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

end TwoPermutationPrototype.Grouped
