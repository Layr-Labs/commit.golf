import CommitGolfCandidate.GroupOpenUpperRun
import CommitGolfCandidate.GroupOpenMask

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open PackedOpening (ByteCopy)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem pc_set (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem mem_set_reg (state : MachineState) (r : Reg) (v : Word) :
    (state.setReg r v).mem = state.mem := by cases r <;> rfl
@[local simp] private theorem mem_set_pc (state : MachineState) (v : Word) : (state.setPC v).mem = state.mem := rfl

def slotCode : List Instr :=
  [.ADDI .x21 .x21 16, .SLLI .x7 .x6 8, .ANDI .x7 .x7 3072, .ADD .x7 .x7 .x24, .ANDI .x10 .x6 3,
   .ADDI .x7 .x7 584]

def quartetHeadCode (j : Fin 3) : List Instr :=
  [.XORI .x28 .x10 (BitVec.ofNat 12 (j.val+1)), .SLLI .x28 .x28 5,
   .ADD .x28 .x28 .x7]

def quartetExitCode : List Instr := [.ADDI .x21 .x21 96, .SRLI .x6 .x6 2, .ADD .x6 .x6 .x19]

def straightPrefix (code : List Instr) (state : MachineState) (n : Nat) : MachineState :=
  (code.take n).foldl execInstrBr state

def slotStart (state : MachineState) := straightPrefix slotCode state 6
def quartetHead (j : Fin 3) (state : MachineState) := straightPrefix (quartetHeadCode j) state 3
def quartetExit (state : MachineState) := straightPrefix quartetExitCode state 3

theorem run_slot (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*34)) :
    RunsOpeningBlock state (slotStart state) 6 := by
  intro fuel coins
  apply execute_unit_steps (states := straightPrefix slotCode state)
  intro i inside
  refine ⟨.base (slotCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (34+i) _ (by omega)
    · interval_cases i <;> simp [straightPrefix, slotCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem run_quartet_head (j : Fin 3) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(40+35*j.val))) :
    RunsOpeningBlock state (quartetHead j state) 3 := by
  intro fuel coins
  apply execute_unit_steps (states := straightPrefix (quartetHeadCode j) state)
  intro i inside
  refine ⟨.base ((quartetHeadCode j)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ ((40+35*j.val)+i) _ (by omega)
    · fin_cases j <;> interval_cases i <;> simp [straightPrefix, quartetHeadCode, execInstrBr, pc]
    · fin_cases j <;> interval_cases i <;> rfl
  · fin_cases j <;> interval_cases i <;> rfl
  · fin_cases j <;> interval_cases i <;> rfl

theorem run_quartet_exit (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*145)) :
    RunsOpeningBlock state (quartetExit state) 3 := by
  intro fuel coins
  apply execute_unit_steps (states := straightPrefix quartetExitCode state)
  intro i inside
  refine ⟨.base (quartetExitCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ (145+i) _ (by omega)
    · interval_cases i <;> simp [straightPrefix, quartetExitCode, execInstrBr, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem slot_post (s : MachineState) :
    let u := slotStart s
    u.pc=s.pc+24 ∧ u.mem=s.mem ∧ u.getReg .x21=s.getReg .x21+16 ∧
    u.getReg .x7 = (((s.getReg .x6 <<< 8) &&& (3072#12).signExtend 64) + s.getReg .x24) + 584 ∧
    u.getReg .x10 = s.getReg .x6 &&& 3 ∧
    ∀ r, r ≠ .x21 → r ≠ .x7 → r ≠ .x10 → u.getReg r = s.getReg r := by
  simp [slotStart,straightPrefix,slotCode,execInstrBr,signExtend12,BitVec.add_assoc]
  intro r a b c
  simp [Ne.symm a,Ne.symm b,Ne.symm c]

theorem quartet_head_post (j : Fin 3) (s : MachineState) :
    let u := quartetHead j s
    u.pc=s.pc+12 ∧ u.mem=s.mem ∧
    u.getReg .x28 = ((s.getReg .x10 ^^^ BitVec.ofNat 64 (j.val+1)) <<< 5) + s.getReg .x7 ∧
    ∀ r, r ≠ .x28 → u.getReg r = s.getReg r := by
  fin_cases j <;>
    simp [quartetHead,straightPrefix,quartetHeadCode,execInstrBr,signExtend12,BitVec.add_assoc] <;>
    intro r a <;> simp [Ne.symm a]

theorem quartet_exit_post (s : MachineState) :
    let u := quartetExit s
    u.pc=s.pc+12 ∧ u.mem=s.mem ∧ u.getReg .x21=s.getReg .x21+96 ∧
    u.getReg .x6=(s.getReg .x6 >>> 2)+s.getReg .x19 ∧
    ∀ r, r ≠ .x21 → r ≠ .x6 → u.getReg r = s.getReg r := by
  simp [quartetExit,straightPrefix,quartetExitCode,execInstrBr,signExtend12,BitVec.add_assoc]
  intro r a b
  simp [Ne.symm a, Ne.symm b]

theorem quarter_shift (i : Index) : (BitVec.ofNat 64 i.val >>> 2) = BitVec.ofNat 64 (i.val/4) := by
  apply BitVec.eq_of_toNat_eq
  have bound : i.val < 16777216 := i.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : i.val <2^64), Nat.mod_eq_of_lt (by omega : i.val/4 <2^64)]

theorem masked_group (i : Index) :
    ((BitVec.ofNat 64 i.val <<< 8) &&& (3072#12).signExtend 64) = BitVec.ofNat 64 (1024*(i.val/4)) := by
  rw [quartet_slot_mask, quarter_shift, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 (i.val/4) * BitVec.ofNat 64 1024 = _
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

theorem low_selector (i : Index) : (BitVec.ofNat 64 i.val &&& 3) = BitVec.ofNat 64 (i.val%4) := by
  change BitVec.ofNat 64 i.val &&& BitVec.ofNat 64 (2^2-1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

theorem xor_group (i j : Nat) (small : j<4) :
    (i ^^^ j)/4 = i/4 ∧ (i ^^^ j)%4 = i%4 ^^^ j := by
  constructor
  · change (i ^^^ j)/2^2 = i/2^2
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    have zero : j >>> 2 = 0 := by rw [Nat.shiftRight_eq_div_pow]; omega
    simp [zero]
  · change (i ^^^ j)%2^2 = i%2^2 ^^^ j
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt small]

theorem quartet_physical_source (s : MachineState) (i : Index) (j : Fin 3)
    (group : s.getReg .x7 = BitVec.ofNat 64 (groupSlots+1024*(i.val/4)+584))
    (selector : s.getReg .x10 = BitVec.ofNat 64 (i.val%4)) :
    (quartetHead j s).getReg .x28 = BitVec.ofNat 64 (leafAddress (i.val ^^^ (j.val+1))) := by
  rw [(quartet_head_post j s).2.2.1, selector, group, ← BitVec.ofNat_xor, BitVec.shiftLeft_eq_mul_twoPow]
  change (BitVec.ofNat 64 (i.val%4 ^^^ (j.val+1)) * BitVec.ofNat 64 32 +
      BitVec.ofNat 64 (groupSlots+1024*(i.val/4)+584)) = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  obtain ⟨g,p⟩ := xor_group i.val (j.val+1) (by omega)
  unfold leafAddress
  rw [g,p]
  congr 1
  omega

theorem sibling_in_message (i : Index) (j : Fin 3) : i.val ^^^ (j.val+1) < LENGTH :=
  Nat.xor_lt_two_pow i.isLt (by have := j.isLt; change j.val+1 < 2^24; omega)

end TwoPermutationPrototype.GroupedOpening
