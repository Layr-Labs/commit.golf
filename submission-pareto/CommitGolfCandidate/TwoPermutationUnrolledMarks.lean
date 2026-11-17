import CommitGolfCandidate.TwoPermutationOpeningCapEntry
import CommitGolfCandidate.TwoPermutationOpeningMarkContents

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private def offset (node : Nat) : BitVec 12 := BitVec.ofNat 12 (8 * node + 2049)

private def instruction (node : Nat) : Nat → Instr
  | 0 => .LD .x28 .x6 (offset (2*node))
  | 1 => .LD .x29 .x6 (offset (2*node+1))
  | 2 => .OR .x28 .x28 .x29
  | _ => .SD .x6 .x28 (offset node)

private def index (node : Nat) := 87 + 4*(255-node)
private def pcOf (i : Nat) : Word := BitVec.ofNat 64 (4096+4*i)
private def addr (n : Nat) : Word := BitVec.ofNat 64 (markBase+8*n)

private theorem offset_ok : ∀ n : Fin 512,
    6143#64 + signExtend12 (offset n.val) = addr n.val := by decide

private theorem mark_valid (n : Nat) (h : n < 512) : accessValid (addr n) 8 = true := by
  apply aligned_access
  · unfold markBase; omega
  · unfold markBase MEMORY_BYTES; omega

deriving instance DecidableEq for Instruction

private theorem decoded : ∀ n : Fin 255, ∀ i : Fin 4,
    (openingImage.code[index (n.val+1)+i.val]?).bind decodeInstruction =
      some (.base (instruction (n.val+1) i.val)) := by decide

private theorem addPC (i j : Nat) : pcOf i + BitVec.ofNat 64 (4*j) = pcOf (i+j) := by
  unfold pcOf
  rw [← BitVec.ofNat_add]
  congr 1
  omega

private def blockPrefix (s : MachineState) (node : Nat) : Nat → MachineState
  | 0 => s
  | i+1 => execInstrBr (blockPrefix s node i) (instruction node i)

def markPass (s : MachineState) : Nat → MachineState
  | 0 => s
  | n+1 => markPass (blockPrefix s (n+1) 4) n

private theorem prefix_pc (s : MachineState) (n : Nat) (i : Fin 5)
    (h : s.pc = pcOf (index n)) :
    (blockPrefix s n i.val).pc = pcOf (index n + i.val) := by
  fin_cases i <;> simp [blockPrefix, instruction, execInstrBr, h, MachineState.setPC,
    ← addPC, BitVec.add_assoc]

private theorem run_parent (s : MachineState) (n fuel : Nat) (coins : Bool)
    (within : n < 255) (pc : s.pc = pcOf (index (n+1)))
    (base : s.getReg .x6 = 6143#64) :
    execute openingImage (4+fuel) s coins =
      (do let r ← execute openingImage fuel (blockPrefix s (n+1) 4) coins
          return r.charge 4 0) := by
  apply execute_unit_steps (states := blockPrefix s (n+1))
  intro i hi
  refine ⟨.base (instruction (n+1) i), ?_, ?_, ?_⟩
  · apply opening_fetch _ (index (n+1)+i)
    · unfold index
      omega
    · exact prefix_pc s _ ⟨i, by omega⟩ pc
    · exact decoded ⟨n,within⟩ ⟨i,hi⟩
  · have left := offset_ok ⟨2*(n+1), by omega⟩
    have right := offset_ok ⟨2*(n+1)+1, by omega⟩
    have parent := offset_ok ⟨n+1, by omega⟩
    have lv := mark_valid (2*(n+1)) (by omega)
    have rv := mark_valid (2*(n+1)+1) (by omega)
    have pv := mark_valid (n+1) (by omega)
    interval_cases i <;>
      simp [blockPrefix, instruction, ordinaryStep, memoryArgumentsValid, memAccess,
        execInstrBr, base, left, right, parent, lv, rv, pv]
  · interval_cases i <;> rfl

@[local simp] private theorem mem_setPC' (s : MachineState) (v : Word) :
    (s.setPC v).mem = s.mem := rfl
@[local simp] private theorem mem_setReg' (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

private theorem parent_mem (s : MachineState) (n : Nat) (within : n < 256)
    (base : s.getReg .x6 = 6143#64) :
    (blockPrefix s n 4).mem =
      (s.setMem (addr n) (s.getMem (addr (2*n)) ||| s.getMem (addr (2*n+1)))).mem := by
  have a := offset_ok ⟨2*n,by omega⟩
  have b := offset_ok ⟨2*n+1,by omega⟩
  have c := offset_ok ⟨n,within.trans (by decide)⟩
  simp [blockPrefix, instruction, execInstrBr, base, a, b, c, MachineState.setMem]

private theorem parent_register (s : MachineState) (n : Nat) (r : Reg)
    (left : r ≠ .x28) (right : r ≠ .x29) : (blockPrefix s n 4).getReg r = s.getReg r := by
  simp [blockPrefix, instruction, execInstrBr, Ne.symm left, Ne.symm right]

theorem pass_register (s : MachineState) (n : Nat) (r : Reg)
    (left : r ≠ .x28) (right : r ≠ .x29) : (markPass s n).getReg r = s.getReg r := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih (blockPrefix s (n+1) 4)).trans (parent_register _ _ _ left right)

private theorem next_pc (n : Nat) (h : n < 255) : index (n+1) + 4 = index n := by
  unfold index
  omega

theorem run_pass (s : MachineState) (n fuel : Nat) (coins : Bool) (bound : n < 256)
    (pc : s.pc = pcOf (index n)) (base : s.getReg .x6 = 6143#64) :
    execute openingImage (4*n+fuel) s coins =
      (do let r ← execute openingImage fuel (markPass s n) coins
          return r.charge (4*n) 0) := by
  induction n generalizing s with
  | zero => simp [markPass, Execution.charge]
  | succ n ih =>
    have within : n < 255 := by omega
    have pc' := prefix_pc s (n+1) ⟨4,by decide⟩ pc
    rw [next_pc n within] at pc'
    have base' := (parent_register s (n+1) .x6 (by decide) (by decide)).trans base
    rw [show 4*(n+1)+fuel = 4+(4*n+fuel) by omega, run_parent s n _ coins within pc base,
      ih _ (by omega) pc' base']
    simp [markPass, Execution.charge, Nat.mul_succ, Nat.add_assoc, Nat.add_comm 4]

theorem pass_end (s : MachineState) (n : Nat) (bound : n < 256) (pc : s.pc = pcOf (index n)) :
    (markPass s n).pc = pcOf (index 0) := by
  induction n generalizing s with
  | zero => exact pc
  | succ n ih =>
    apply ih _ (by omega)
    exact (prefix_pc s (n+1) ⟨4,by decide⟩ pc).trans (congrArg pcOf (next_pc _ (by omega)))

theorem pass_frame (s : MachineState) (n address : Nat) (bound : n < 256)
    (above : trapdoorBase ≤ address) (fit : address < 2^64) (base : s.getReg .x6 = 6143#64) :
    (markPass s n).getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have different : BitVec.ofNat 64 address ≠ addr (n+1) := by
      intro eq
      have before := marks_before_trapdoor
      have size : markBase + 8*(n+1) < 2^64 := by unfold markBase; omega
      have := nat_address_injective fit size eq
      omega
    apply (ih (blockPrefix s (n+1) 4) (by omega)
      ((parent_register s _ .x6 (by decide) (by decide)).trans base)).trans
    apply (congrFun (parent_mem s _ bound base) (BitVec.ofNat 64 address)).trans
    exact MachineState.getMem_setMem_ne different

theorem pass_marks (s : MachineState) (groups : List Nat) (n : Nat) (bound : n < 256)
    (base : s.getReg .x6 = 6143#64)
    (done' : ∀ k, n < k → k < 512 → machineMarks s k = markWord groups k) :
    ∀ k, 0 < k → k < 512 → machineMarks (markPass s n) k = markWord groups k := by
  induction n generalizing s with
  | zero => exact done'
  | succ n ih =>
    apply ih (blockPrefix s (n+1) 4) (by omega)
      ((parent_register s _ .x6 (by decide) (by decide)).trans base)
    intro k lower upper
    change (blockPrefix s (n+1) 4).getMem (addr k) = _
    apply (congrFun (parent_mem s _ bound base) (addr k)).trans
    change (s.setMem (addr (n+1)) _).getMem (addr k) = _
    by_cases equal : k = n+1
    · subst k
      rw [MachineState.getMem_setMem_eq]
      change machineMarks s (2*(n+1)) ||| machineMarks s (2*(n+1)+1) = _
      rw [done' _ (by omega) (by omega), done' _ (by omega) (by omega)]
      exact (mark_word_parent groups ⟨n+1,bound⟩ (show 0 < n+1 by omega)).symm
    · have diff : addr k ≠ addr (n+1) := by
        intro eq
        unfold addr at eq
        unfold markBase at eq
        have := nat_address_injective (by omega) (by omega) eq
        omega
      rw [MachineState.getMem_setMem_ne diff]
      exact done' _ (by omega) upper

def unrollEnter (s : MachineState) : MachineState :=
  (s.setReg .x6 (s.getReg .x26 + 2047)).setPC (pcOf (index 255))

theorem entry_run (s : MachineState) (pc : s.pc = 0x10b0) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) s coins =
      (do let r ← execute openingImage fuel (unrollEnter s) coins
          return r.charge 2 0) := by
  let mid := s.setPC (pcOf 86)
  have f1 := opening_fetch s 44 (.JAL .x0 168) (by decide) pc rfl
  have h1 : ordinaryStep s (.base (.JAL .x0 168)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, mid, pc, pcOf, MachineState.setReg]
  have f2 := opening_fetch mid 86 (.ADDI .x6 .x26 2047) (by decide) rfl rfl
  have h2 : ordinaryStep mid (.base (.ADDI .x6 .x26 2047)) = some (unrollEnter s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, mid,
      unrollEnter, pcOf, index, MachineState.setReg, MachineState.setPC, MachineState.getReg]
  rw [show 2+fuel = fuel+1+1 by omega, execute_ordinary_step _ _ _ _ _ _ f1 h1,
    execute_ordinary_step _ _ _ _ _ _ f2 h2]
  simp [Execution.charge, instructionCycles, Nat.add_assoc, ← Nat.add_assoc]

theorem return_run (s : MachineState) (pc : s.pc = pcOf (index 0)) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) s coins =
      (do let r ← execute openingImage fuel (s.setPC 0x10dc) coins
          return r.charge 1 0) := by
  have f := opening_fetch s 1107 (.JAL .x0 2092944) (by decide) pc rfl
  have h : ordinaryStep s (.base (.JAL .x0 2092944)) = some (s.setPC 0x10dc) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc, pcOf, index, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ f h]
  rfl

end TwoPermutationPrototype.Opening
