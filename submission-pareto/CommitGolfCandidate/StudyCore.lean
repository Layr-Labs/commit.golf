import CommitGolfCandidate.GroupOpenImage

namespace CapStudy

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

abbrev openingImage : Image := TwoPermutationPrototype.GroupedOpening.openingImage

theorem execute_ordinary_step (image : Image) (instruction : Instruction)
    (state next : MachineState) (fuel : Nat) (allowCoins : Bool)
    (fetched : fetch image state = some instruction)
    (stepped : ordinaryStep state instruction = some next) :
    execute image (fuel + 1) state allowCoins =
      (do let result ← execute image fuel next allowCoins
          return result.charge (instructionCycles instruction) 0) := by
  cases instruction with
  | base instruction =>
    cases instruction <;> simp_all [execute, ordinaryStep]
  | word op rd rs1 rs2 => simp only [execute, fetched, stepped]
  | sraiw rd rs shift => simp only [execute, fetched, stepped]

def markBase : Nat := 4096
def trapdoorBase : Nat := 4096 + 256 * LENGTH + 32
def trapdoorBytes : Nat := 96 * LENGTH

theorem getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

theorem getReg_setReg (state : MachineState) (rd rs : Reg) (value : Word) :
    (state.setReg rd value).getReg rs =
      if rd = rs ∧ rd ≠ .x0 then value else state.getReg rs := by
  by_cases same : rd = rs
  · subst rs
    by_cases zero : rd = .x0
    · subst rd
      rfl
    · simp [zero, MachineState.getReg_setReg_eq]
  · simp [same, MachineState.getReg_setReg_ne]

theorem nat_address_injective {left right : Nat}
    (leftBound : left < 2 ^ 64) (rightBound : right < 2 ^ 64)
    (same : BitVec.ofNat 64 left = BitVec.ofNat 64 right) : left = right := by
  have x := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] at x
  exact x

theorem aligned_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address + 8 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2 ^ 64 := by
    unfold MEMORY_BYTES at bounded
    omega
  have natural : (BitVec.ofNat 64 address).toNat = address := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp [accessValid, rangeValid, natural, aligned, bounded]

theorem marks_before_trapdoor : markBase + 8 * 512 ≤ trapdoorBase := by
  decide

structure CapSpan (node height : Nat) : Prop where
  heightBound : height ≤ 8
  start : 256 ≤ node * 2 ^ height
  finish : (node + 1) * 2 ^ height ≤ 512

theorem cap_span_root : CapSpan 1 8 := ⟨by decide, by decide, by decide⟩

theorem cap_span_children (node height : Nat) (span : CapSpan node (height + 1)) :
    CapSpan (2 * node) height ∧ CapSpan (2 * node + 1) height := by
  have bound := span.heightBound
  have start := span.start
  have finish := span.finish
  have leftStart : (2 * node) * 2 ^ height = node * 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    ring
  have rightEnd : (2 * node + 1 + 1) * 2 ^ height = (node + 1) * 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    ring
  refine ⟨⟨by omega, by omega, ?_⟩, ⟨by omega, ?_, by omega⟩⟩
  · exact (Nat.mul_le_mul_right _ (by omega : 2 * node + 1 ≤ 2 * node + 1 + 1)).trans
      (rightEnd.trans_le finish)
  · exact start.trans (leftStart.symm.le.trans (Nat.mul_le_mul_right _ (by omega)))

theorem cap_span_node (node height : Nat) (span : CapSpan node height) :
    0 < node ∧ node < 512 := by
  have low := span.start
  have high := span.finish
  have finish : node + 1 ≤ (node + 1) * 2 ^ height := by
    exact Nat.le_mul_of_pos_right _ (by positivity)
  constructor
  · by_contra zero
    have eq : node = 0 := by omega
    simp [eq] at low
  · omega

theorem cap_span_is_leaf (node : Nat) (span : CapSpan node 0) : 256 ≤ node := by
  simpa using span.start

theorem cap_span_is_internal (node height : Nat) (span : CapSpan node (height + 1)) :
    node < 256 := by
  have pow : 2 ≤ 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    have positive : 0 < 2 ^ height := by positivity
    omega
  have growth := (Nat.mul_le_mul_left (node + 1) pow).trans span.finish
  omega

def decodeBase (word : BitVec 32) : Option Instr :=
  (decodeInstruction word).bind fun
    | .base instruction => some instruction
    | _ => none

theorem packed_fetch_raw (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 1867) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (openingImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch openingImage state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, ite_eq_left (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases word : openingImage.code[index]? with
  | none => simp [word] at decoded
  | some word => simpa [word] using decoded

end CapStudy
