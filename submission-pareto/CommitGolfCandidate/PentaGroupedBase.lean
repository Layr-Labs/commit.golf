import CommitGolfCandidate.QuadCommitArtifactW
import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationOpeningCopy
import CommitGolfCandidate.TwoPermutationLeafRun

/-! Base definitions and straight-line action kernel for the 4,095-leaf counter-mode
prefix of the 5-ary (penta) commit image (words 0 .. 45,200). -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Quad.Commit
set_option maxRecDepth 18000
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

abbrev image : Image := Quad.Commit.image

theorem image_eq_artifact : image = Artifact.submission.image .commit :=
  ArtifactMatchB.quad_commit_image.symm

def codeWord (index : Nat) : BitVec 32 :=
  if inside : index < 215278 then Artifact.commitCode.get 32 ⟨index, inside⟩ else 0

def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4 * index)

theorem fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 215278) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (codeWord index) = some instruction) :
    fetch image state = some (.base instruction) := by
  have address : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have code : image.code = ArtifactEncoding.decode 32 Artifact.commitCode := by
    rw [image_eq_artifact]; rfl
  have length : index < image.code.length := by
    rw [code, ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : image.code[index]? = some (Artifact.commitCode.get 32 ⟨index, inCode⟩) := by
    rw [List.getElem?_eq_getElem length, ← List.getD_eq_getElem _ _ length, code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch, address, ite_eq_left (by omega), show (4096 + 4 * index - 4096) / 4 = index by omega, atIndex]
  have base : Manifest.decodeBase (Artifact.commitCode.get 32 ⟨index, inCode⟩) = some instruction := by
    simpa only [codeWord, dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (Artifact.commitCode.get 32 ⟨index, inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all

/-- Number of salt-generator heads among the first `n` leaves of the 4,095-leaf period. -/
def heads (n : Nat) : Nat := 373 * (n / 4095) + ((n % 4095 + 10) / 11)

def rank (n : Nat) : Nat := (n % 4095) % 11

/-- Register-prefetch credit charged to earlier leaves in the same 11-leaf group. -/
def cacheCredit (n : Nat) : Nat :=
  if n % 4095 ≥ 4092 ∨ rank n = 0 then 0 else if rank n ≤ 9 then 4 else 2

def bodyLen (n : Nat) : Nat :=
  if rank n = 0 then (if n % 4095 = 4092 then 11 else 15) else if rank n ≤ 8 then 11 else 9

/-- Number of 45-leaf destination-window rebases before slot `n` inside a 4,095-leaf body. -/
def rb (n : Nat) : Nat := n / 45

/-- Leaf slot `n` is followed by `addi x20, x12, 1776` rebasing the centered window. -/
def rebase (n : Nat) : Prop := rb (n + 1) ≠ rb n
instance (n : Nat) : Decidable (rebase n) := inferInstanceAs (Decidable (_ ≠ _))

def firstWord (n : Nat) : Nat := 17 + 11 * n + cacheCredit n + rb n

def sourceImm (n : Nat) : BitVec 12 := BitVec.ofNat 12 (3992 - 240 * rank n)

/-- One leaf packet inside the 4,095-leaf unrolled loop body (words 17 .. 45,152). -/
def packet (n : Nat) : List Instr :=
  [.ADDI .x12 .x10 (-32), .ECALL] ++
  (if rank n = 0 then
    [.SD .x24 .x10 0, .ADDI .x12 .x10 (-120), .ADDI .x10 .x24 0, .ECALL] ++
    (if n % 4095 = 4092 then [] else
       [.LD .x14 .x12 128, .LD .x15 .x12 136, .LD .x16 .x12 144, .LD .x17 .x12 152]) ++
     [.ADDI .x10 .x12 176, .SD .x10 .x10 0]
   else [.ADDI .x10 .x10 56, .SD .x10 .x10 0] ++
     (if rank n ≤ 8 then [.LD .x31 .x12 (sourceImm n), .SD .x10 .x31 8,
                          .LD .x31 .x12 (sourceImm n + 8), .SD .x10 .x31 16]
      else if rank n = 9 then [.SD .x10 .x14 8, .SD .x10 .x15 16]
      else [.SD .x10 .x16 8, .SD .x10 .x17 16])) ++
  [.ADDI .x12 .x20 (slotImmediate n), .ECALL, .ADDI .x10 .x10 200] ++
  (if rebase n then [.ADDI .x20 .x12 1776] else [])

/-- Trailing leaf packet for the final leaf `i = 2^24 - 1 = 4097 * 4095` (words 45,190 .. 45,200). -/
def trailingPacket : List Instr :=
  [.ADDI .x12 .x10 (-32), .ECALL,
   .SD .x24 .x10 0, .ADDI .x12 .x10 (-120), .ADDI .x10 .x24 0, .ECALL,
   .ADDI .x10 .x12 176, .SD .x10 .x10 0,
   .ADDI .x12 .x20 (slotImmediate 0), .ECALL, .ADDI .x10 .x10 200]

/-! ### Straight-line action kernel -/

inductive Action where
  | offset (dest base : Reg) (imm : BitVec 12) (result : Nat)
  | add (dest left right : Reg) (result : Nat)
  | load (dest base : Reg) (imm : BitVec 12) (addr : Nat)
  | store (base value : Reg) (imm : BitVec 12) (addr : Nat)
  | perm (src dst : Nat)

def Action.op : Action → Instr
  | .offset dest base imm _ => .ADDI dest base imm
  | .add dest left right _ => .ADD dest left right
  | .load dest base imm _ => .LD dest base imm
  | .store base value imm _ => .SD base value imm
  | .perm .. => .ECALL

def Action.calls : Action → Nat | .perm .. => 1 | _ => 0

def Action.valid (a : Action) (s : MachineState) : Prop :=
  match a with
  | .offset _ base imm result => s.getReg base + signExtend12 imm = wordAddress result
  | .add _ left right result => s.getReg left + s.getReg right = wordAddress result
  | .load _ base imm addr | .store base _ imm addr =>
      s.getReg base + signExtend12 imm = wordAddress addr ∧ addr + 1 ≤ 2^33
  | .perm src dst => s.getReg .x10 = wordAddress src ∧ s.getReg .x12 = wordAddress dst ∧
      s.getReg .x5 = 0 ∧ s.getReg .x11 = 200 ∧ s.getReg .x13 = 1 ∧ src + 25 ≤ 2^33 ∧ dst + 25 ≤ 2^33

def putReg (s : MachineState) (rd : Reg) (v : Word) := (s.setReg rd v).setPC (s.pc + 4)
def putWord (s : MachineState) (a : Nat) (v : Word) := (s.setMem (wordAddress a) v).setPC (s.pc + 4)

def Action.run (a : Action) (s : MachineState) : OracleComp World MachineState :=
  match a with
  | .offset dest _ _ result | .add dest _ _ result => pure (putReg s dest (wordAddress result))
  | .load dest _ _ addr => pure (putReg s dest (memoryView s addr))
  | .store _ value _ addr => pure (putWord s addr (s.getReg value))
  | .perm src dst => do
      let reply ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) src)))))
      return writeBits s (wordAddress dst) reply

def runOps : List Action → MachineState → OracleComp World MachineState
  | [], s => pure s
  | a :: rest, s => a.run s >>= runOps rest

def validOps : List Action → MachineState → Prop
  | [], _ => True
  | a :: rest, s => a.valid s ∧ ∀ t ∈ support (a.run s), validOps rest t

def opCalls (ops : List Action) := (ops.map Action.calls).sum

private theorem ordinary_charge (s t : MachineState) (op : Instr) (fuel : Nat) (coins : Bool)
    (cell : fetch image s = some (.base op)) (step : ordinaryStep s (.base op) = some t)
    (price : instructionCycles (.base op) = 1) :
    execute image (1 + fuel) s coins = (do let r ← execute image fuel t coins; return r.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, execute_ordinary_step image (.base op) s t fuel coins cell step, price]

theorem action_run (a : Action) (s : MachineState) (fuel : Nat) (coins : Bool)
    (cell : fetch image s = some (.base a.op)) (ok : a.valid s) :
    execute image (1 + fuel) s coins = (do
      let t ← a.run s
      let r ← execute image fuel t coins
      return r.charge (1 + 7 * a.calls) a.calls) := by
  cases a with
  | offset rd base imm addr =>
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge s _ _ _ _ cell _ rfl
    change some ((s.setReg rd (s.getReg base + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [show s.getReg base + signExtend12 imm = wordAddress addr from ok]; rfl
  | add rd left right addr =>
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge s _ _ _ _ cell _ rfl
    change some ((s.setReg rd (s.getReg left + s.getReg right)).setPC (s.pc + 4)) = _
    rw [show s.getReg left + s.getReg right = wordAddress addr from ok]; rfl
  | load rd base imm addr =>
    obtain ⟨atAddr, room⟩ := ok
    have access : accessValid (wordAddress addr) 8 = true := by simpa using leaf_word_access addr 0 (by omega)
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge s _ _ _ _ cell _ rfl
    simp only [ordinaryStep, Action.op, memoryArgumentsValid, memAccess, atAddr, access, ite_true, execInstrBr,
      putReg, memoryView]
  | store base value imm addr =>
    obtain ⟨atAddr, room⟩ := ok
    have access : accessValid (wordAddress addr) 8 = true := by simpa using leaf_word_access addr 0 (by omega)
    simp only [Action.run, pure_bind, Action.calls, Nat.mul_zero, Nat.add_zero]
    apply ordinary_charge s _ _ _ _ cell _ rfl
    simp only [ordinaryStep, Action.op, memoryArgumentsValid, memAccess, atAddr, access, ite_true, execInstrBr, putWord]
  | perm src dst =>
    obtain ⟨input, output, sel, size, pr, rs, rd⟩ := ok
    rw [Nat.add_comm 1 fuel, execute_permutation_call image fuel s coins src dst rs rd input output sel size pr cell]
    simp only [Action.run, bind_assoc, pure_bind, Action.calls]

theorem action_pc (a : Action) (s t : MachineState) (hit : t ∈ support (a.run s)) : t.pc = s.pc + 4 := by
  cases a <;> simp only [Action.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  all_goals first | subst t; rfl | obtain ⟨_, _, rfl⟩ := hit; exact written_pc ..

def fetchOps (index : Nat) (ops : List Action) :=
  ∀ (i : Fin ops.length) (s : MachineState), s.pc = wordPC (index + i.val) →
    fetch image s = some (.base ops[i].op)

theorem run_ops (ops : List Action) (index fuel : Nat) (s : MachineState) (coins : Bool)
    (pc : s.pc = wordPC index) (cells : fetchOps index ops) (ok : validOps ops s) :
    execute image (ops.length + fuel) s coins = (do
      let t ← runOps ops s
      let r ← execute image fuel t coins
      return r.charge (ops.length + 7 * opCalls ops) (opCalls ops)) := by
  induction ops generalizing index s with
  | nil => simp [runOps, opCalls, Execution.charge]
  | cons a rest ih =>
    have cell := cells ⟨0, by simp⟩ s (by simpa using pc)
    rw [show (a :: rest).length + fuel = 1 + (rest.length + fuel) by simp; omega,
      action_run a s _ coins cell ok.1]
    simp only [runOps, bind_assoc]
    apply bind_congr_of_forall_mem_support; intro t hit
    have tpc : t.pc = wordPC (index + 1) := by
      rw [action_pc a s t hit, pc, wordPC, wordPC, BitVec.ofNat_add]
      simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    have tail : fetchOps (index + 1) rest := by
      intro i st hp
      exact cells ⟨i.val + 1, by simp⟩ st (by simpa only [Nat.add_assoc, Nat.add_comm 1 i.val] using hp)
    rw [ih (index + 1) t tpc tail (ok.2 t hit)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro last
    apply bind_congr; intro r
    apply congrArg pure
    cases r
    simp [opCalls, Execution.charge, Nat.mul_add] <;> omega

end TwoPermutationPrototype.PentaGrouped
