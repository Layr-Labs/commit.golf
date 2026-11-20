import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.ProjectedMask
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! # The lower loop's compression call and what follows it

Word 234 is the per-level compression call (pair at 12544 → node at 12288). `lower_hash_with_tail`
composes it with any straight run from word 235 to word 236 (`GroupHop` from the call's answer state).
The L21 run (word 235 `jal` to 573; 573 `addi x7,x0,14`; 574 `beq x29,x7,+8`; 575 `sh x0,30(x23)`;
576 `jal` to 236) keeps the level-21 node whole for `x29 = 14` and clears its two top bytes otherwise. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

/-- The compression call at word 234 followed by an `n`-step run to `post answer`. -/
theorem lower_hash_with_tail (h : MachineState) (pc : h.pc = BitVec.ofNat 64 (4096+4*234))
    (src : h.getReg .x10 = BitVec.ofNat 64 12544) (dst : h.getReg .x12 = BitVec.ofNat 64 12288)
    (selector : h.getReg .x5 = 0 ∧ h.getReg .x11 = 64 ∧ h.getReg .x13 = 0)
    (n : Nat) (post : BitVec 256 → MachineState)
    (tail : ∀ answer : BitVec 256, GroupHop (capCompressionAnswer h answer) (post answer) n) (fuel : Nat) :
    execute packedImage (1+n+fuel) h false = do
      let answer ← World.query (.inr (.inl (readBuffer h 12576 32 ++ readBuffer h 12544 32)))
      let result ← execute packedImage fuel (post answer) false
      return result.charge (n+8) 1 := by
  have srcV : rangeValid (h.getReg .x10) 64 = true := by rw [src]; decide
  have dstV : rangeValid (h.getReg .x12) 32 = true := by rw [dst]; decide
  have asrc : (h.getReg .x10).toNat % 8 = 0 := by rw [src]; decide
  have adst : (h.getReg .x12).toNat % 8 = 0 := by rw [dst]; decide
  have call := cap_compression_execute packedImage h (fetch_at h 234 .ECALL (by decide) pc rfl) selector
    srcV dstV asrc adst (n+fuel) false
  change execute packedImage (1+(n+fuel)) h false = (do
    let answer ← World.query (.inr (.inl (readBuffer h (h.getReg .x10).toNat 64)))
    let result ← execute packedImage (n+fuel) (capCompressionAnswer h answer) false
    return result.charge 8 1) at call
  rw [src, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 12544 < 2^64),
    read_compression_halves h 12544 (by decide), show (12544:Nat)+32 = 12576 from rfl] at call
  rw [show 1+n+fuel = 1+(n+fuel) by omega, call]
  congr 1
  funext answer
  rw [tail answer fuel]
  simp only [bind_assoc, pure_bind, Execution.charge, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm]

/-! ### The L21 run from word 235 to word 236 -/

/-- Steps from word 235 to word 236: four when `x29 = 14` (no truncation), five otherwise. -/
def tailSteps (left : Nat) : Nat := if left = 14 then 4 else 5

/-- The node left at 12288 by loop counter `left`: whole for `left = 14`, top bytes cleared otherwise. -/
def levelProject (left : Nat) (x : BitVec 256) : BitVec 256 := if left = 14 then x else padLow x

/-- The state at word 236 after the L21 run: the projected node at 12288 and `x7 = 14`. -/
def l21Post (h : MachineState) (left : Nat) (answer : BitVec 256) : MachineState :=
  ((writeBits h (wordAddress 1536) (levelProject left answer)).setReg .x7 14).setPC (BitVec.ofNat 64 (4096+4*236))

private theorem one_step {s t : MachineState} {i : Instr} (fetched : fetch packedImage s = some (.base i))
    (stepped : ordinaryStep s (.base i) = some t) (cost : instructionCycles (.base i) = 1) : GroupHop s t 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped, cost]

private theorem sh_shape (t : MachineState) :
    execInstrBr t (.SH .x12 .x0 30) = (t.setHalfword (t.getReg .x12 + signExtend12 30) 0).setPC (t.pc+4) := by
  cases t
  rfl

private theorem sh_tail (t : MachineState) (p q r : Word) :
    (execInstrBr ((((t.setPC p).setReg .x7 14).setPC q).setPC r) (.SH .x23 .x0 30)).setPC 5040 =
      ((t.setHalfword (t.getReg .x23 + signExtend12 30) 0).setReg .x7 14).setPC 5040 := by
  cases t
  rfl

private theorem pc_chain (t : MachineState) (p q r : Word) :
    ((((t.setPC p).setReg .x7 14).setPC q).setPC r).setPC 5040 = (t.setReg .x7 14).setPC 5040 := by
  cases t
  rfl

private theorem drop_pc (t u : MachineState) (p : Word) (same : t.setPC p = u.setPC p) :
    (t.setReg .x7 14).setPC 5040 = (u.setReg .x7 14).setPC 5040 := by
  have both : ((t.setPC p).setReg .x7 14).setPC 5040 = ((u.setPC p).setReg .x7 14).setPC 5040 := by rw [same]
  have l : ((t.setPC p).setReg .x7 14).setPC 5040 = (t.setReg .x7 14).setPC 5040 := by cases t; rfl
  have r : ((u.setPC p).setReg .x7 14).setPC 5040 = (u.setReg .x7 14).setPC 5040 := by cases u; rfl
  rw [← l, ← r]
  exact both

/-- The post state in terms of the call's answer state (x12 = 12288 = `wordAddress 1536`). -/
private theorem post_shape (h : MachineState) (dst : h.getReg .x12 = BitVec.ofNat 64 12288) (left : Nat)
    (answer : BitVec 256) :
    l21Post h left answer = ((capCompressionAnswer h (levelProject left answer)).setReg .x7 14).setPC 5040 := by
  unfold l21Post capCompressionAnswer
  rw [dst]
  rfl

/-- Words 235 (`jal` 573) and 573 (`addi x7,x0,14`) from the call's answer state. -/
private theorem l21_head (h : MachineState) (pc : h.pc = BitVec.ofNat 64 (4096+4*234)) (answer : BitVec 256) :
    GroupHop (capCompressionAnswer h answer) (((capCompressionAnswer h answer).setPC 6388).setReg .x7 14 |>.setPC 6392) 2 := by
  let m := capCompressionAnswer h answer
  have moved : m.pc = h.pc + 4 := by
    show (capCompressionAnswer h answer).pc = h.pc + 4
    unfold capCompressionAnswer writeBits
    rfl
  have mpc : m.pc = 5036 := by rw [moved, pc]; rfl
  let a := m.setPC 6388
  have h0 : GroupHop m a 1 := by
    apply one_step (i := .JAL .x0 (BitVec.ofNat 21 1352))
    · exact fetch_at m 235 _ (by decide) (by rw [mpc]; rfl) rfl
    · have landing : m.pc + signExtend21 (BitVec.ofNat 21 1352) = 6388 := by rw [mpc]; rfl
      simp [a, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setReg, landing]
    · rfl
  have h1 : GroupHop a ((a.setReg .x7 14).setPC 6392) 1 := by
    apply one_step (i := .ADDI .x7 .x0 14)
    · exact fetch_at a 573 _ (by decide) rfl rfl
    · simp [a, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
        MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · rfl
  exact h0.thenDo h1

/-- `x29 = 14`: jump, `x7 = 14`, branch taken, jump back; the node is not truncated. -/
theorem l21_tail_full (h : MachineState) (pc : h.pc = BitVec.ofNat 64 (4096+4*234))
    (dst : h.getReg .x12 = BitVec.ofNat 64 12288) (counter : h.getReg .x29 = 14) (answer : BitVec 256) :
    GroupHop (capCompressionAnswer h answer) (l21Post h 14 answer) 4 := by
  let m := capCompressionAnswer h answer
  let b := ((m.setPC 6388).setReg .x7 14).setPC 6392
  have head : GroupHop m b 2 := l21_head h pc answer
  have bx29 : b.getReg .x29 = 14 := by
    show (((m.setPC 6388).setReg .x7 14).setPC 6392).getReg .x29 = _
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setPC,
      cap_compression_register, counter]
  have bx7 : b.getReg .x7 = 14 := by
    show (((m.setPC 6388).setReg .x7 14).setPC 6392).getReg .x7 = _
    rw [MachineState.getReg_setPC]
    rfl
  let c := b.setPC 6400
  have h2 : GroupHop b c 1 := by
    apply one_step (i := .BEQ .x29 .x7 8)
    · exact fetch_at b 574 _ (by decide) rfl rfl
    · have same : b.getReg .x29 = b.getReg .x7 := by rw [bx29, bx7]
      simp [c, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, same, signExtend13]
      rfl
    · rfl
  let e := c.setPC 5040
  have h3 : GroupHop c e 1 := by
    apply one_step (i := .JAL .x0 (BitVec.ofNat 21 0x1ffab0))
    · exact fetch_at c 576 _ (by decide) rfl rfl
    · have cpc : c.pc = 6400 := rfl
      have landing : c.pc + signExtend21 (BitVec.ofNat 21 0x1ffab0) = 5040 := by rw [cpc]; rfl
      simp [e, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setReg, landing]
    · rfl
  have run := (head.thenDo h2).thenDo h3
  have final : e = l21Post h 14 answer := by
    rw [post_shape h dst]
    exact pc_chain m 6388 6392 6400
  rw [final] at run
  exact run

/-- `x29 ≠ 14`: jump, `x7 = 14`, branch not taken, clear the top bytes, jump back. -/
theorem l21_tail_mask (h : MachineState) (left : Nat) (pc : h.pc = BitVec.ofNat 64 (4096+4*234))
    (dst : h.getReg .x12 = BitVec.ofNat 64 12288) (out : h.getReg .x23 = BitVec.ofNat 64 12288)
    (counter : h.getReg .x29 = BitVec.ofNat 64 left) (bound : left ≤ 14) (other : left ≠ 14)
    (answer : BitVec 256) :
    GroupHop (capCompressionAnswer h answer) (l21Post h left answer) 5 := by
  let m := capCompressionAnswer h answer
  have mreg (r : Reg) : m.getReg r = h.getReg r := cap_compression_register h answer r
  have moved : m.pc = h.pc + 4 := by
    show (capCompressionAnswer h answer).pc = h.pc + 4
    unfold capCompressionAnswer writeBits
    rfl
  let b := ((m.setPC 6388).setReg .x7 14).setPC 6392
  have head : GroupHop m b 2 := l21_head h pc answer
  have ne : h.getReg .x29 ≠ 14 := by
    rw [counter]
    intro same
    have := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact other this
  have bx29 : b.getReg .x29 = h.getReg .x29 := by
    show (((m.setPC 6388).setReg .x7 14).setPC 6392).getReg .x29 = _
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setPC, mreg]
  have bx7 : b.getReg .x7 = 14 := by
    show (((m.setPC 6388).setReg .x7 14).setPC 6392).getReg .x7 = _
    rw [MachineState.getReg_setPC]
    rfl
  let c := b.setPC 6396
  have h2 : GroupHop b c 1 := by
    apply one_step (i := .BEQ .x29 .x7 8)
    · exact fetch_at b 574 _ (by decide) rfl rfl
    · have differ : b.getReg .x29 ≠ b.getReg .x7 := by rw [bx29, bx7]; exact ne
      simp [c, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, differ]
      rfl
    · rfl
  let d := execInstrBr c (.SH .x23 .x0 30)
  have cx23 : c.getReg .x23 = BitVec.ofNat 64 12288 := by
    show ((((m.setPC 6388).setReg .x7 14).setPC 6392).setPC 6396).getReg .x23 = _
    rw [MachineState.getReg_setPC, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      MachineState.getReg_setPC, mreg, out]
  have h3 : GroupHop c d 1 := by
    apply one_step (i := .SH .x23 .x0 30)
    · exact fetch_at c 575 _ (by decide) rfl rfl
    · have valid : accessValid (c.getReg .x23 + signExtend12 30) 2 = true := by rw [cx23]; decide
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, valid, ↓reduceIte, d]
    · rfl
  let e := d.setPC 5040
  have dpc : d.pc = 6400 := by
    show (execInstrBr c (.SH .x23 .x0 30)).pc = _
    simp only [execInstrBr]
    rfl
  have h4 : GroupHop d e 1 := by
    apply one_step (i := .JAL .x0 (BitVec.ofNat 21 0x1ffab0))
    · exact fetch_at d 576 _ (by decide) (by rw [dpc]; rfl) rfl
    · have landing : d.pc + signExtend21 (BitVec.ofNat 21 0x1ffab0) = 5040 := by rw [dpc]; rfl
      simp [e, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setReg, landing]
    · rfl
  have run := ((head.thenDo h2).thenDo h3).thenDo h4
  have final : e = l21Post h left answer := by
    have tail : e = ((m.setHalfword (m.getReg .x23 + signExtend12 30) 0).setReg .x7 14).setPC 5040 :=
      sh_tail m 6388 6392 6396
    have masked := masked_reply_step h 12288 answer dst (by decide) (by decide)
    rw [sh_shape] at masked
    have e23 : m.getReg .x12 = m.getReg .x23 := by rw [mreg, mreg, dst, out]
    have pcs : m.pc + 4 = h.pc + 8 := by rw [moved, BitVec.add_assoc]; rfl
    rw [e23, pcs] at masked
    rw [tail, drop_pc _ _ _ masked, post_shape h dst]
    unfold levelProject
    rw [if_neg other]
  rw [final] at run
  exact run

end TwoPermutationPrototype.Packed.Checker
