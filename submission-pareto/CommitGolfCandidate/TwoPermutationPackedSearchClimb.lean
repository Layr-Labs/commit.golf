import CommitGolfCandidate.TwoPermutationPackedSearchHead

/-! # One-byte search: the climb step (check words 1190..1201) and the climb as a function -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt write_bits_word_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

attribute [local irreducible] execute readBuffer writeBits

@[local simp] private theorem search_reg_zero (s : MachineState) : s.getReg .x0 = 0#64 := rfl
@[local simp] private theorem search_sext_zero : signExtend12 (0#12) = 0#64 := by decide

private theorem reg_setReg (s : MachineState) (rd rs : Reg) (v : Word) :
    (s.setReg rd v).getReg rs = if rd = rs ∧ rd ≠ .x0 then v else s.getReg rs :=
  Opening.getReg_setReg s rd rs v

/-! ### One climb step (1190..1201): recompute the parent of the current node

The instructions are the walk's parent call (334..339) and 238-bit mask (700..703), laid out contiguously. -/

structure ClimbReady (s : MachineState) (n : Nat) : Prop where
  pc : s.pc = spc 1190
  node : s.getReg .x6 = BitVec.ofNat 64 n
  roots : s.getReg .x25 = 16384#64
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 64
  primitive : s.getReg .x13 = 0
  low : 2 ≤ n
  bound : n < 512

/-- After the reply: the mask, then `addi x7,x0,1; bne x6,x7,<1190>`. -/
def climbReply (s : MachineState) (answer : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (maskAfter (capCompressionAnswer (capParent s) answer) .x12 28) (.ADDI .x7 .x0 1))
    (.BNE .x6 .x7 8148)

def climbQuery (s : MachineState) (parent : Nat) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl (capRootAt s (2*parent+1) ++ capRootAt s (2*parent))))
  return climbReply s answer

theorem climb_parent_post (s : MachineState) (pc : s.pc = spc 1190) :
    let next := capParent s
    let parent := s.getReg .x6 >>> 1
    next.pc = spc 1195 ∧ next.getReg .x6 = parent ∧
    next.getReg .x10 = s.getReg .x25 + (parent <<< 6) ∧
    next.getReg .x12 = s.getReg .x25 + (parent <<< 5) ∧ next.mem = s.mem := by
  intro next parent
  let s1 := execInstrBr s (.SRLI .x6 .x6 1)
  let s2 := execInstrBr s1 (.SLLI .x10 .x6 6)
  let s3 := execInstrBr s2 (.ADD .x10 .x25 .x10)
  let s4 := execInstrBr s3 (.SLLI .x12 .x6 5)
  have same : next = execInstrBr s4 (.ADD .x12 .x25 .x12) := rfl
  have r6 : s4.getReg .x6 = parent := by simp [s4, s3, s2, s1, execInstrBr, reg_setReg, parent]
  have r25 : s4.getReg .x25 = s.getReg .x25 := by simp [s4, s3, s2, s1, execInstrBr, reg_setReg]
  have r10 : s4.getReg .x10 = s.getReg .x25 + (parent <<< 6) := by
    simp [s4, s3, s2, s1, execInstrBr, reg_setReg, parent]
  have r12 : s4.getReg .x12 = parent <<< 5 := by simp [s4, s3, s2, s1, execInstrBr, reg_setReg, parent]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [same, straight_pc _ _ (by rfl), straight_pc _ _ (by rfl), straight_pc _ _ (by rfl),
      straight_pc _ _ (by rfl), straight_pc _ _ (by rfl), pc]; decide
  · rw [same]; simp [execInstrBr, reg_setReg, r6]
  · rw [same]; simp [execInstrBr, reg_setReg, r10]
  · rw [same]; simp [execInstrBr, reg_setReg, r12, r25]
  · rw [same]; rfl

private theorem climb_xor (g : Nat) : (g^^^1)/2=g/2 ∧ (g^^^1)%2=1-g%2 := by
  constructor
  · change (g^^^1)/2^1=g/2^1
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    have zero : (1:Nat) >>> 1 = 0 := by decide
    simp [zero]
  · change (g^^^1)%2^1=1-g%2
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt (by decide : (1:Nat)<2^1)]
    have small : ∀ b<2, b^^^1=1-b := by decide
    exact small (g%2^1) (by omega)

theorem addi_mem (t : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr t (.ADDI rd rs imm)).mem = t.mem := by
  cases rd <;> rfl

theorem climb_reply_mem (s : MachineState) (answer : BitVec 256) :
    (climbReply s answer).mem = (maskAfter (capCompressionAnswer (capParent s) answer) .x12 28).mem := by
  show (execInstrBr (execInstrBr (maskAfter (capCompressionAnswer (capParent s) answer) .x12 28) _) _).mem = _
  rw [(branch_mem _ _ _ _).1, addi_mem]

private theorem node_shift (node : Nat) (bounded : node < 2^64) :
    BitVec.ofNat 64 node >>> 1 = BitVec.ofNat 64 (node/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt (by omega : node/2 < 2^64), Nat.shiftRight_eq_div_pow]

theorem climb_parent_regs {s : MachineState} {n : Nat} (ready : ClimbReady s n) :
    (capParent s).pc = spc 1195 ∧ (capParent s).getReg .x6 = BitVec.ofNat 64 (n/2) ∧
      (capParent s).getReg .x10 = wordAddress (2048+8*(n/2)) ∧
      (capParent s).getReg .x12 = wordAddress (2048+4*(n/2)) ∧ (capParent s).mem = s.mem := by
  obtain ⟨pc, parent, source, dest, mem⟩ := climb_parent_post s ready.pc
  have room := ready.bound
  have shifted : s.getReg .x6 >>> 1 = BitVec.ofNat 64 (n/2) := by rw [ready.node, node_shift _ (by omega)]
  refine ⟨pc, by rw [parent, shifted], ?_, ?_, mem⟩
  · rw [source, ready.roots, shifted, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (n/2) * BitVec.ofNat 64 64 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
    congr 1
    omega
  · rw [dest, ready.roots, shifted, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (n/2) * BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
    congr 1
    omega

theorem climb_setup {s : MachineState} {n : Nat} (ready : ClimbReady s n) : Hop s (capParent s) 5 5 := by
  let s1 := execInstrBr s (.SRLI .x6 .x6 1)
  let s2 := execInstrBr s1 (.SLLI .x10 .x6 6)
  let s3 := execInstrBr s2 (.ADD .x10 .x25 .x10)
  let s4 := execInstrBr s3 (.SLLI .x12 .x6 5)
  have p1 : s1.pc = spc 1191 := by rw [straight_pc _ _ (by rfl), ready.pc]; decide
  have p2 : s2.pc = spc 1192 := by rw [straight_pc _ _ (by rfl), p1]; decide
  have p3 : s3.pc = spc 1193 := by rw [straight_pc _ _ (by rfl), p2]; decide
  have p4 : s4.pc = spc 1194 := by rw [straight_pc _ _ (by rfl), p3]; decide
  have a := search_step s 1190 _ ready.pc (by decide) searchCode1190 rfl rfl
  have b := search_step s1 1191 _ p1 (by decide) searchCode1191 rfl rfl
  have c := search_step s2 1192 _ p2 (by decide) searchCode1192 rfl rfl
  have d := search_step s3 1193 _ p3 (by decide) searchCode1193 rfl rfl
  have e := search_step s4 1194 _ p4 (by decide) searchCode1194 rfl rfl
  have same : capParent s = execInstrBr s4 (.ADD .x12 .x25 .x12) := rfl
  rw [same]
  exact (((a.thenDo b).thenDo c).thenDo d).thenDo e

theorem climb_answer_regs (s : MachineState) (answer : BitVec 256) (r : Reg) :
    (capCompressionAnswer (capParent s) answer).getReg r = (capParent s).getReg r :=
  cap_compression_register _ _ r

/-- The mask and the loop test after the reply. -/
theorem climb_tail {s : MachineState} {n : Nat} (ready : ClimbReady s n) (answer : BitVec 256) :
    Hop (capCompressionAnswer (capParent s) answer) (climbReply s answer) 6 6 := by
  obtain ⟨ppc, p6, p10, p12, pmem⟩ := climb_parent_regs ready
  have room := ready.bound
  let a := capCompressionAnswer (capParent s) answer
  have apc : a.pc = spc 1196 := by rw [cap_answer_pc, ppc]; decide
  have a12 : a.getReg .x12 = wordAddress (2048+4*(n/2)) := (climb_answer_regs s answer .x12).trans p12
  have addr : a.getReg .x12 + signExtend12 28 = BitVec.ofNat 64 (8*(2048+4*(n/2))+24+4) := by
    rw [a12, wordAddress, show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  let s1 := execInstrBr a (.LHU .x31 .x12 28)
  let s2 := execInstrBr s1 (.SLLI .x31 .x31 50)
  let s3 := execInstrBr s2 (.SRLI .x31 .x31 50)
  let s4 := maskAfter a .x12 28
  let s5 := execInstrBr s4 (.ADDI .x7 .x0 1)
  have p1 : s1.pc = spc 1197 := by rw [straight_pc _ _ (by rfl), apc]; decide
  have p2 : s2.pc = spc 1198 := by rw [straight_pc _ _ (by rfl), p1]; decide
  have p3 : s3.pc = spc 1199 := by rw [straight_pc _ _ (by rfl), p2]; decide
  have r3 : s3.getReg .x12 = a.getReg .x12 := by
    simp only [s3, s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x31 ≠ .x12 by decide)]
  have post := mask_post a .x12 28 (8*(2048+4*(n/2))+24) addr (by omega) (by decide)
  have p4 : s4.pc = spc 1200 := by rw [post.pc, apc]; decide
  have p5 : s5.pc = spc 1201 := by rw [straight_pc _ _ (by rfl), p4]; decide
  have h1 := search_step a 1196 _ apc (by decide) searchCode1196 rfl (by
    simp only [memoryArgumentsValid, memAccess, addr]
    exact access_ofNat _ 2 (by unfold MEMORY_BYTES; omega) (by omega))
  have h2 := search_step s1 1197 _ p1 (by decide) searchCode1197 rfl rfl
  have h3 := search_step s2 1198 _ p2 (by decide) searchCode1198 rfl rfl
  have h4 := search_step s3 1199 _ p3 (by decide) searchCode1199 rfl (by
    simp only [memoryArgumentsValid, memAccess, r3, addr]
    exact access_ofNat _ 4 (by unfold MEMORY_BYTES; omega) (by omega))
  have h5 := search_step s4 1200 _ p4 (by decide) searchCode1200 rfl rfl
  have h6 := search_step s5 1201 _ p5 (by decide) searchCode1201 rfl rfl
  exact ((((h1.thenDo h2).thenDo h3).thenDo h4).thenDo h5).thenDo h6

theorem climb_reply_regs {s : MachineState} {n : Nat} (ready : ClimbReady s n) (answer : BitVec 256) :
    let t := climbReply s answer
    t.getReg .x6 = BitVec.ofNat 64 (n/2) ∧
      t.pc = (if n/2 = 1 then spc 1202 else spc 1190) ∧
      ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x31 → t.getReg r = s.getReg r := by
  obtain ⟨ppc, p6, p10, p12, pmem⟩ := climb_parent_regs ready
  have room := ready.bound
  let a := capCompressionAnswer (capParent s) answer
  have addr : a.getReg .x12 + signExtend12 28 = BitVec.ofNat 64 (8*(2048+4*(n/2))+24+4) := by
    rw [climb_answer_regs, p12, wordAddress, show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  have post := mask_post a .x12 28 (8*(2048+4*(n/2))+24) addr (by omega) (by decide)
  let s4 := maskAfter a .x12 28
  let s5 := execInstrBr s4 (.ADDI .x7 .x0 1)
  have apc : a.pc = spc 1196 := by rw [cap_answer_pc, ppc]; decide
  have p4 : s4.pc = spc 1200 := by rw [post.pc, apc]; decide
  have p5 : s5.pc = spc 1201 := by rw [straight_pc _ _ (by rfl), p4]; decide
  have x6_5 : s5.getReg .x6 = BitVec.ofNat 64 (n/2) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, reg_setReg]
    simp only [show ¬ (Reg.x7 = .x6 ∧ Reg.x7 ≠ .x0) by decide, if_false]
    rw [post.regs .x6 (by decide), climb_answer_regs, p6]
  have x7_5 : s5.getReg .x7 = 1#64 := by simp [s5, execInstrBr, reg_setReg] <;> decide
  refine ⟨?_, ?_, ?_⟩
  · show (execInstrBr s5 _).getReg .x6 = _
    rw [(branch_reg _ _ _ _ _).1, x6_5]
  · show (execInstrBr s5 _).pc = _
    rw [bne_pc, x6_5, x7_5, p5]
    by_cases one : n/2 = 1
    · rw [if_pos (by rw [one]), if_pos one]; decide
    · have ne : BitVec.ofNat 64 (n/2) ≠ 1#64 := by
        intro e
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega
      rw [if_neg ne, if_neg one]; decide
  · intro r a6 a7 a10 a12 a31
    show (execInstrBr s5 _).getReg r = _
    rw [(branch_reg _ _ _ _ _).1]
    simp only [s5, execInstrBr, MachineState.getReg_setPC, reg_setReg]
    rw [if_neg (by intro h; exact a7 h.1.symm), post.regs r a31, climb_answer_regs, cap_parent_register s r a6 a10 a12]

/-- The parent slot after a climb step holds `pad238` of the reply. -/
theorem climb_digest {s : MachineState} {n : Nat} (ready : ClimbReady s n) (answer : BitVec 256) :
    capRootAt (climbReply s answer) (n/2) = pad238 answer := by
  obtain ⟨ppc, p6, p10, p12, pmem⟩ := climb_parent_regs ready
  have bound := ready.bound
  let a := capCompressionAnswer (capParent s) answer
  have addr : a.getReg .x12 + signExtend12 28 = BitVec.ofNat 64 (8*(2048+4*(n/2))+24+4) := by
    rw [climb_answer_regs, p12, wordAddress, show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  have words : ∀ k < 4, a.getMem (BitVec.ofNat 64 (8*(2048+4*(n/2))+8*k)) = answer.extractLsb' (64*k) 64 := by
    intro k small
    show (capCompressionAnswer (capParent s) answer).getMem _ = _
    unfold capCompressionAnswer
    rw [p12]
    exact written_dword _ _ k answer (by omega) small
  have masked := masked_slot_digest a .x12 (8*(2048+4*(n/2))) answer (by omega) (by omega) addr (by decide) words
  unfold capRootAt
  rw [← masked]
  apply read_digest_congr _ _ _ (by omega)
  intro _ _
  unfold MachineState.getMem
  rw [climb_reply_mem]

/-- A climb step changes only the parent slot. -/
theorem climb_frame {s : MachineState} {n : Nat} (ready : ClimbReady s n) (answer : BitVec 256) (word : Nat)
    (bound : word < 2^61) (outside : word < 2048+4*(n/2) ∨ 2048+4*(n/2)+4 ≤ word) :
    memoryView (climbReply s answer) word = memoryView s word := by
  obtain ⟨ppc, p6, p10, p12, pmem⟩ := climb_parent_regs ready
  have room := ready.bound
  let a := capCompressionAnswer (capParent s) answer
  have addr : a.getReg .x12 + signExtend12 28 = BitVec.ofNat 64 (8*(2048+4*(n/2))+24+4) := by
    rw [climb_answer_regs, p12, wordAddress, show signExtend12 28 = BitVec.ofNat 64 28 from rfl, ← BitVec.ofNat_add]
  have post := mask_post a .x12 28 (8*(2048+4*(n/2))+24) addr (by omega) (by decide)
  have masked : memoryView (maskAfter a .x12 28) word = memoryView a word := by
    unfold memoryView
    apply post.other
    unfold wordAddress
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega
  have written : memoryView a word = memoryView (capParent s) word := by
    show memoryView (capCompressionAnswer (capParent s) answer) word = _
    unfold capCompressionAnswer
    rw [p12]
    exact write_bits_word_outside _ answer _ _ (by omega) bound (by omega)
  rw [view_of_mem (climb_reply_mem s answer), masked, written, view_of_mem pmem]

/-! ### The climb step as a segment -/

theorem execute_climb {s : MachineState} {n : Nat} (ready : ClimbReady s n) (fuel : Nat) :
    execute packedImage (12+fuel) s false =
      (do let next ← climbQuery s (n/2)
          let result ← execute packedImage fuel next false
          return result.charge 19 1) := by
  obtain ⟨ppc, p6, src, dst, mem⟩ := climb_parent_regs ready
  have room := ready.bound
  have control (r : Reg) (a : r ≠ .x6) (b : r ≠ .x10) (c : r ≠ .x12) :
      (capParent s).getReg r = s.getReg r := cap_parent_register s r a b c
  have select : (capParent s).getReg .x5=0 ∧ (capParent s).getReg .x11=64 ∧ (capParent s).getReg .x13=0 :=
    ⟨(control _ (by decide) (by decide) (by decide)).trans ready.selector,
      (control _ (by decide) (by decide) (by decide)).trans ready.size,
      (control _ (by decide) (by decide) (by decide)).trans ready.primitive⟩
  have lim : MEMORY_BYTES < 2^64 := by decide
  have memLimit : 32768 ≤ MEMORY_BYTES := by decide
  have srcV : rangeValid ((capParent s).getReg .x10) 64 = true := by
    simp only [src, wordAddress, rangeValid, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8*(2048+8*(n/2)) < 2^64), decide_eq_true_eq]
    omega
  have dstV : rangeValid ((capParent s).getReg .x12) 32 = true := by
    simp only [dst, wordAddress, rangeValid, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8*(2048+4*(n/2)) < 2^64), decide_eq_true_eq]
    omega
  have asrc : ((capParent s).getReg .x10).toNat % 8 = 0 := by
    simp only [src, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(2048+8*(n/2)) < 2^64)]
    omega
  have adst : ((capParent s).getReg .x12).toNat % 8 = 0 := by
    simp only [dst, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(2048+4*(n/2)) < 2^64)]
    omega
  have fetched : fetch packedImage (capParent s) = some (.base .ECALL) :=
    wide_image_fetch _ _ 1195 _ (by decide) ppc searchCode1195
  have call := cap_compression_execute packedImage (capParent s) fetched select srcV dstV asrc adst (6+fuel) false
  have inner : readBuffer (capParent s) ((capParent s).getReg .x10).toNat 64 =
      capRootAt s (2*(n/2)+1) ++ capRootAt s (2*(n/2)) := by
    rw [src, wordAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(2048+8*(n/2)) < 2^64),
      read_compression_halves _ _ (by omega)]
    unfold capRootAt
    have offset : 8*(2048+8*(n/2))+32 = 8*(2048+4*(2*(n/2)+1)) := by omega
    have base : 8*(2048+8*(n/2)) = 8*(2048+4*(2*(n/2))) := by omega
    rw [offset, base]
    congr 1 <;> apply read_digest_congr _ _ _ (by omega) <;>
      intro i _ <;> exact congrFun mem _
  rw [show 12+fuel = 5+(1+(6+fuel)) by omega, climb_setup ready (1+(6+fuel)), call]
  unfold capCompressionInput
  erw [inner]
  simp only [climbQuery, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  rw [climb_tail ready answer fuel]
  simp only [Execution.charge, bind_assoc, pure_bind, ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]

theorem climb_rows (oracle : Oracle) (s : MachineState) (parent : Nat) :
    let pair := capRootAt s (2*parent+1) ++ capRootAt s (2*parent)
    let reply := oracle.compression pair
    checkEvaluation oracle (recordRows (climbQuery s parent)) =
      ((climbReply s reply, [.compression pair reply]), 1) := by
  simp only [climbQuery, record_rows_query, check_evaluation_public_bind, check_evaluation_map,
    record_rows_pure, check_evaluation_pure]
  rfl

def climbSegment (oracle : Oracle) {s : MachineState} {n : Nat} (ready : ClimbReady s n) :
    let parent := n/2
    let pair := capRootAt s (2*parent+1) ++ capRootAt s (2*parent)
    Segment oracle s (climbReply s (oracle.compression pair)) :=
  Segment.query oracle 12 19 (climbQuery s (n/2)) _ (execute_climb ready) (climb_rows oracle s (n/2))

/-! ### The climb as a function -/

/-- A trial's climb from node `n` holding `v`, `d` levels, with the siblings' slots `σ`: the rows and the root. -/
def climbFrom (oracle : Oracle) (σ : Nat → BitVec 256) : Nat → Nat → BitVec 256 → List PublicRow × BitVec 256
  | 0, _, v => ([], v)
  | d+1, n, v =>
    let pair := pathPair n v (σ (n ^^^ 1))
    let rest := climbFrom oracle σ d (n/2) (pad238 (oracle.compression pair))
    (.compression pair (oracle.compression pair) :: rest.1, rest.2)

theorem pair_children (n : Nat) (v w : BitVec 256) (left right : BitVec 256)
    (here : (if n % 2 = 0 then left else right) = v) (there : (if n % 2 = 0 then right else left) = w) :
    right ++ left = pathPair n v w := by
  unfold pathPair
  by_cases even : n % 2 = 0
  · rw [if_pos even] at here there ⊢
    rw [here, there]
  · rw [if_neg even] at here there ⊢
    rw [here, there]

/-- The slot words of node `m`. -/
def SlotWord (m word : Nat) : Prop := 2048+4*m ≤ word ∧ word < 2048+4*m+4

/-- The climb: from node `n` with `2^d ≤ n < 2^(d+1)`, `d ≥ 1` steps to word 1202. The rows are `climbFrom`'s, the
root slot holds its root, only the ancestors' slots change, and the registers the loop keeps are kept. -/
theorem climb_run (oracle : Oracle) (σ : Nat → BitVec 256) :
    ∀ (d n : Nat) (v : BitVec 256) (s : MachineState), ClimbReady s n → 1 ≤ d → 2^d ≤ n → n < 2^(d+1) →
      capRootAt s n = v → (∀ i, i < d → capRootAt s ((n/2^i) ^^^ 1) = σ ((n/2^i) ^^^ 1)) →
      ∃ (t : MachineState) (seg : Segment oracle s t), seg.rows = (climbFrom oracle σ d n v).1 ∧
        seg.steps = 12*d ∧ seg.cycles = 19*d ∧ t.pc = spc 1202 ∧ capRootAt t 1 = (climbFrom oracle σ d n v).2 ∧
        (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x31 → t.getReg r = s.getReg r) ∧
        ∀ word < 2^61, (∀ i, 1 ≤ i → i ≤ d → ¬ SlotWord (n/2^i) word) → memoryView t word = memoryView s word := by
  intro d
  induction d with
  | zero => intro _ _ _ _ bad; omega
  | succ d ih =>
    intro n v s ready _ lo hi value sibs
    have room := ready.bound
    have pow : 2^(d+1) = 2*2^d := by rw [Nat.pow_succ]; ring
    have pow2 : 2^(d+1+1) = 4*2^d := by rw [Nat.pow_succ, Nat.pow_succ]; ring
    let p := n/2
    let pair := capRootAt s (2*p+1) ++ capRootAt s (2*p)
    let answer := oracle.compression pair
    let t1 := climbReply s answer
    let seg1 : Segment oracle s t1 := climbSegment oracle ready
    have sib0 := sibs 0 (by omega)
    simp only [Nat.pow_zero, Nat.div_one] at sib0
    have pairEq : pair = pathPair n v (σ (n ^^^ 1)) := by
      apply pair_children
      · by_cases even : n % 2 = 0
        · rw [if_pos even, ← value]; congr 1; omega
        · rw [if_neg even, ← value]; congr 1; omega
      · by_cases even : n % 2 = 0
        · rw [if_pos even, ← sib0]; congr 1; have := climb_xor n; omega
        · rw [if_neg even, ← sib0]; congr 1; have := climb_xor n; omega
    obtain ⟨t1x6, t1pc, t1regs⟩ := climb_reply_regs ready answer
    have t1slot : capRootAt t1 p = pad238 answer := climb_digest ready answer
    have t1frame := climb_frame ready answer
    by_cases top : d = 0
    · subst top
      have p1 : p = 1 := by simp at lo hi; omega
      refine ⟨t1, seg1, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · show [PublicRow.compression pair answer] = _
        simp [climbFrom, pairEq, answer]
      · rw [t1pc, if_pos p1]
      · calc capRootAt t1 1 = capRootAt t1 p := by rw [p1]
          _ = pad238 answer := t1slot
          _ = _ := by simp [climbFrom, pairEq, answer]
      · exact t1regs
      · intro word bound outside
        apply t1frame word bound
        have := outside 1 (by omega) (by omega)
        simp only [SlotWord, Nat.pow_one] at this
        omega
    · have pLow : 2 ≤ p := by
        have : 2^1 ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have readyP : ClimbReady t1 p := by
        refine ⟨?_, t1x6, ?_, ?_, ?_, ?_, pLow, by omega⟩
        · rw [t1pc, if_neg (by omega)]
        · rw [t1regs .x25 (by decide) (by decide) (by decide) (by decide) (by decide), ready.roots]
        · rw [t1regs .x5 (by decide) (by decide) (by decide) (by decide) (by decide), ready.selector]
        · rw [t1regs .x11 (by decide) (by decide) (by decide) (by decide) (by decide), ready.size]
        · rw [t1regs .x13 (by decide) (by decide) (by decide) (by decide) (by decide), ready.primitive]
      have sibsP : ∀ i, i < d → capRootAt t1 ((p/2^i) ^^^ 1) = σ ((p/2^i) ^^^ 1) := by
        intro i small
        have shifted : p/2^i = n/2^(i+1) := by
          rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        have old := sibs (i+1) (by omega)
        rw [← shifted] at old
        rw [← old]
        unfold capRootAt
        apply read_digest_congr _ _ _ (by omega)
        intro j small'
        simp only [← Nat.mul_add]
        -- the sibling of an ancestor is not the parent p
        have x := climb_xor (p/2^i)
        have range := Nat.div_le_self p (2^i)
        by_cases zero : i = 0
        · subst zero
          simp only [Nat.pow_zero, Nat.div_one] at x range ⊢
          apply t1frame _ (by omega)
          omega
        · have h2 : p/2^i ≤ p/2 := Nat.div_le_div_left (Nat.le_self_pow zero 2) (by decide)
          apply t1frame _ (by omega)
          omega
      obtain ⟨t, seg2, rows, steps, cycles, tpc, troot, tregs, tframe⟩ :=
        ih p (pad238 answer) t1 readyP (by omega) (by omega) (by omega) t1slot sibsP
      refine ⟨t, seg1.append seg2, ?_, ?_, ?_, tpc, ?_, ?_, ?_⟩
      · show seg1.rows ++ seg2.rows = _
        rw [rows]
        show [PublicRow.compression pair answer] ++ _ = _
        simp [climbFrom, pairEq, answer, p]
      · show seg1.steps + seg2.steps = _
        rw [steps]
        show 12 + 12*d = _
        ring
      · show seg1.cycles + seg2.cycles = _
        rw [cycles]
        show 19 + 19*d = _
        ring
      · rw [troot]
        simp [climbFrom, pairEq, answer, p]
      · intro r a b c e f
        rw [tregs r a b c e f, t1regs r a b c e f]
      · intro word bound outside
        rw [tframe word bound ?_]
        · apply t1frame word bound
          have := outside 1 (by omega) (by omega)
          simp only [SlotWord, Nat.pow_one] at this
          omega
        · intro i lo' hi'
          have shifted : p/2^i = n/2^(i+1) := by
            rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
          rw [shifted]
          exact outside (i+1) (by omega) (by omega)

end TwoPermutationPrototype.Packed.Checker
