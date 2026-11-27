import CommitGolfCandidate.TwoPermutationPackedOpeningInitial
import CommitGolfCandidate.TwoPermutationPackedOpeningABI
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.C3CommitMemory

/-! # The paired opener's pre-pass (opening image words 12 and 1435..1504)

The leader's word 12 becomes `jal zero,<1435>`. For the `count` sorted positions `i_k`:

pass 1 (words 1444..1475, one inverse permutation call per position): the reply of leaf `i` at
word `Rw + 25 i` (byte `R = TD + 2^29 + 168`) is inverted into scratch words 2048..2072; its salt
(input words 23, 24 for even `i`, words 0, 1 for odd `i`) and the mate's digest (reply words
`Rw + 25 i + 25 ..` for even `i`, `Rw + 25 i - 4 ..` for odd `i`) go to list words `Lw k .. Lw k + 6`
(`Lw k = 2^27 + 6 k`).

pass 2 (words 1481..1502): list words to the leader's salt slot (`TDw + 10 LENGTH + 2 i`, the
leader's nonce table) and to the mate's heap leaf slot (`TDw + 2^26 + 4 (i^1)`).

Then `addi s11,zero,256` (the leader's word 12) and `jal zero,<13>`. -/
namespace TwoPermutationPrototype.PackedOpening.Prepass
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.C3Leaves
-- Sequential elaboration, as in C3PAdmission (the verifier builds with parallel elaboration on two CPUs).
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem set_pc_pc (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem mem_set_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
@[local simp] private theorem mem_set_pc (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl

theorem reg_zero (s : MachineState) : s.getReg .x0 = 0 := rfl

abbrev opPC (k : Nat) : Word := BitVec.ofNat 64 (4096 + 4 * k)

/-- Word indices of the layout (bytes / 8). -/
def TDw : Nat := 536871428
def Rw : Nat := TDw + 2 ^ 26 + 21
def IW : Nat := 1023411204
def Lw (k : Nat) : Nat := 2 ^ 27 + 6 * k
def scratchW : Nat := 2048

theorem pre_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 1505) (pc : state.pc = opPC index)
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

theorem oracle_input_inverse (state : MachineState) (src dst : Nat)
    (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 2) :
    oracleInput state = some (.inr (.inr (packBuffer (window (memoryView state) src)))) := by
  have srcValue := word_address_value (word := src) (by omega)
  have dstValue := word_address_value (word := dst) (by omega)
  have fitsSrc : 8 * src + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have fitsDst : 8 * dst + 200 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have kind : (state.getReg .x13).toNat = 2 := by rw [primitive]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [input, output, size, srcValue, dstValue, rangeValid,
    fitsSrc, fitsDst, PERMUTATION_WIDTH, read_permutation_window]

theorem execute_inverse_call (image : Image) (fuel : Nat) (state : MachineState) (allowCoins : Bool)
    (src dst : Nat) (srcBound : src + 25 ≤ 2 ^ 33) (dstBound : dst + 25 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (selector : state.getReg .x5 = 0) (size : state.getReg .x11 = 200) (primitive : state.getReg .x13 = 2)
    (fetched : fetch image state = some (.base .ECALL)) :
    execute image (fuel + 1) state allowCoins = (do
      let answer ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView state) src)))))
      let result ← execute image fuel (writeBits state (wordAddress dst) answer) allowCoins
      pure (result.charge 30 1)) := by
  have ready := oracle_input_inverse state src dst srcBound dstBound input output size primitive
  simp only [execute, fetched, selector, ↓reduceIte, ready, output, writeOracleAnswer, oracleCycles,
    PERMUTATION_CYCLES]

/-! ### Abstract-state instruction lemmas -/

theorem ordinary_one (st next : MachineState) (instr : Instr) (fuel : Nat) (coins : Bool)
    (fetched : fetch openingImage st = some (.base instr)) (stepped : ordinaryStep st (.base instr) = some next)
    (unit : instructionCycles (.base instr) = 1) :
    execute openingImage (1 + fuel) st coins =
      (do let result ← execute openingImage fuel next coins; return result.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped, unit]

theorem charge_charge (r : Execution) (a b c d : Nat) : (r.charge a b).charge c d = r.charge (c + a) (d + b) := by
  simp only [Execution.charge, Nat.add_assoc]

theorem sd_step (t : MachineState) (b src : Reg) (imm : BitVec 12)
    (valid : accessValid (t.getReg b + signExtend12 imm) 8 = true) :
    ordinaryStep t (.base (.SD b src imm)) = some (execInstrBr t (.SD b src imm)) := by
  change (if memoryArgumentsValid t (.SD b src imm) = true then some (execInstrBr t (.SD b src imm)) else none) = _
  rw [show memoryArgumentsValid t (.SD b src imm) = accessValid (t.getReg b + signExtend12 imm) 8 from rfl, valid]
  rfl

theorem ld_step (t : MachineState) (rd b : Reg) (imm : BitVec 12)
    (valid : accessValid (t.getReg b + signExtend12 imm) 8 = true) :
    ordinaryStep t (.base (.LD rd b imm)) = some (execInstrBr t (.LD rd b imm)) := by
  change (if memoryArgumentsValid t (.LD rd b imm) = true then some (execInstrBr t (.LD rd b imm)) else none) = _
  rw [show memoryArgumentsValid t (.LD rd b imm) = accessValid (t.getReg b + signExtend12 imm) 8 from rfl, valid]
  rfl

theorem word_valid (a k : Nat) (imm : BitVec 12) (value : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (bound : a + k < 2 ^ 33) : accessValid (wordAddress a + signExtend12 imm) 8 = true := by
  rw [value]
  exact word_access a k bound

theorem written_pc' {bits : Nat} (s : MachineState) (dst : Word) (coins : BitVec bits) :
    (writeBits s dst coins).pc = s.pc + 4 := by simp only [writeBits, MachineState.setPC]

theorem write_word_point (X Y : Memory) (a : Nat) (d : Word) (w : Nat) (h : X w = Y w) :
    writeWord X a d w = writeWord Y a d w := by
  simp only [writeWord]
  split
  · rfl
  · exact h

/-- Register effect of every `setReg ; setPC` instruction. -/
theorem set_other (s : MachineState) (rd r : Reg) (v p : Word) (h : r ≠ rd) :
    ((s.setReg rd v).setPC p).getReg r = s.getReg r := by
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem set_same (s : MachineState) (rd : Reg) (v p : Word) (h : rd ≠ .x0) :
    ((s.setReg rd v).setPC p).getReg rd = v := by
  rw [MachineState.getReg_setPC]
  cases rd <;> first | exact absurd rfl h | rfl

theorem set_mem (s : MachineState) (rd : Reg) (v p : Word) : ((s.setReg rd v).setPC p).mem = s.mem := by
  cases rd <;> rfl

/-- `ld t6,la(rs) ; sd t6,sb(rd)`: one word copied. -/
theorem ld_sd_pair (t : MachineState) (rs rd : Reg) (hrs : rs ≠ .x31) (hrd : rd ≠ .x31)
    (a b la sb : Nat) (ra : t.getReg rs = wordAddress a) (rb : t.getReg rd = wordAddress b)
    (load store : BitVec 12) (lv : signExtend12 load = BitVec.ofNat 64 (8 * la))
    (sv : signExtend12 store = BitVec.ofNat 64 (8 * sb)) (bounded : b + sb < 2 ^ 61) :
    let u := execInstrBr (execInstrBr t (.LD .x31 rs load)) (.SD rd .x31 store)
    (∀ w < 2 ^ 61, memoryView u w = writeWord (memoryView t) (b + sb) (memoryView t (a + la)) w) ∧
      u.pc = t.pc + 4 + 4 ∧ (∀ g, g ≠ .x31 → u.getReg g = t.getReg g) := by
  intro u
  let l := execInstrBr t (.LD .x31 rs load)
  have lb : l.getReg rd = wordAddress b := (ld_other _ _ _ _ _ hrd).trans rb
  have l31 : l.getReg .x31 = memoryView t (a + la) := by
    rw [ld_same _ _ _ _ (by decide), ra, lv, address_up]
    rfl
  refine ⟨fun w hw => ?_, ?_, fun g h => (sd_reg _ _ _ _ _).trans (ld_other _ _ _ _ _ h)⟩
  · have same : u.mem = (l.setMem (l.getReg rd + signExtend12 store) (l.getReg .x31)).mem := sd_mem _ _ _ _
    rw [memoryView_congr same, lb, l31, sv, address_up, view_store _ (b + sb) w _ bounded hw]
    exact write_word_point _ _ _ _ _ (congrFun (memoryView_congr (ld_mem _ _ _ _)) w)
  · change (l.pc + 4) = _
    rw [ld_pc]

/-! ### Parity arithmetic of the pass-1 offsets -/

theorem parity_mask (i : Nat) (small : i < 2 ^ 63) :
    (BitVec.ofNat 64 i &&& signExtend12 1) + signExtend12 (4095 : BitVec 12) =
      if i % 2 = 0 then (-1 : Word) else 0 := by
  have one : signExtend12 (1 : BitVec 12) = 1 := by decide
  have neg : signExtend12 (4095 : BitVec 12) = -1 := by decide
  rw [one, neg]
  have low : BitVec.ofNat 64 i &&& 1 = BitVec.ofNat 64 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (1 : BitVec 64).toNat = 1 by rfl, Nat.and_one_is_mod]
    omega
  rw [low]
  split
  · rename_i h; rw [h]; decide
  · rename_i h; rw [show i % 2 = 1 by omega]; decide

theorem mask_and (m : Word) (c : Nat) (imm : BitVec 12) (value : signExtend12 imm = BitVec.ofNat 64 c)
    (i : Nat) (hm : m = if i % 2 = 0 then (-1 : Word) else 0) :
    m &&& signExtend12 imm = BitVec.ofNat 64 (if i % 2 = 0 then c else 0) := by
  rw [value, hm]
  split
  · rw [show (-1 : Word) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
  · simp

theorem times200 (i : Nat) (small : 200 * i < 2 ^ 64) :
    (BitVec.ofNat 64 i <<< (3 : BitVec 6).toNat) + (BitVec.ofNat 64 i <<< (6 : BitVec 6).toNat) +
      (BitVec.ofNat 64 i <<< (7 : BitVec 6).toNat) = BitVec.ofNat 64 (200 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (3 : BitVec 6).toNat = 3 by rfl, show (6 : BitVec 6).toNat = 6 by rfl,
    show (7 : BitVec 6).toNat = 7 by rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hi : i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hi]
  norm_num
  omega

theorem times200' (i : Nat) (small : 200 * i < 2 ^ 64) :
    (BitVec.ofNat 64 i <<< 3) + (BitVec.ofNat 64 i <<< 6) + (BitVec.ofNat 64 i <<< 7) =
      BitVec.ofNat 64 (200 * i) := times200 i small

theorem address_if (a c i : Nat) :
    wordAddress a + BitVec.ofNat 64 (if i % 2 = 0 then 8 * c else 0) =
      wordAddress (a + if i % 2 = 0 then c else 0) := by
  split
  · exact address_up a c
  · rw [Nat.add_zero]; exact BitVec.add_zero _

/-! ### Straight-line runs of ALU instructions and word copies -/

def runOps (s : MachineState) (ops : List Instr) : MachineState := ops.foldl execInstrBr s

theorem run_ops_append (s : MachineState) (a b : List Instr) : runOps s (a ++ b) = runOps (runOps s a) b := by
  simp [runOps, List.foldl_append]

theorem run_ops_singleton (s : MachineState) (op : Instr) : runOps s [op] = execInstrBr s op := rfl

theorem bne_pc (t : MachineState) (a b : Reg) (o : BitVec 13) :
    (execInstrBr t (.BNE a b o)).pc = if (t.getReg a != t.getReg b) = true then t.pc + signExtend13 o else t.pc + 4 := by
  simp only [execInstrBr]; split <;> rfl

theorem bne_reg (t : MachineState) (a b : Reg) (o : BitVec 13) (r : Reg) :
    (execInstrBr t (.BNE a b o)).getReg r = t.getReg r := by
  simp only [execInstrBr]; split <;> rfl

theorem op_pc_next (k : Nat) : opPC k + 4 = opPC (k + 1) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 by rfl, ← BitVec.ofNat_add]
  show BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  congr 1

/-- A straight-line block of one-cycle ALU instructions (no memory access) at words `start ..`. -/
theorem alu_run (s : MachineState) (start : Nat) (ops : List Instr) (fuel : Nat) (coins : Bool)
    (pc : s.pc = opPC start) (fits : start + ops.length ≤ 1505)
    (code : ∀ j (h : j < ops.length), (openingImage.code[start + j]?).bind decodeInstruction = some (.base ops[j]))
    (plain : ∀ j (h : j + 1 < ops.length) (t : MachineState), (execInstrBr t ops[j]).pc = t.pc + 4)
    (alu : ∀ j (h : j < ops.length) (t : MachineState), ordinaryStep t (.base ops[j]) = some (execInstrBr t ops[j]))
    (unit : ∀ j (h : j < ops.length), instructionCycles (.base ops[j]) = 1) :
    execute openingImage (ops.length + fuel) s coins =
      (do let r ← execute openingImage fuel (runOps s ops) coins; return r.charge ops.length 0) := by
  have pcs : ∀ j, j < ops.length → (runOps s (ops.take j)).pc = opPC (start + j) := by
    intro j
    induction j with
    | zero => intro _; simpa [runOps] using pc
    | succ j ih =>
      intro h
      rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some, run_ops_append]
      change (execInstrBr (runOps s (ops.take j)) ops[j]).pc = _
      rw [plain j h, ih (by omega), op_pc_next, Nat.add_assoc]
  have final : runOps s ops = runOps s (ops.take ops.length) := by rw [List.take_length]
  rw [final]
  apply CommitGolfCandidate.execute_unit_steps (states := fun j => runOps s (ops.take j))
  intro j h
  refine ⟨.base ops[j], pre_fetch _ (start + j) _ (by omega) (pcs j h) (code j h), ?_, unit j h⟩
  rw [List.take_succ, List.getElem?_eq_getElem h, Option.toList_some, run_ops_append]
  exact alu j h _

/-- `ld t6,la(rs) ; sd t6,sb(rd)` at words `k, k+1`: two steps. -/
theorem ld_sd_run (t : MachineState) (k : Nat) (rs rd : Reg) (load store : BitVec 12) (a b la sb : Nat)
    (pc : t.pc = opPC k) (hk : k + 2 ≤ 1505)
    (dl : (openingImage.code[k]?).bind decodeInstruction = some (.base (.LD .x31 rs load)))
    (ds : (openingImage.code[k + 1]?).bind decodeInstruction = some (.base (.SD rd .x31 store)))
    (hrd : rd ≠ .x31) (ra : t.getReg rs = wordAddress a) (rb : t.getReg rd = wordAddress b)
    (lv : signExtend12 load = BitVec.ofNat 64 (8 * la)) (sv : signExtend12 store = BitVec.ofNat 64 (8 * sb))
    (ba : a + la < 2 ^ 33) (bb : b + sb < 2 ^ 33) (fuel : Nat) (coins : Bool) :
    execute openingImage (2 + fuel) t coins =
      (do let r ← execute openingImage fuel (execInstrBr (execInstrBr t (.LD .x31 rs load)) (.SD rd .x31 store)) coins
          return r.charge 2 0) := by
  let l := execInstrBr t (.LD .x31 rs load)
  have lb : l.getReg rd = wordAddress b := (ld_other _ _ _ _ _ hrd).trans rb
  have lpc : l.pc = opPC (k + 1) := by rw [ld_pc, pc, op_pc_next]
  rw [show 2 + fuel = 1 + (1 + fuel) by omega,
    ordinary_one _ l (.LD .x31 rs load) _ _ (pre_fetch _ k _ (by omega) pc dl)
      (ld_step _ _ _ _ (by rw [ra]; exact word_valid a la load lv ba)) rfl,
    ordinary_one _ _ (.SD rd .x31 store) _ _ (pre_fetch _ (k + 1) _ (by omega) lpc ds)
      (sd_step _ _ _ _ (by rw [lb]; exact word_valid b sb store sv bb)) rfl]
  simp [Execution.charge]
  congr 1
  funext r
  congr 1 <;> omega

/-! ### Pass 1: one position -/

def p1OpsA7 : List Instr := [.SLLI .x7 .x6 3, .SLLI .x28 .x6 6, .ADD .x7 .x7 .x28,
  .SLLI .x28 .x6 7, .ADD .x7 .x7 .x28, .ADD .x7 .x15 .x7, .ADDI .x10 .x7 0]
def p1OpsB : List Instr := [.ANDI .x29 .x6 1, .ADDI .x29 .x29 4095, .ANDI .x28 .x29 184, .ADD .x28 .x12 .x28]
def p1OpsD : List Instr := [.ANDI .x29 .x29 232, .ADD .x7 .x7 .x29, .ADDI .x7 .x7 4064]
def p1OpsF3 : List Instr := [.ADDI .x17 .x17 48, .ADDI .x14 .x14 8, .ADDI .x16 .x16 4095]
def p1OpsF : List Instr := p1OpsF3 ++ [.BNE .x16 .x0 8068]

/-- The salt's word offset in an inverted input, and the mate digest's reply word. -/
def saltOff (i : Nat) : Nat := if i % 2 = 0 then 23 else 0
def mateWord (i : Nat) : Nat := Rw + 25 * i + (if i % 2 = 0 then 29 else 0) - 4

def p1A (s : MachineState) : MachineState := runOps (execInstrBr s (.LD .x6 .x14 0)) p1OpsA7

def p1W (s : MachineState) (y : Sampling.Block) : MachineState := writeBits (p1A s) (wordAddress scratchW) y

def copyPair (t : MachineState) (rs rd : Reg) (load store : BitVec 12) : MachineState :=
  execInstrBr (execInstrBr t (.LD .x31 rs load)) (.SD rd .x31 store)

/-- The salt copy (words 1457..1460) and the digest copy (words 1464..1471). -/
def saltCopy (t : MachineState) : MachineState := copyPair (copyPair t .x28 .x17 0 0) .x28 .x17 8 8

def digestCopy (t : MachineState) : MachineState :=
  copyPair (copyPair (copyPair (copyPair t .x7 .x17 0 16) .x7 .x17 8 24) .x7 .x17 16 32) .x7 .x17 24 40

/-- The state after one pass-1 position, given the inverse call's answer `y`. -/
def p1Next (s : MachineState) (y : Sampling.Block) : MachineState :=
  runOps (digestCopy (runOps (saltCopy (runOps (p1W s y) p1OpsB)) p1OpsD)) p1OpsF

structure P1Ready (s : MachineState) (k i card : Nat) : Prop where
  pc : s.pc = opPC 1444
  idx : s.getReg .x14 = wordAddress (IW + k)
  idxVal : memoryView s (IW + k) = BitVec.ofNat 64 i
  reply : s.getReg .x15 = wordAddress Rw
  list : s.getReg .x17 = wordAddress (Lw k)
  left : s.getReg .x16 = BitVec.ofNat 64 (card - k)
  size : s.getReg .x11 = 200
  out : s.getReg .x12 = wordAddress scratchW
  prim : s.getReg .x13 = 2
  sel : s.getReg .x5 = 0
  small : i < LENGTH
  present : k < card
  cardBound : card ≤ LENGTH

theorem p1a_facts (s : MachineState) (k i card : Nat) (r : P1Ready s k i card) :
    (p1A s).getReg .x6 = BitVec.ofNat 64 i ∧ (p1A s).getReg .x10 = wordAddress (Rw + 25 * i) ∧
    (p1A s).getReg .x7 = wordAddress (Rw + 25 * i) ∧ (p1A s).mem = s.mem ∧ (p1A s).pc = opPC 1452 ∧
    ∀ g, g ≠ .x6 → g ≠ .x7 → g ≠ .x28 → g ≠ .x10 → (p1A s).getReg g = s.getReg g := by
  have hi := r.small
  have len : LENGTH = 2 ^ 24 := rfl
  have v6 : s.getMem (s.getReg .x14 + signExtend12 0) = BitVec.ofNat 64 i := by
    rw [r.idx, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]; exact r.idxVal
  have e6 : (p1A s).getReg .x6 = s.getMem (s.getReg .x14 + signExtend12 0) := rfl
  have e7 : (p1A s).getReg .x7 = s.getReg .x15 +
      ((s.getMem (s.getReg .x14 + signExtend12 0) <<< (3 : BitVec 6).toNat +
        s.getMem (s.getReg .x14 + signExtend12 0) <<< (6 : BitVec 6).toNat) +
        s.getMem (s.getReg .x14 + signExtend12 0) <<< (7 : BitVec 6).toNat) := rfl
  have e10 : (p1A s).getReg .x10 = (p1A s).getReg .x7 + signExtend12 0 := rfl
  have v7 : (p1A s).getReg .x7 = wordAddress (Rw + 25 * i) := by
    rw [e7, v6, times200 i (by omega), r.reply, show 200 * i = 8 * (25 * i) by ring, address_up]
  refine ⟨e6.trans v6, ?_, v7, ?_, ?_, ?_⟩
  · rw [e10, v7, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]
  · simp only [p1A, p1OpsA7, runOps, List.foldl, execInstrBr, set_mem]
  · rw [show (p1A s).pc = s.pc + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl, r.pc]; rfl
  · intro g a b c d
    simp [p1A, p1OpsA7, runOps, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

theorem p1w_facts (s : MachineState) (k i card : Nat) (r : P1Ready s k i card) (y : Sampling.Block) :
    (∀ g, (p1W s y).getReg g = (p1A s).getReg g) ∧ (p1W s y).pc = opPC 1453 ∧
    ∀ w < 2 ^ 33, memoryView (p1W s y) w = writeWindow (memoryView s) scratchW (replyWords y) w := by
  obtain ⟨_, _, _, mem, pc, _⟩ := p1a_facts s k i card r
  refine ⟨fun g => by unfold p1W; exact CommitGolfCandidate.writeBits_register _ _ _ _, ?_, fun w hw => ?_⟩
  · rw [p1W, written_pc', pc]; rfl
  · rw [p1W]
    have h := permutation_write_memory (p1A s) scratchW w y (by unfold scratchW; omega) hw
    rw [memoryView_congr mem] at h
    exact h

theorem p1w_eq (s : MachineState) (y : Sampling.Block) : writeBits (p1A s) (wordAddress scratchW) y = p1W s y := rfl

attribute [local irreducible] p1W

/-! ### Memory views below `2^33` (all buffers live there) -/

def bview (X : MachineState) : Memory := fun w => if w < 2 ^ 33 then memoryView X w else 0

theorem copy_pair_view (t : MachineState) (rs rd : Reg) (hrs : rs ≠ .x31) (hrd : rd ≠ .x31)
    (a b la sb : Nat) (ra : t.getReg rs = wordAddress a) (rb : t.getReg rd = wordAddress b)
    (load store : BitVec 12) (lv : signExtend12 load = BitVec.ofNat 64 (8 * la))
    (sv : signExtend12 store = BitVec.ofNat 64 (8 * sb)) (ba : a + la < 2 ^ 33) (bb : b + sb < 2 ^ 33) :
    bview (copyPair t rs rd load store) = writeWord (bview t) (b + sb) (bview t (a + la)) ∧
      (copyPair t rs rd load store).pc = t.pc + 4 + 4 ∧
      (∀ g, g ≠ .x31 → (copyPair t rs rd load store).getReg g = t.getReg g) := by
  obtain ⟨mem, pc, regs⟩ := ld_sd_pair t rs rd hrs hrd a b la sb ra rb load store lv sv (by omega)
  refine ⟨?_, pc, regs⟩
  funext w
  unfold copyPair
  simp only [bview, writeWord]
  by_cases hw : w < 2 ^ 33
  · simp only [hw, ba, ↓reduceIte]
    rw [mem w (by omega)]
    rfl
  · simp only [hw, ↓reduceIte]
    rw [if_neg (by omega)]

theorem bview_congr {X Y : MachineState} (h : X.mem = Y.mem) : bview X = bview Y := by
  unfold bview
  rw [memoryView_congr h]

theorem bne_mem (t : MachineState) (a b : Reg) (o : BitVec 13) : (execInstrBr t (.BNE a b o)).mem = t.mem := by
  simp only [execInstrBr]
  split <;> rfl

/-! ### Pass 1: the stages after the call, on abstract states (never unfold a written state) -/

theorem stage_b (W : MachineState) (i : Nat) (hi : i < 2 ^ 63) (x6 : W.getReg .x6 = BitVec.ofNat 64 i)
    (x12 : W.getReg .x12 = wordAddress scratchW) :
    (runOps W p1OpsB).getReg .x29 = (if i % 2 = 0 then (-1 : Word) else 0) ∧
    (runOps W p1OpsB).getReg .x28 = wordAddress (scratchW + saltOff i) ∧
    (runOps W p1OpsB).mem = W.mem ∧ (runOps W p1OpsB).pc = W.pc + 4 + 4 + 4 + 4 ∧
    ∀ g, g ≠ .x28 → g ≠ .x29 → (runOps W p1OpsB).getReg g = W.getReg g := by
  have e29 : (runOps W p1OpsB).getReg .x29 = (W.getReg .x6 &&& signExtend12 1) + signExtend12 4095 := by
    simp only [runOps, p1OpsB, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
    reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
  have v29 : (W.getReg .x6 &&& signExtend12 1) + signExtend12 4095 = if i % 2 = 0 then (-1 : Word) else 0 := by
    rw [x6]; exact parity_mask i hi
  have m29 : (runOps W p1OpsB).getReg .x29 = if i % 2 = 0 then (-1 : Word) else 0 := e29.trans v29
  have e28 : (runOps W p1OpsB).getReg .x28 =
      W.getReg .x12 + (((W.getReg .x6 &&& signExtend12 1) + signExtend12 4095) &&& signExtend12 184) := by
    simp only [runOps, p1OpsB, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
    reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
  refine ⟨m29, ?_, ?_, rfl, ?_⟩
  · rw [e28, mask_and _ 184 184 (by decide) i v29, x12,
      show (if i % 2 = 0 then 184 else 0) = (if i % 2 = 0 then 8 * 23 else 0) by rfl, address_if]
    rfl
  · simp only [runOps, p1OpsB, List.foldl, execInstrBr, set_mem]
  · intro g a b
    simp [p1OpsB, runOps, execInstrBr, Ne.symm a, Ne.symm b]

theorem stage_d (C : MachineState) (i : Nat) (x29 : C.getReg .x29 = if i % 2 = 0 then (-1 : Word) else 0)
    (x7 : C.getReg .x7 = wordAddress (Rw + 25 * i)) :
    (runOps C p1OpsD).getReg .x7 = wordAddress (mateWord i) ∧
    (runOps C p1OpsD).mem = C.mem ∧ (runOps C p1OpsD).pc = C.pc + 4 + 4 + 4 ∧
    ∀ g, g ≠ .x7 → g ≠ .x29 → (runOps C p1OpsD).getReg g = C.getReg g := by
  have e7 : (runOps C p1OpsD).getReg .x7 = (C.getReg .x7 + (C.getReg .x29 &&& signExtend12 232)) + signExtend12 4064 := by
    simp only [runOps, p1OpsD, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
    reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
  have d29 : C.getReg .x29 &&& signExtend12 232 = BitVec.ofNat 64 (if i % 2 = 0 then 232 else 0) :=
    mask_and _ 232 232 (by decide) i x29
  have rwv : Rw = 603980313 := rfl
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [e7, d29, x7, show (if i % 2 = 0 then 232 else 0) = (if i % 2 = 0 then 8 * 29 else 0) by rfl, address_if,
      address_down _ 4 4064 (by decide) (by split <;> omega) (by decide)]
    rfl
  · simp only [runOps, p1OpsD, List.foldl, execInstrBr, set_mem]
  · intro g a b
    simp [p1OpsD, runOps, execInstrBr, Ne.symm a, Ne.symm b]

theorem stage_f (E : MachineState) (k card : Nat) (hk : k < card) (hc : card ≤ 2 ^ 24)
    (x14 : E.getReg .x14 = wordAddress (IW + k)) (x16 : E.getReg .x16 = BitVec.ofNat 64 (card - k))
    (x17 : E.getReg .x17 = wordAddress (Lw k)) (pc : E.pc = opPC 1472) :
    (runOps E p1OpsF).getReg .x14 = wordAddress (IW + (k + 1)) ∧
    (runOps E p1OpsF).getReg .x16 = BitVec.ofNat 64 (card - (k + 1)) ∧
    (runOps E p1OpsF).getReg .x17 = wordAddress (Lw (k + 1)) ∧
    (runOps E p1OpsF).mem = E.mem ∧
    (runOps E p1OpsF).pc = (if k + 1 = card then opPC 1476 else opPC 1444) ∧
    ∀ g, g ≠ .x14 → g ≠ .x16 → g ≠ .x17 → (runOps E p1OpsF).getReg g = E.getReg g := by
  have split3 : runOps E p1OpsF = execInstrBr (runOps E p1OpsF3) (.BNE .x16 .x0 8068) := by
    rw [p1OpsF, run_ops_append, run_ops_singleton]
  let F3 := runOps E p1OpsF3
  have f16 : F3.getReg .x16 = BitVec.ofNat 64 (card - (k + 1)) := by
    have e : F3.getReg .x16 = E.getReg .x16 + signExtend12 4095 := by
      simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
        reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e, x16, show signExtend12 (4095 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 1) by decide, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [show card - k + (2 ^ 64 - 1) = (card - (k + 1)) + 2 ^ 64 by omega, Nat.add_mod_right]
  have f14 : F3.getReg .x14 = wordAddress (IW + (k + 1)) := by
    have e : F3.getReg .x14 = E.getReg .x14 + signExtend12 8 := by
      simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
        reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e, x14, show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 (8 * 1) by decide, address_up, Nat.add_assoc]
  have f17 : F3.getReg .x17 = wordAddress (Lw (k + 1)) := by
    have e : F3.getReg .x17 = E.getReg .x17 + signExtend12 48 := by
      simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
        reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e, x17, show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 (8 * 6) by decide, address_up]
    unfold Lw; congr 1
  have fpc : F3.pc = opPC 1475 := by
    change E.pc + 4 + 4 + 4 = _
    rw [pc]; rfl
  have fmem : F3.mem = E.mem := by simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, set_mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [split3, bne_reg]; exact f14
  · rw [split3, bne_reg]; exact f16
  · rw [split3, bne_reg]; exact f17
  · rw [split3, bne_mem]; exact fmem
  · rw [split3, bne_pc]
    have zero : (runOps E p1OpsF3).getReg .x0 = 0 := rfl
    rw [f16, zero, fpc]
    by_cases last : k + 1 = card
    · rw [if_pos last, show card - (k + 1) = 0 by omega, if_neg (by decide)]
      decide
    · have nz : (BitVec.ofNat 64 (card - (k + 1)) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        simp at this
        omega
      rw [if_neg last, if_pos nz]
      decide
  · intro g a b c
    rw [split3, bne_reg]
    simp [F3, runOps, p1OpsF3, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

/-- The six words a pass-1 position writes to its list entry, on top of the inverted input at 2048. -/
def p1Mem (M : Memory) (y : Sampling.Block) (k i : Nat) : Memory :=
  let W := writeWindow M scratchW (replyWords y)
  writeWord (writeWord (writeWord (writeWord (writeWord (writeWord W
    (Lw k) (W (scratchW + saltOff i))) (Lw k + 1) (W (scratchW + saltOff i + 1)))
    (Lw k + 2) (W (mateWord i))) (Lw k + 3) (W (mateWord i + 1)))
    (Lw k + 4) (W (mateWord i + 2))) (Lw k + 5) (W (mateWord i + 3))

theorem salt_off_small (i : Nat) : saltOff i ≤ 23 := by unfold saltOff; split <;> omega

theorem mate_word_bounds (i : Nat) (hi : i < 2 ^ 24) : Rw + 25 * i - 4 ≤ mateWord i ∧ mateWord i ≤ Rw + 25 * i + 25 := by
  unfold mateWord; split <;> omega

theorem p1_next_facts (s : MachineState) (k i card : Nat) (r : P1Ready s k i card) (y : Sampling.Block) :
    (∀ w < 2 ^ 33, memoryView (p1Next s y) w = p1Mem (memoryView s) y k i w) ∧
    (p1Next s y).getReg .x14 = wordAddress (IW + (k + 1)) ∧
    (p1Next s y).getReg .x17 = wordAddress (Lw (k + 1)) ∧
    (p1Next s y).getReg .x16 = BitVec.ofNat 64 (card - (k + 1)) ∧
    (p1Next s y).pc = (if k + 1 = card then opPC 1476 else opPC 1444) ∧
    (∀ g, g ≠ .x6 → g ≠ .x7 → g ≠ .x10 → g ≠ .x14 → g ≠ .x16 → g ≠ .x17 → g ≠ .x28 → g ≠ .x29 → g ≠ .x31 →
      (p1Next s y).getReg g = s.getReg g) := by
  have hi := r.small
  have hk := r.present
  have hc := r.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  obtain ⟨a6, _, a7, _, _, akeep⟩ := p1a_facts s k i card r
  obtain ⟨wreg, wpc, wmem⟩ := p1w_facts s k i card r y
  have so := salt_off_small i
  have mb := mate_word_bounds i (by omega)
  have lwk : Lw k + 6 ≤ 2 ^ 27 + 6 * 2 ^ 24 := by unfold Lw; omega
  have rwv : Rw = 603980313 := rfl
  let W := p1W s y
  have keepW (g : Reg) (h6 : g ≠ .x6) (h7 : g ≠ .x7) (h28 : g ≠ .x28) (h10 : g ≠ .x10) : W.getReg g = s.getReg g :=
    (wreg g).trans (akeep g h6 h7 h28 h10)
  obtain ⟨b29, b28, bmem, bpc, bkeep⟩ := stage_b W i (by omega) ((wreg .x6).trans a6)
    ((keepW .x12 (by decide) (by decide) (by decide) (by decide)).trans r.out)
  let B := runOps W p1OpsB
  have b17 : B.getReg .x17 = wordAddress (Lw k) :=
    (bkeep .x17 (by decide) (by decide)).trans ((keepW .x17 (by decide) (by decide) (by decide) (by decide)).trans r.list)
  obtain ⟨c1, c1pc, c1keep⟩ := copy_pair_view B .x28 .x17 (by decide) (by decide)
    (scratchW + saltOff i) (Lw k) 0 0 b28 b17 0 0 (by decide) (by decide) (by unfold scratchW; omega) (by omega)
  let C1 := copyPair B .x28 .x17 0 0
  obtain ⟨c2, c2pc, c2keep⟩ := copy_pair_view C1 .x28 .x17 (by decide) (by decide)
    (scratchW + saltOff i) (Lw k) 1 1 ((c1keep .x28 (by decide)).trans b28) ((c1keep .x17 (by decide)).trans b17)
    8 8 (by decide) (by decide) (by unfold scratchW; omega) (by omega)
  let C := copyPair C1 .x28 .x17 8 8
  have ckeep (g : Reg) (h : g ≠ .x31) : C.getReg g = B.getReg g := (c2keep g h).trans (c1keep g h)
  obtain ⟨d7, dmem, dpc, dkeep⟩ := stage_d C i ((ckeep .x29 (by decide)).trans b29)
    ((ckeep .x7 (by decide)).trans ((bkeep .x7 (by decide) (by decide)).trans ((wreg .x7).trans a7)))
  let D := runOps C p1OpsD
  have d17 : D.getReg .x17 = wordAddress (Lw k) :=
    (dkeep .x17 (by decide) (by decide)).trans ((ckeep .x17 (by decide)).trans b17)
  obtain ⟨e1, e1pc, e1keep⟩ := copy_pair_view D .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 0 2 d7 d17 0 16 (by decide) (by decide) (by omega) (by omega)
  let E1 := copyPair D .x7 .x17 0 16
  obtain ⟨e2, e2pc, e2keep⟩ := copy_pair_view E1 .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 1 3 ((e1keep .x7 (by decide)).trans d7) ((e1keep .x17 (by decide)).trans d17)
    8 24 (by decide) (by decide) (by omega) (by omega)
  let E2 := copyPair E1 .x7 .x17 8 24
  obtain ⟨e3, e3pc, e3keep⟩ := copy_pair_view E2 .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 2 4 ((e2keep .x7 (by decide)).trans ((e1keep .x7 (by decide)).trans d7))
    ((e2keep .x17 (by decide)).trans ((e1keep .x17 (by decide)).trans d17))
    16 32 (by decide) (by decide) (by omega) (by omega)
  let E3 := copyPair E2 .x7 .x17 16 32
  obtain ⟨e4, e4pc, e4keep⟩ := copy_pair_view E3 .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 3 5 ((e3keep .x7 (by decide)).trans ((e2keep .x7 (by decide)).trans
      ((e1keep .x7 (by decide)).trans d7)))
    ((e3keep .x17 (by decide)).trans ((e2keep .x17 (by decide)).trans ((e1keep .x17 (by decide)).trans d17)))
    24 40 (by decide) (by decide) (by omega) (by omega)
  let E := copyPair E3 .x7 .x17 24 40
  have ekeep (g : Reg) (h : g ≠ .x31) : E.getReg g = D.getReg g :=
    (e4keep g h).trans ((e3keep g h).trans ((e2keep g h).trans (e1keep g h)))
  have toW (g : Reg) (h7 : g ≠ .x7) (h29 : g ≠ .x29) (h31 : g ≠ .x31) (h28 : g ≠ .x28) :
      E.getReg g = W.getReg g :=
    (ekeep g h31).trans ((dkeep g h7 h29).trans ((ckeep g h31).trans (bkeep g h28 h29)))
  have epc : E.pc = opPC 1472 := by
    rw [e4pc, e3pc, e2pc, e1pc, dpc, c2pc, c1pc, bpc, wpc]; rfl
  obtain ⟨f14, f16, f17, fmem, fpc, fkeep⟩ := stage_f E k card hk (by omega)
    ((toW .x14 (by decide) (by decide) (by decide) (by decide)).trans
      ((keepW .x14 (by decide) (by decide) (by decide) (by decide)).trans r.idx))
    ((toW .x16 (by decide) (by decide) (by decide) (by decide)).trans
      ((keepW .x16 (by decide) (by decide) (by decide) (by decide)).trans r.left))
    ((ekeep .x17 (by decide)).trans d17) epc
  have nextIs : p1Next s y = runOps E p1OpsF := rfl
  rw [nextIs]
  refine ⟨?_, f14, f17, f16, fpc, ?_⟩
  · intro w hw
    have view : memoryView (runOps E p1OpsF) w = bview (runOps E p1OpsF) w := by simp only [bview, hw, ↓reduceIte]
    have bW : bview B = fun w => if w < 2 ^ 33 then writeWindow (memoryView s) scratchW (replyWords y) w else 0 := by
      rw [bview_congr bmem]; funext v; unfold bview; split
      · exact wmem v (by assumption)
      · rfl
    have chain : bview (runOps E p1OpsF) = bview E := bview_congr fmem
    have dview : bview D = bview C := bview_congr dmem
    rw [view, chain, e4, e3, e2, e1, dview, c2, c1, bW]
    simp only [writeWord, p1Mem, hw, ↓reduceIte]
    have l0 : scratchW + saltOff i + 0 < 2 ^ 33 := by unfold scratchW; omega
    have l1 : scratchW + saltOff i + 1 < 2 ^ 33 := by unfold scratchW; omega
    have m0 : mateWord i + 0 < 2 ^ 33 := by omega
    have m1 : mateWord i + 1 < 2 ^ 33 := by omega
    have m2 : mateWord i + 2 < 2 ^ 33 := by omega
    have m3 : mateWord i + 3 < 2 ^ 33 := by omega
    have l0' : scratchW + saltOff i < 2 ^ 33 := by unfold scratchW; omega
    simp only [l0, l0', l1, m0, m1, m2, m3, ↓reduceIte, Nat.add_zero]
    have n1 : ¬ (scratchW + saltOff i + 1 = Lw k) := by unfold scratchW Lw; omega
    have q0 : ¬ (mateWord i = Lw k) := by unfold Lw; omega
    have q0' : ¬ (mateWord i = Lw k + 1) := by unfold Lw; omega
    have q1 : ∀ t < 4, ¬ (mateWord i + 1 = Lw k + t) := by intro t _; unfold Lw; omega
    have q2 : ∀ t < 4, ¬ (mateWord i + 2 = Lw k + t) := by intro t _; unfold Lw; omega
    have q3 : ∀ t < 5, ¬ (mateWord i + 3 = Lw k + t) := by intro t _; unfold Lw; omega
    simp only [n1, q0, q0', q1 0 (by decide), q1 1 (by decide), q1 2 (by decide), q1 3 (by decide),
      q2 0 (by decide), q2 1 (by decide), q2 2 (by decide), q2 3 (by decide), q3 0 (by decide), q3 1 (by decide),
      q3 2 (by decide), q3 3 (by decide), q3 4 (by decide), Nat.add_zero, ↓reduceIte]
    have z1 : ¬ (mateWord i + 1 = Lw k) := by unfold Lw; omega
    have z2 : ¬ (mateWord i + 2 = Lw k) := by unfold Lw; omega
    have z3 : ¬ (mateWord i + 3 = Lw k) := by unfold Lw; omega
    have m0' : mateWord i < 2 ^ 33 := by omega
    simp only [z1, z2, z3, m0', ↓reduceIte]
  · intro g h6 h7 h10 h14 h16 h17 h28 h29 h31
    rw [fkeep g h14 h16 h17, toW g h7 h29 h31 h28, keepW g h6 h7 h28 h10]

/-- The run of one pass-1 position. -/
theorem execute_p1 (s : MachineState) (k i card : Nat) (r : P1Ready s k i card) (fuel : Nat) (coins : Bool) :
    execute openingImage (32 + fuel) s coins =
      (do let y ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView s) (Rw + 25 * i))))))
          let res ← execute openingImage fuel (p1Next s y) coins
          return res.charge 61 1) := by
  have hi := r.small
  have hk := r.present
  have hc := r.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have rwv : Rw = 603980313 := rfl
  have iwv : IW = 1023411204 := rfl
  obtain ⟨a6, a10, a7, amem, apc, akeep⟩ := p1a_facts s k i card r
  -- word 1444: the index load
  let L := execInstrBr s (.LD .x6 .x14 0)
  have lpc : L.pc = opPC 1445 := by rw [ld_pc, r.pc, op_pc_next]
  have runL : ∀ X, execute openingImage (1 + X) s coins =
      (do let res ← execute openingImage X L coins; return res.charge 1 0) := fun X =>
    ordinary_one _ L (.LD .x6 .x14 0) _ _ (pre_fetch _ 1444 _ (by decide) r.pc rfl)
      (ld_step _ _ _ _ (by rw [r.idx]; exact word_valid (IW + k) 0 0 (by decide) (by omega))) rfl
  have runA : ∀ X, execute openingImage (7 + X) L coins =
      (do let res ← execute openingImage X (p1A s) coins; return res.charge 7 0) := fun X =>
    alu_run L 1445 p1OpsA7 X coins lpc (by decide)
      (by intro j h; change j < 7 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 6 := (by change j + 1 < 7 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 7 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 7 at h; interval_cases j <;> rfl)
  -- word 1452: the inverse call
  have call := execute_inverse_call openingImage (23 + fuel) (p1A s) coins (Rw + 25 * i) scratchW
    (by omega) (by unfold scratchW; omega) a10
    ((akeep .x12 (by decide) (by decide) (by decide) (by decide)).trans r.out)
    ((akeep .x5 (by decide) (by decide) (by decide) (by decide)).trans r.sel)
    ((akeep .x11 (by decide) (by decide) (by decide) (by decide)).trans r.size)
    ((akeep .x13 (by decide) (by decide) (by decide) (by decide)).trans r.prim)
    (pre_fetch _ 1452 _ (by decide) apc rfl)
  rw [show 32 + fuel = 1 + (7 + ((23 + fuel) + 1)) by omega, runL, runA, call, memoryView_congr amem]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext y
  rw [p1w_eq]
  -- words 1453..1475 after the call
  have so := salt_off_small i
  have mb := mate_word_bounds i (by omega)
  have lwk : Lw k + 6 ≤ 2 ^ 27 + 6 * 2 ^ 24 := by unfold Lw; omega
  obtain ⟨wreg, wpc, _⟩ := p1w_facts s k i card r y
  let W := p1W s y
  have keepW (g : Reg) (h6 : g ≠ .x6) (h7 : g ≠ .x7) (h28 : g ≠ .x28) (h10 : g ≠ .x10) : W.getReg g = s.getReg g :=
    (wreg g).trans (akeep g h6 h7 h28 h10)
  obtain ⟨b29, b28, _, bpc, bkeep⟩ := stage_b W i (by omega) ((wreg .x6).trans a6)
    ((keepW .x12 (by decide) (by decide) (by decide) (by decide)).trans r.out)
  let B := runOps W p1OpsB
  have bpc' : B.pc = opPC 1457 := by rw [bpc, wpc]; decide
  have runB : ∀ X, execute openingImage (4 + X) W coins =
      (do let res ← execute openingImage X B coins; return res.charge 4 0) := fun X =>
    alu_run W 1453 p1OpsB X coins wpc (by decide)
      (by intro j h; change j < 4 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 3 := (by change j + 1 < 4 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 4 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 4 at h; interval_cases j <;> rfl)
  have b17 : B.getReg .x17 = wordAddress (Lw k) :=
    (bkeep .x17 (by decide) (by decide)).trans ((keepW .x17 (by decide) (by decide) (by decide) (by decide)).trans r.list)
  have runC1 : ∀ X, execute openingImage (2 + X) B coins =
      (do let res ← execute openingImage X (copyPair B .x28 .x17 0 0) coins; return res.charge 2 0) := fun X =>
    ld_sd_run B 1457 .x28 .x17 0 0 (scratchW + saltOff i) (Lw k) 0 0 bpc' (by decide) rfl rfl (by decide) b28 b17
      (by decide) (by decide) (by unfold scratchW; omega) (by omega) X coins
  obtain ⟨_, c1pc, c1keep⟩ := copy_pair_view B .x28 .x17 (by decide) (by decide)
    (scratchW + saltOff i) (Lw k) 0 0 b28 b17 0 0 (by decide) (by decide) (by unfold scratchW; omega) (by omega)
  let C1 := copyPair B .x28 .x17 0 0
  have c1pc' : C1.pc = opPC 1459 := by rw [c1pc, bpc']; decide
  have runC2 : ∀ X, execute openingImage (2 + X) C1 coins =
      (do let res ← execute openingImage X (copyPair C1 .x28 .x17 8 8) coins; return res.charge 2 0) := fun X =>
    ld_sd_run C1 1459 .x28 .x17 8 8 (scratchW + saltOff i) (Lw k) 1 1 c1pc' (by decide) rfl rfl (by decide)
      ((c1keep .x28 (by decide)).trans b28) ((c1keep .x17 (by decide)).trans b17)
      (by decide) (by decide) (by unfold scratchW; omega) (by omega) X coins
  obtain ⟨_, c2pc, c2keep⟩ := copy_pair_view C1 .x28 .x17 (by decide) (by decide)
    (scratchW + saltOff i) (Lw k) 1 1 ((c1keep .x28 (by decide)).trans b28) ((c1keep .x17 (by decide)).trans b17)
    8 8 (by decide) (by decide) (by unfold scratchW; omega) (by omega)
  let C := copyPair C1 .x28 .x17 8 8
  have cpc : C.pc = opPC 1461 := by rw [c2pc, c1pc']; decide
  have ckeep (g : Reg) (h : g ≠ .x31) : C.getReg g = B.getReg g := (c2keep g h).trans (c1keep g h)
  obtain ⟨d7, _, dpc, dkeep⟩ := stage_d C i ((ckeep .x29 (by decide)).trans b29)
    ((ckeep .x7 (by decide)).trans ((bkeep .x7 (by decide) (by decide)).trans ((wreg .x7).trans a7)))
  let D := runOps C p1OpsD
  have dpc' : D.pc = opPC 1464 := by rw [dpc, cpc]; decide
  have runD : ∀ X, execute openingImage (3 + X) C coins =
      (do let res ← execute openingImage X D coins; return res.charge 3 0) := fun X =>
    alu_run C 1461 p1OpsD X coins cpc (by decide)
      (by intro j h; change j < 3 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 2 := (by change j + 1 < 3 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 3 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 3 at h; interval_cases j <;> rfl)
  have d17 : D.getReg .x17 = wordAddress (Lw k) :=
    (dkeep .x17 (by decide) (by decide)).trans ((ckeep .x17 (by decide)).trans b17)
  have runE1 : ∀ X, execute openingImage (2 + X) D coins =
      (do let res ← execute openingImage X (copyPair D .x7 .x17 0 16) coins; return res.charge 2 0) := fun X =>
    ld_sd_run D 1464 .x7 .x17 0 16 (mateWord i) (Lw k) 0 2 dpc' (by decide) rfl rfl (by decide) d7 d17
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e1pc, e1keep⟩ := copy_pair_view D .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 0 2 d7 d17 0 16 (by decide) (by decide) (by omega) (by omega)
  let E1 := copyPair D .x7 .x17 0 16
  have e1pc' : E1.pc = opPC 1466 := by rw [e1pc, dpc']; decide
  have e1_7 : E1.getReg .x7 = wordAddress (mateWord i) := (e1keep .x7 (by decide)).trans d7
  have e1_17 : E1.getReg .x17 = wordAddress (Lw k) := (e1keep .x17 (by decide)).trans d17
  have runE2 : ∀ X, execute openingImage (2 + X) E1 coins =
      (do let res ← execute openingImage X (copyPair E1 .x7 .x17 8 24) coins; return res.charge 2 0) := fun X =>
    ld_sd_run E1 1466 .x7 .x17 8 24 (mateWord i) (Lw k) 1 3 e1pc' (by decide) rfl rfl (by decide) e1_7 e1_17
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e2pc, e2keep⟩ := copy_pair_view E1 .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 1 3 e1_7 e1_17 8 24 (by decide) (by decide) (by omega) (by omega)
  let E2 := copyPair E1 .x7 .x17 8 24
  have e2pc' : E2.pc = opPC 1468 := by rw [e2pc, e1pc']; decide
  have e2_7 : E2.getReg .x7 = wordAddress (mateWord i) := (e2keep .x7 (by decide)).trans e1_7
  have e2_17 : E2.getReg .x17 = wordAddress (Lw k) := (e2keep .x17 (by decide)).trans e1_17
  have runE3 : ∀ X, execute openingImage (2 + X) E2 coins =
      (do let res ← execute openingImage X (copyPair E2 .x7 .x17 16 32) coins; return res.charge 2 0) := fun X =>
    ld_sd_run E2 1468 .x7 .x17 16 32 (mateWord i) (Lw k) 2 4 e2pc' (by decide) rfl rfl (by decide) e2_7 e2_17
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e3pc, e3keep⟩ := copy_pair_view E2 .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 2 4 e2_7 e2_17 16 32 (by decide) (by decide) (by omega) (by omega)
  let E3 := copyPair E2 .x7 .x17 16 32
  have e3pc' : E3.pc = opPC 1470 := by rw [e3pc, e2pc']; decide
  have e3_7 : E3.getReg .x7 = wordAddress (mateWord i) := (e3keep .x7 (by decide)).trans e2_7
  have e3_17 : E3.getReg .x17 = wordAddress (Lw k) := (e3keep .x17 (by decide)).trans e2_17
  have runE4 : ∀ X, execute openingImage (2 + X) E3 coins =
      (do let res ← execute openingImage X (copyPair E3 .x7 .x17 24 40) coins; return res.charge 2 0) := fun X =>
    ld_sd_run E3 1470 .x7 .x17 24 40 (mateWord i) (Lw k) 3 5 e3pc' (by decide) rfl rfl (by decide) e3_7 e3_17
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e4pc, _⟩ := copy_pair_view E3 .x7 .x17 (by decide) (by decide)
    (mateWord i) (Lw k) 3 5 e3_7 e3_17 24 40 (by decide) (by decide) (by omega) (by omega)
  let E := copyPair E3 .x7 .x17 24 40
  have epc : E.pc = opPC 1472 := by rw [e4pc, e3pc']; decide
  have runF : ∀ X, execute openingImage (4 + X) E coins =
      (do let res ← execute openingImage X (runOps E p1OpsF) coins; return res.charge 4 0) := fun X =>
    alu_run E 1472 p1OpsF X coins epc (by decide)
      (by intro j h; change j < 4 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 3 := (by change j + 1 < 4 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 4 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 4 at h; interval_cases j <;> rfl)
  have nextIs : p1Next s y = runOps E p1OpsF := rfl
  rw [show 23 + fuel = 4 + (2 + (2 + (3 + (2 + (2 + (2 + (2 + (4 + fuel)))))))) by omega,
    runB, runC1, runC2, runD, runE1, runE2, runE3, runE4, runF, nextIs]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

attribute [local irreducible] p1Next

/-! ### Pass 1: the loop -/

theorem window_out (M : Memory) (words : Words 25) (w : Nat) (h : w < scratchW ∨ scratchW + 25 ≤ w) :
    writeWindow M scratchW words w = M w := by
  unfold writeWindow
  rw [dif_neg (by omega)]

theorem window_in (M : Memory) (words : Words 25) (m : Nat) (h : m < 25) :
    writeWindow M scratchW words (scratchW + m) = words ⟨m, h⟩ := by
  unfold writeWindow
  rw [dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

theorem p1mem_other (M : Memory) (y : Sampling.Block) (k i w : Nat) (hw : w < Lw k ∨ Lw k + 6 ≤ w) :
    p1Mem M y k i w = writeWindow M scratchW (replyWords y) w := by
  simp only [p1Mem, writeWord]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- The list entry of a position: salt words of the inverted input, then the mate's four digest words. -/
def listVal (M0 : Memory) (y : Sampling.Block) (i t : Nat) : Word :=
  if h : t < 2 then replyWords y ⟨saltOff i + t, by have := salt_off_small i; omega⟩ else M0 (mateWord i + (t - 2))

theorem p1mem_entry (M : Memory) (y : Sampling.Block) (k i t : Nat) (ht : t < 6) (hi : i < 2 ^ 24) :
    p1Mem M y k i (Lw k + t) = listVal M y i t := by
  have so := salt_off_small i
  have mb := mate_word_bounds i hi
  have rwv : Rw = 603980313 := rfl
  have sw : scratchW = 2048 := rfl
  have w0 : writeWindow M scratchW (replyWords y) (scratchW + saltOff i) =
      replyWords y ⟨saltOff i + 0, by omega⟩ := window_in M (replyWords y) (saltOff i) (by omega)
  have w1 : writeWindow M scratchW (replyWords y) (scratchW + saltOff i + 1) =
      replyWords y ⟨saltOff i + 1, by omega⟩ := window_in M (replyWords y) (saltOff i + 1) (by omega)
  have mj (j : Nat) (hj : j < 4) : writeWindow M scratchW (replyWords y) (mateWord i + j) = M (mateWord i + j) :=
    window_out _ _ _ (by omega)
  have m0 : writeWindow M scratchW (replyWords y) (mateWord i) = M (mateWord i) := by
    simpa using mj 0 (by decide)
  interval_cases t <;> simp [p1Mem, writeWord, listVal]
  · exact w0
  · exact w1
  · exact m0
  · exact mj 1 (by decide)
  · exact mj 2 (by decide)
  · exact mj 3 (by decide)

structure P1Inv (S0 s : MachineState) (k card : Nat) (idx : Nat → Nat) (ys : Nat → Sampling.Block) : Prop where
  pc : s.pc = if k = card then opPC 1476 else opPC 1444
  idx14 : s.getReg .x14 = wordAddress (IW + k)
  reply : s.getReg .x15 = wordAddress Rw
  list : s.getReg .x17 = wordAddress (Lw k)
  left : s.getReg .x16 = BitVec.ofNat 64 (card - k)
  size : s.getReg .x11 = 200
  out : s.getReg .x12 = wordAddress scratchW
  prim : s.getReg .x13 = 2
  sel : s.getReg .x5 = 0
  keep : ∀ g, g ≠ .x5 → g ≠ .x6 → g ≠ .x7 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 → g ≠ .x13 → g ≠ .x14 → g ≠ .x15 →
    g ≠ .x16 → g ≠ .x17 → g ≠ .x28 → g ≠ .x29 → g ≠ .x31 → s.getReg g = S0.getReg g
  frame : ∀ w < 2 ^ 33, (w < scratchW ∨ scratchW + 25 ≤ w) → (w < Lw 0 ∨ Lw k ≤ w) →
    memoryView s w = memoryView S0 w
  entries : ∀ j < k, ∀ t < 6, memoryView s (Lw j + t) = listVal (memoryView S0) (ys j) (idx j) t
  idxMem : ∀ j < card, memoryView S0 (IW + j) = BitVec.ofNat 64 (idx j)
  idxSmall : ∀ j < card, idx j < LENGTH
  le : k ≤ card
  cardBound : card ≤ LENGTH

theorem p1_ready_of {S0 s : MachineState} {k card : Nat} {idx : Nat → Nat} {ys : Nat → Sampling.Block}
    (inv : P1Inv S0 s k card idx ys) (hk : k < card) : P1Ready s k (idx k) card := by
  have hc := inv.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have iwv : IW = 1023411204 := rfl
  refine ⟨by rw [inv.pc, if_neg (by omega)], inv.idx14, ?_, inv.reply, inv.list, inv.left, inv.size, inv.out,
    inv.prim, inv.sel, inv.idxSmall k hk, hk, hc⟩
  rw [inv.frame (IW + k) (by omega) (Or.inr (by unfold scratchW; omega)) (Or.inr (by unfold Lw; omega))]
  exact inv.idxMem k hk

theorem p1_inv_step {S0 s : MachineState} {k card : Nat} {idx : Nat → Nat} {ys : Nat → Sampling.Block}
    (inv : P1Inv S0 s k card idx ys) (hk : k < card) (y : Sampling.Block) :
    P1Inv S0 (p1Next s y) (k + 1) card idx (Function.update ys k y) := by
  have hc := inv.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have rwv : Rw = 603980313 := rfl
  have hi := inv.idxSmall k hk
  obtain ⟨mem, x14, x17, x16, pc, keep⟩ := p1_next_facts s k (idx k) card (p1_ready_of inv hk) y
  have mb := mate_word_bounds (idx k) (by omega)
  refine ⟨pc, x14, ?_, x17, x16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv.idxMem, inv.idxSmall, by omega, hc⟩
  · exact (keep .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans inv.reply
  · exact (keep .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans inv.size
  · exact (keep .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans inv.out
  · exact (keep .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans inv.prim
  · exact (keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans inv.sel
  · intro g h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h28 h29 h31
    exact (keep g h6 h7 h10 h14 h16 h17 h28 h29 h31).trans
      (inv.keep g h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h28 h29 h31)
  · intro w hw outS outL
    rw [mem w hw, p1mem_other _ _ _ _ _ (by unfold Lw at outL ⊢; omega), window_out _ _ _ outS]
    exact inv.frame w hw outS (by unfold Lw at outL ⊢; omega)
  · intro j hj t ht
    have bound : Lw j + t < 2 ^ 33 := by unfold Lw; omega
    rw [mem _ bound]
    by_cases last : j = k
    · subst last
      rw [p1mem_entry _ _ _ _ _ ht (by omega), Function.update_self]
      unfold listVal
      split
      · rfl
      · rw [inv.frame _ (by omega) (Or.inr (by unfold scratchW; omega)) (Or.inr (by unfold Lw; omega))]
    · rw [p1mem_other _ _ _ _ _ (by unfold Lw; omega), window_out _ _ _ (Or.inr (by unfold scratchW Lw; omega)),
        Function.update_of_ne last]
      exact inv.entries j (by omega) t ht

/-- Pass 1 as an oracle computation: `n` positions from ordinal `k`, the queries read from `M0`. -/
def pass1Loop (M0 : Memory) (idx : Nat → Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n + 1, k, s => do
      let y ← World.query (.inr (.inr (.inr (packBuffer (window M0 (Rw + 25 * idx k))))))
      pass1Loop M0 idx n (k + 1) (p1Next s y)

theorem query_window {S0 s : MachineState} {k card : Nat} {idx : Nat → Nat} {ys : Nat → Sampling.Block}
    (inv : P1Inv S0 s k card idx ys) (hk : k < card) :
    window (memoryView s) (Rw + 25 * idx k) = (window (memoryView S0) (Rw + 25 * idx k) : Words 25) := by
  have hc := inv.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have rwv : Rw = 603980313 := rfl
  have hi := inv.idxSmall k hk
  funext m
  have hm := m.isLt
  exact inv.frame _ (by omega) (Or.inr (by unfold scratchW; omega)) (Or.inr (by unfold Lw; omega))

theorem pass1_run (S0 : MachineState) (card : Nat) (idx : Nat → Nat) :
    ∀ n k (s : MachineState) (ys : Nat → Sampling.Block), k + n = card → P1Inv S0 s k card idx ys →
      ∀ fuel coins, execute openingImage (32 * n + fuel) s coins =
        (do let t ← pass1Loop (memoryView S0) idx n k s
            let res ← execute openingImage fuel t coins
            return res.charge (61 * n) n) := by
  intro n
  induction n with
  | zero =>
    intro k s ys _ _ fuel coins
    simp only [pass1Loop, Nat.mul_zero, Nat.zero_add, pure_bind]
    have h : ∀ res : Execution, res.charge 0 0 = res := fun res => by simp [Execution.charge]
    simp only [h, bind_pure]
  | succ n ih =>
    intro k s ys total inv fuel coins
    have hk : k < card := by omega
    rw [show 32 * (n + 1) + fuel = 32 + (32 * n + fuel) by ring,
      execute_p1 s k (idx k) card (p1_ready_of inv hk), query_window inv hk]
    simp only [pass1Loop, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro y _
    rw [ih (k + 1) (p1Next s y) (Function.update ys k y) (by omega) (p1_inv_step inv hk y)]
    simp only [bind_assoc, pure_bind, charge_charge]
    rw [show 61 + 61 * n = 61 * (n + 1) by ring, show 1 + n = n + 1 by ring]

/-- Every reachable end of pass 1 satisfies the invariant at `card`, for some answers. -/
theorem pass1_support (S0 : MachineState) (card : Nat) (idx : Nat → Nat) :
    ∀ n k (s : MachineState) (ys : Nat → Sampling.Block), k + n = card → P1Inv S0 s k card idx ys →
      ∀ t ∈ support (pass1Loop (memoryView S0) idx n k s), ∃ ys', P1Inv S0 t card card idx ys' := by
  intro n
  induction n with
  | zero =>
    intro k s ys total inv t reached
    simp only [pass1Loop, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨ys, by simpa [show k = card by omega] using inv⟩
  | succ n ih =>
    intro k s ys total inv t reached
    have hk : k < card := by omega
    simp only [pass1Loop, mem_support_bind_iff] at reached
    obtain ⟨y, _, rest⟩ := reached
    exact ih (k + 1) (p1Next s y) (Function.update ys k y) (by omega) (p1_inv_step inv hk y) t rest

/-- Iterate a per-ordinal state step `n` times from ordinal `k`. -/
def iterState (f : Nat → MachineState → MachineState) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n + 1, k, s => iterState f n (k + 1) (f k s)

theorem iter_zero (f : Nat → MachineState → MachineState) (k : Nat) (s : MachineState) : iterState f 0 k s = s := rfl

theorem iter_succ (f : Nat → MachineState → MachineState) (n k : Nat) (s : MachineState) :
    iterState f (n + 1) k s = iterState f n (k + 1) (f k s) := rfl

/-- One pass-1 position with a fixed answer function (the fixed oracle's inverse permutation). -/
def p1Honest (ans : Sampling.Block → Sampling.Block) (M0 : Memory) (idx : Nat → Nat) (k : Nat) (s : MachineState) :
    MachineState := p1Next s (ans (packBuffer (window M0 (Rw + 25 * idx k))))

/-- The fixed oracle's answer to an inverse query. -/
def inverseAnswer (oracle : Oracle) (q : Sampling.Block) : Sampling.Block :=
  oracle.answer (m := Id) (.inr (.inr q))

theorem inverse_answer (oracle : Oracle) (q : Sampling.Block) : inverseAnswer oracle q = oracle.permutation.symm q :=
  rfl

theorem pass1_fixed (oracle : Oracle) (M0 : Memory) (idx : Nat → Nat) :
    ∀ n k s, fixedOracleRun oracle (pass1Loop M0 idx n k s) =
      pure (iterState (p1Honest (inverseAnswer oracle) M0 idx) n k s) := by
  intro n
  induction n with
  | zero => intro k s; rw [iter_zero]; simp only [pass1Loop, fixed_oracle_run_pure]
  | succ n ih =>
    intro k s
    rw [iter_succ]
    simp only [pass1Loop]
    rw [fixed_oracle_run_public, ih]
    rfl

theorem pass1_det_inv (S0 : MachineState) (card : Nat) (idx : Nat → Nat) (ans : Sampling.Block → Sampling.Block) :
    ∀ n k (s : MachineState) (ys : Nat → Sampling.Block), k + n = card → P1Inv S0 s k card idx ys →
      (∀ j < k, ys j = ans (packBuffer (window (memoryView S0) (Rw + 25 * idx j)))) →
      ∃ ys', P1Inv S0 (iterState (p1Honest ans (memoryView S0) idx) n k s) card card idx ys' ∧
        ∀ j < card, ys' j = ans (packBuffer (window (memoryView S0) (Rw + 25 * idx j))) := by
  intro n
  induction n with
  | zero =>
    intro k s ys total inv honest
    have e : k = card := by omega
    subst e
    rw [iter_zero]
    exact ⟨ys, inv, honest⟩
  | succ n ih =>
    intro k s ys total inv honest
    have hk : k < card := by omega
    have step := p1_inv_step inv hk (ans (packBuffer (window (memoryView S0) (Rw + 25 * idx k))))
    rw [iter_succ]
    refine ih (k + 1) (p1Honest ans (memoryView S0) idx k s) _ (by omega) step ?_
    intro j hj
    by_cases e : j = k
    · subst e; rw [Function.update_self]
    · rw [Function.update_of_ne e]; exact honest j (by omega)

/-! ### Pass 2: list entries to the leader's salt slot and the mate's heap leaf slot (no calls) -/

/-- Word indices of the leader's salt table (`x22`) and of the heap leaf slots (`a5 = s1 + 2^29`). -/
def NW : Nat := TDw + 10 * 2 ^ 24
def HW : Nat := TDw + 2 ^ 26

def p2OpsA2 : List Instr := [.SLLI .x30 .x6 4, .ADD .x30 .x22 .x30]
def p2OpsB : List Instr := [.XORI .x30 .x6 1, .SLLI .x30 .x30 5, .ADD .x30 .x15 .x30]
def p2OpsF : List Instr := p1OpsF3 ++ [.BNE .x16 .x0 8108]

def p2A (s : MachineState) : MachineState := runOps (execInstrBr s (.LD .x6 .x14 0)) p2OpsA2

def p2Salt (t : MachineState) : MachineState := copyPair (copyPair t .x17 .x30 0 0) .x17 .x30 8 8

def p2Digest (t : MachineState) : MachineState :=
  copyPair (copyPair (copyPair (copyPair t .x17 .x30 16 0) .x17 .x30 24 8) .x17 .x30 32 16) .x17 .x30 40 24

def p2Next (s : MachineState) : MachineState := runOps (p2Digest (runOps (p2Salt (p2A s)) p2OpsB)) p2OpsF

structure P2Ready (s : MachineState) (k i card : Nat) : Prop where
  pc : s.pc = opPC 1481
  idx : s.getReg .x14 = wordAddress (IW + k)
  idxVal : memoryView s (IW + k) = BitVec.ofNat 64 i
  list : s.getReg .x17 = wordAddress (Lw k)
  left : s.getReg .x16 = BitVec.ofNat 64 (card - k)
  heap : s.getReg .x15 = wordAddress HW
  salts : s.getReg .x22 = wordAddress NW
  small : i < LENGTH
  present : k < card
  cardBound : card ≤ LENGTH

theorem shift_word (i n : Nat) (small : 2 ^ n * i < 2 ^ 64) :
    BitVec.ofNat 64 i <<< n = BitVec.ofNat 64 (2 ^ n * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hi : i < 2 ^ 64 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    calc i ≤ 2 ^ n * i := Nat.le_mul_of_pos_left i (by omega)
      _ < 2 ^ 64 := small
  rw [Nat.mod_eq_of_lt hi, Nat.mul_comm]

theorem xor_one_word (i : Nat) (small : i < 2 ^ 62) :
    BitVec.ofNat 64 i ^^^ signExtend12 1 = BitVec.ofNat 64 (i ^^^ 1) := by
  rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 by decide]
  apply BitVec.eq_of_toNat_eq
  have bound : i ^^^ 1 < 2 ^ 64 := by
    have := Nat.xor_lt_two_pow (n := 62) small (by decide : 1 < 2 ^ 62)
    omega
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt bound]

theorem xor_one_small (i : Nat) (hi : i < 2 ^ 24) : i ^^^ 1 < 2 ^ 24 :=
  Nat.xor_lt_two_pow hi (by decide)

theorem p2a_facts (s : MachineState) (k i card : Nat) (r : P2Ready s k i card) :
    (p2A s).getReg .x6 = BitVec.ofNat 64 i ∧ (p2A s).getReg .x30 = wordAddress (NW + 2 * i) ∧
    (p2A s).mem = s.mem ∧ (p2A s).pc = opPC 1484 ∧
    ∀ g, g ≠ .x6 → g ≠ .x30 → (p2A s).getReg g = s.getReg g := by
  have hi := r.small
  have len : LENGTH = 2 ^ 24 := rfl
  have v6 : s.getMem (s.getReg .x14 + signExtend12 0) = BitVec.ofNat 64 i := by
    rw [r.idx, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]; exact r.idxVal
  have e6 : (p2A s).getReg .x6 = s.getMem (s.getReg .x14 + signExtend12 0) := by
    simp only [p2A, runOps, p2OpsA2, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte, and_self]
  have e30 : (p2A s).getReg .x30 = s.getReg .x22 + (s.getMem (s.getReg .x14 + signExtend12 0) <<< (4 : BitVec 6).toNat) := by
    simp only [p2A, runOps, p2OpsA2, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte, and_self]
  refine ⟨e6.trans v6, ?_, ?_, ?_, ?_⟩
  · rw [e30, v6, r.salts, show (4 : BitVec 6).toNat = 4 from rfl, shift_word i 4 (by omega),
      show 2 ^ 4 * i = 8 * (2 * i) by ring, address_up]
  · simp only [p2A, p2OpsA2, runOps, List.foldl, execInstrBr, set_mem]
  · rw [show (p2A s).pc = s.pc + 4 + 4 + 4 from rfl, r.pc]; decide
  · intro g a b
    simp [p2A, p2OpsA2, runOps, execInstrBr, Ne.symm a, Ne.symm b]

theorem stage_p2b (T : MachineState) (i : Nat) (hi : i < 2 ^ 24) (x6 : T.getReg .x6 = BitVec.ofNat 64 i)
    (x15 : T.getReg .x15 = wordAddress HW) :
    (runOps T p2OpsB).getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) ∧ (runOps T p2OpsB).mem = T.mem ∧
    (runOps T p2OpsB).pc = T.pc + 4 + 4 + 4 ∧ ∀ g, g ≠ .x30 → (runOps T p2OpsB).getReg g = T.getReg g := by
  have e30 : (runOps T p2OpsB).getReg .x30 = T.getReg .x15 + ((T.getReg .x6 ^^^ signExtend12 1) <<< (5 : BitVec 6).toNat) := by
    simp only [runOps, p2OpsB, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte, and_self]
  have xs := xor_one_small i hi
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [e30, x6, x15, xor_one_word i (by omega), show (5 : BitVec 6).toNat = 5 from rfl,
      shift_word _ 5 (by omega), show 2 ^ 5 * (i ^^^ 1) = 8 * (4 * (i ^^^ 1)) by ring, address_up]
  · simp only [runOps, p2OpsB, List.foldl, execInstrBr, set_mem]
  · intro g a
    simp [p2OpsB, runOps, execInstrBr, Ne.symm a]

theorem stage_f2 (E : MachineState) (k card : Nat) (hk : k < card) (hc : card ≤ 2 ^ 24)
    (x14 : E.getReg .x14 = wordAddress (IW + k)) (x16 : E.getReg .x16 = BitVec.ofNat 64 (card - k))
    (x17 : E.getReg .x17 = wordAddress (Lw k)) (pc : E.pc = opPC 1499) :
    (runOps E p2OpsF).getReg .x14 = wordAddress (IW + (k + 1)) ∧
    (runOps E p2OpsF).getReg .x16 = BitVec.ofNat 64 (card - (k + 1)) ∧
    (runOps E p2OpsF).getReg .x17 = wordAddress (Lw (k + 1)) ∧
    (runOps E p2OpsF).mem = E.mem ∧
    (runOps E p2OpsF).pc = (if k + 1 = card then opPC 1503 else opPC 1481) ∧
    ∀ g, g ≠ .x14 → g ≠ .x16 → g ≠ .x17 → (runOps E p2OpsF).getReg g = E.getReg g := by
  have split3 : runOps E p2OpsF = execInstrBr (runOps E p1OpsF3) (.BNE .x16 .x0 8108) := by
    rw [p2OpsF, run_ops_append, run_ops_singleton]
  let F3 := runOps E p1OpsF3
  have f16 : F3.getReg .x16 = BitVec.ofNat 64 (card - (k + 1)) := by
    have e : F3.getReg .x16 = E.getReg .x16 + signExtend12 4095 := by
      simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
        reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e, x16, show signExtend12 (4095 : BitVec 12) = BitVec.ofNat 64 (2 ^ 64 - 1) by decide, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [show card - k + (2 ^ 64 - 1) = (card - (k + 1)) + 2 ^ 64 by omega, Nat.add_mod_right]
  have f14 : F3.getReg .x14 = wordAddress (IW + (k + 1)) := by
    have e : F3.getReg .x14 = E.getReg .x14 + signExtend12 8 := by
      simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
        reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e, x14, show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 (8 * 1) by decide, address_up, Nat.add_assoc]
  have f17 : F3.getReg .x17 = wordAddress (Lw (k + 1)) := by
    have e : F3.getReg .x17 = E.getReg .x17 + signExtend12 48 := by
      simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
        reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [e, x17, show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 (8 * 6) by decide, address_up]
    unfold Lw; congr 1
  have fpc : F3.pc = opPC 1502 := by
    change E.pc + 4 + 4 + 4 = _
    rw [pc]; rfl
  have fmem : F3.mem = E.mem := by simp only [F3, runOps, p1OpsF3, List.foldl, execInstrBr, set_mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [split3, bne_reg]; exact f14
  · rw [split3, bne_reg]; exact f16
  · rw [split3, bne_reg]; exact f17
  · rw [split3, bne_mem]; exact fmem
  · rw [split3, bne_pc]
    have zero : (runOps E p1OpsF3).getReg .x0 = 0 := rfl
    rw [f16, zero, fpc]
    by_cases last : k + 1 = card
    · rw [if_pos last, show card - (k + 1) = 0 by omega, if_neg (by decide)]
      decide
    · have nz : (BitVec.ofNat 64 (card - (k + 1)) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        simp at this
        omega
      rw [if_neg last, if_pos nz]
      decide
  · intro g a b c
    rw [split3, bne_reg]
    simp [F3, runOps, p1OpsF3, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c]

/-- The six slot words a pass-2 position writes, each from its list word. -/
def p2Mem (M : Memory) (k i : Nat) : Memory :=
  writeWord (writeWord (writeWord (writeWord (writeWord (writeWord M
    (NW + 2 * i) (M (Lw k))) (NW + 2 * i + 1) (M (Lw k + 1)))
    (HW + 4 * (i ^^^ 1)) (M (Lw k + 2))) (HW + 4 * (i ^^^ 1) + 1) (M (Lw k + 3)))
    (HW + 4 * (i ^^^ 1) + 2) (M (Lw k + 4))) (HW + 4 * (i ^^^ 1) + 3) (M (Lw k + 5))

theorem p2_next_facts (s : MachineState) (k i card : Nat) (r : P2Ready s k i card) :
    (∀ w < 2 ^ 33, memoryView (p2Next s) w = p2Mem (memoryView s) k i w) ∧
    (p2Next s).getReg .x14 = wordAddress (IW + (k + 1)) ∧
    (p2Next s).getReg .x17 = wordAddress (Lw (k + 1)) ∧
    (p2Next s).getReg .x16 = BitVec.ofNat 64 (card - (k + 1)) ∧
    (p2Next s).pc = (if k + 1 = card then opPC 1503 else opPC 1481) ∧
    (∀ g, g ≠ .x6 → g ≠ .x14 → g ≠ .x16 → g ≠ .x17 → g ≠ .x30 → g ≠ .x31 → (p2Next s).getReg g = s.getReg g) := by
  have hi := r.small
  have hk := r.present
  have hc := r.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have xs := xor_one_small i (by omega)
  have lwk : Lw k + 6 ≤ 2 ^ 27 + 6 * 2 ^ 24 := by unfold Lw; omega
  have nwv : NW = 704643588 := rfl
  have hwv : HW = 603980292 := rfl
  obtain ⟨a6, a30, amem, apc, akeep⟩ := p2a_facts s k i card r
  let A := p2A s
  have a17 : A.getReg .x17 = wordAddress (Lw k) := (akeep .x17 (by decide) (by decide)).trans r.list
  obtain ⟨c1, c1pc, c1keep⟩ := copy_pair_view A .x17 .x30 (by decide) (by decide)
    (Lw k) (NW + 2 * i) 0 0 a17 a30 0 0 (by decide) (by decide) (by omega) (by omega)
  let C1 := copyPair A .x17 .x30 0 0
  obtain ⟨c2, c2pc, c2keep⟩ := copy_pair_view C1 .x17 .x30 (by decide) (by decide)
    (Lw k) (NW + 2 * i) 1 1 ((c1keep .x17 (by decide)).trans a17) ((c1keep .x30 (by decide)).trans a30)
    8 8 (by decide) (by decide) (by omega) (by omega)
  let C := copyPair C1 .x17 .x30 8 8
  have ckeep (g : Reg) (h : g ≠ .x31) : C.getReg g = A.getReg g := (c2keep g h).trans (c1keep g h)
  obtain ⟨b30, bmem, bpc, bkeep⟩ := stage_p2b C i (by omega) ((ckeep .x6 (by decide)).trans a6)
    ((ckeep .x15 (by decide)).trans ((akeep .x15 (by decide) (by decide)).trans r.heap))
  let B := runOps C p2OpsB
  have b17 : B.getReg .x17 = wordAddress (Lw k) := (bkeep .x17 (by decide)).trans ((ckeep .x17 (by decide)).trans a17)
  obtain ⟨e1, e1pc, e1keep⟩ := copy_pair_view B .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 2 0 b17 b30 16 0 (by decide) (by decide) (by omega) (by omega)
  let E1 := copyPair B .x17 .x30 16 0
  have e1_17 : E1.getReg .x17 = wordAddress (Lw k) := (e1keep .x17 (by decide)).trans b17
  have e1_30 : E1.getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) := (e1keep .x30 (by decide)).trans b30
  obtain ⟨e2, e2pc, e2keep⟩ := copy_pair_view E1 .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 3 1 e1_17 e1_30 24 8 (by decide) (by decide) (by omega) (by omega)
  let E2 := copyPair E1 .x17 .x30 24 8
  have e2_17 : E2.getReg .x17 = wordAddress (Lw k) := (e2keep .x17 (by decide)).trans e1_17
  have e2_30 : E2.getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) := (e2keep .x30 (by decide)).trans e1_30
  obtain ⟨e3, e3pc, e3keep⟩ := copy_pair_view E2 .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 4 2 e2_17 e2_30 32 16 (by decide) (by decide) (by omega) (by omega)
  let E3 := copyPair E2 .x17 .x30 32 16
  have e3_17 : E3.getReg .x17 = wordAddress (Lw k) := (e3keep .x17 (by decide)).trans e2_17
  have e3_30 : E3.getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) := (e3keep .x30 (by decide)).trans e2_30
  obtain ⟨e4, e4pc, e4keep⟩ := copy_pair_view E3 .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 5 3 e3_17 e3_30 40 24 (by decide) (by decide) (by omega) (by omega)
  let E := copyPair E3 .x17 .x30 40 24
  have ekeep (g : Reg) (h : g ≠ .x31) : E.getReg g = B.getReg g :=
    (e4keep g h).trans ((e3keep g h).trans ((e2keep g h).trans (e1keep g h)))
  have toA (g : Reg) (h30 : g ≠ .x30) (h31 : g ≠ .x31) : E.getReg g = A.getReg g :=
    (ekeep g h31).trans ((bkeep g h30).trans (ckeep g h31))
  have epc : E.pc = opPC 1499 := by
    rw [e4pc, e3pc, e2pc, e1pc, bpc, c2pc, c1pc, apc]; decide
  obtain ⟨f14, f16, f17, fmem, fpc, fkeep⟩ := stage_f2 E k card hk (by omega)
    ((toA .x14 (by decide) (by decide)).trans ((akeep .x14 (by decide) (by decide)).trans r.idx))
    ((toA .x16 (by decide) (by decide)).trans ((akeep .x16 (by decide) (by decide)).trans r.left))
    ((ekeep .x17 (by decide)).trans b17) epc
  have nextIs : p2Next s = runOps E p2OpsF := rfl
  rw [nextIs]
  refine ⟨?_, f14, f17, f16, fpc, ?_⟩
  · intro w hw
    have view : memoryView (runOps E p2OpsF) w = bview (runOps E p2OpsF) w := by simp only [bview, hw, ↓reduceIte]
    have chain : bview (runOps E p2OpsF) = bview E := bview_congr fmem
    have bv : bview B = bview C := bview_congr bmem
    have av : bview A = fun w => if w < 2 ^ 33 then memoryView s w else 0 := by
      rw [bview_congr amem]; rfl
    rw [view, chain, e4, e3, e2, e1, bv, c2, c1, av]
    simp only [writeWord, p2Mem, hw, ↓reduceIte, Nat.add_zero]
    have l : ∀ t < 6, Lw k + t < 2 ^ 33 := by intro t _; unfold Lw; omega
    have d1 : ∀ t < 6, ¬ (Lw k + t = NW + 2 * i) := by intro t _; unfold Lw; omega
    have d2 : ∀ t < 6, ¬ (Lw k + t = NW + 2 * i + 1) := by intro t _; unfold Lw; omega
    have d3 : ∀ t < 6, ∀ u < 4, ¬ (Lw k + t = HW + 4 * (i ^^^ 1) + u) := by intro t _ u _; unfold Lw; omega
    have d3' : ∀ t < 6, ¬ (Lw k + t = HW + 4 * (i ^^^ 1)) := by intro t _; unfold Lw; omega
    simp only [l 0 (by decide), l 1 (by decide), l 2 (by decide), l 3 (by decide), l 4 (by decide), l 5 (by decide),
      Nat.add_zero, ↓reduceIte, d1 1 (by decide), d1 2 (by decide), d1 3 (by decide), d1 4 (by decide),
      d1 5 (by decide), d2 2 (by decide), d2 3 (by decide), d2 4 (by decide), d2 5 (by decide),
      d3' 3 (by decide), d3' 4 (by decide), d3' 5 (by decide), d3 4 (by decide) 1 (by decide),
      d3 5 (by decide) 1 (by decide), d3 5 (by decide) 2 (by decide)]
    have lk : Lw k < 2 ^ 33 := by unfold Lw; omega
    simp only [lk, ↓reduceIte]
  · intro g h6 h14 h16 h17 h30 h31
    rw [fkeep g h14 h16 h17, toA g h30 h31, akeep g h6 h30]

/-- The run of one pass-2 position: 22 steps, no calls. -/
theorem execute_p2 (s : MachineState) (k i card : Nat) (r : P2Ready s k i card) (fuel : Nat) (coins : Bool) :
    execute openingImage (22 + fuel) s coins =
      (do let res ← execute openingImage fuel (p2Next s) coins; return res.charge 22 0) := by
  have hi := r.small
  have hk := r.present
  have hc := r.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have iwv : IW = 1023411204 := rfl
  have xs := xor_one_small i (by omega)
  have lwk : Lw k + 6 ≤ 2 ^ 27 + 6 * 2 ^ 24 := by unfold Lw; omega
  have nwv : NW = 704643588 := rfl
  have hwv : HW = 603980292 := rfl
  obtain ⟨a6, a30, _, apc, akeep⟩ := p2a_facts s k i card r
  let L := execInstrBr s (.LD .x6 .x14 0)
  have lpc : L.pc = opPC 1482 := by rw [ld_pc, r.pc, op_pc_next]
  have runL : ∀ X, execute openingImage (1 + X) s coins =
      (do let res ← execute openingImage X L coins; return res.charge 1 0) := fun X =>
    ordinary_one _ L (.LD .x6 .x14 0) _ _ (pre_fetch _ 1481 _ (by decide) r.pc rfl)
      (ld_step _ _ _ _ (by rw [r.idx]; exact word_valid (IW + k) 0 0 (by decide) (by omega))) rfl
  have runA : ∀ X, execute openingImage (2 + X) L coins =
      (do let res ← execute openingImage X (p2A s) coins; return res.charge 2 0) := fun X =>
    alu_run L 1482 p2OpsA2 X coins lpc (by decide)
      (by intro j h; change j < 2 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 1 := (by change j + 1 < 2 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 2 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 2 at h; interval_cases j <;> rfl)
  let A := p2A s
  have a17 : A.getReg .x17 = wordAddress (Lw k) := (akeep .x17 (by decide) (by decide)).trans r.list
  have runC1 : ∀ X, execute openingImage (2 + X) A coins =
      (do let res ← execute openingImage X (copyPair A .x17 .x30 0 0) coins; return res.charge 2 0) := fun X =>
    ld_sd_run A 1484 .x17 .x30 0 0 (Lw k) (NW + 2 * i) 0 0 apc (by decide) rfl rfl (by decide) a17 a30
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, c1pc, c1keep⟩ := copy_pair_view A .x17 .x30 (by decide) (by decide)
    (Lw k) (NW + 2 * i) 0 0 a17 a30 0 0 (by decide) (by decide) (by omega) (by omega)
  let C1 := copyPair A .x17 .x30 0 0
  have c1pc' : C1.pc = opPC 1486 := by rw [c1pc, apc]; decide
  have runC2 : ∀ X, execute openingImage (2 + X) C1 coins =
      (do let res ← execute openingImage X (copyPair C1 .x17 .x30 8 8) coins; return res.charge 2 0) := fun X =>
    ld_sd_run C1 1486 .x17 .x30 8 8 (Lw k) (NW + 2 * i) 1 1 c1pc' (by decide) rfl rfl (by decide)
      ((c1keep .x17 (by decide)).trans a17) ((c1keep .x30 (by decide)).trans a30)
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, c2pc, c2keep⟩ := copy_pair_view C1 .x17 .x30 (by decide) (by decide)
    (Lw k) (NW + 2 * i) 1 1 ((c1keep .x17 (by decide)).trans a17) ((c1keep .x30 (by decide)).trans a30)
    8 8 (by decide) (by decide) (by omega) (by omega)
  let C := copyPair C1 .x17 .x30 8 8
  have cpc : C.pc = opPC 1488 := by rw [c2pc, c1pc']; decide
  have ckeep (g : Reg) (h : g ≠ .x31) : C.getReg g = A.getReg g := (c2keep g h).trans (c1keep g h)
  obtain ⟨b30, _, bpc, bkeep⟩ := stage_p2b C i (by omega) ((ckeep .x6 (by decide)).trans a6)
    ((ckeep .x15 (by decide)).trans ((akeep .x15 (by decide) (by decide)).trans r.heap))
  let B := runOps C p2OpsB
  have bpc' : B.pc = opPC 1491 := by rw [bpc, cpc]; decide
  have runB : ∀ X, execute openingImage (3 + X) C coins =
      (do let res ← execute openingImage X B coins; return res.charge 3 0) := fun X =>
    alu_run C 1488 p2OpsB X coins cpc (by decide)
      (by intro j h; change j < 3 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 2 := (by change j + 1 < 3 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 3 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 3 at h; interval_cases j <;> rfl)
  have b17 : B.getReg .x17 = wordAddress (Lw k) := (bkeep .x17 (by decide)).trans ((ckeep .x17 (by decide)).trans a17)
  have runE1 : ∀ X, execute openingImage (2 + X) B coins =
      (do let res ← execute openingImage X (copyPair B .x17 .x30 16 0) coins; return res.charge 2 0) := fun X =>
    ld_sd_run B 1491 .x17 .x30 16 0 (Lw k) (HW + 4 * (i ^^^ 1)) 2 0 bpc' (by decide) rfl rfl (by decide) b17 b30
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e1pc, e1keep⟩ := copy_pair_view B .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 2 0 b17 b30 16 0 (by decide) (by decide) (by omega) (by omega)
  let E1 := copyPair B .x17 .x30 16 0
  have e1pc' : E1.pc = opPC 1493 := by rw [e1pc, bpc']; decide
  have e1_17 : E1.getReg .x17 = wordAddress (Lw k) := (e1keep .x17 (by decide)).trans b17
  have e1_30 : E1.getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) := (e1keep .x30 (by decide)).trans b30
  have runE2 : ∀ X, execute openingImage (2 + X) E1 coins =
      (do let res ← execute openingImage X (copyPair E1 .x17 .x30 24 8) coins; return res.charge 2 0) := fun X =>
    ld_sd_run E1 1493 .x17 .x30 24 8 (Lw k) (HW + 4 * (i ^^^ 1)) 3 1 e1pc' (by decide) rfl rfl (by decide) e1_17 e1_30
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e2pc, e2keep⟩ := copy_pair_view E1 .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 3 1 e1_17 e1_30 24 8 (by decide) (by decide) (by omega) (by omega)
  let E2 := copyPair E1 .x17 .x30 24 8
  have e2pc' : E2.pc = opPC 1495 := by rw [e2pc, e1pc']; decide
  have e2_17 : E2.getReg .x17 = wordAddress (Lw k) := (e2keep .x17 (by decide)).trans e1_17
  have e2_30 : E2.getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) := (e2keep .x30 (by decide)).trans e1_30
  have runE3 : ∀ X, execute openingImage (2 + X) E2 coins =
      (do let res ← execute openingImage X (copyPair E2 .x17 .x30 32 16) coins; return res.charge 2 0) := fun X =>
    ld_sd_run E2 1495 .x17 .x30 32 16 (Lw k) (HW + 4 * (i ^^^ 1)) 4 2 e2pc' (by decide) rfl rfl (by decide) e2_17 e2_30
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e3pc, e3keep⟩ := copy_pair_view E2 .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 4 2 e2_17 e2_30 32 16 (by decide) (by decide) (by omega) (by omega)
  let E3 := copyPair E2 .x17 .x30 32 16
  have e3pc' : E3.pc = opPC 1497 := by rw [e3pc, e2pc']; decide
  have e3_17 : E3.getReg .x17 = wordAddress (Lw k) := (e3keep .x17 (by decide)).trans e2_17
  have e3_30 : E3.getReg .x30 = wordAddress (HW + 4 * (i ^^^ 1)) := (e3keep .x30 (by decide)).trans e2_30
  have runE4 : ∀ X, execute openingImage (2 + X) E3 coins =
      (do let res ← execute openingImage X (copyPair E3 .x17 .x30 40 24) coins; return res.charge 2 0) := fun X =>
    ld_sd_run E3 1497 .x17 .x30 40 24 (Lw k) (HW + 4 * (i ^^^ 1)) 5 3 e3pc' (by decide) rfl rfl (by decide) e3_17 e3_30
      (by decide) (by decide) (by omega) (by omega) X coins
  obtain ⟨_, e4pc, _⟩ := copy_pair_view E3 .x17 .x30 (by decide) (by decide)
    (Lw k) (HW + 4 * (i ^^^ 1)) 5 3 e3_17 e3_30 40 24 (by decide) (by decide) (by omega) (by omega)
  let E := copyPair E3 .x17 .x30 40 24
  have epc : E.pc = opPC 1499 := by rw [e4pc, e3pc']; decide
  have runF : ∀ X, execute openingImage (4 + X) E coins =
      (do let res ← execute openingImage X (runOps E p2OpsF) coins; return res.charge 4 0) := fun X =>
    alu_run E 1499 p2OpsF X coins epc (by decide)
      (by intro j h; change j < 4 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 3 := (by change j + 1 < 4 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 4 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 4 at h; interval_cases j <;> rfl)
  have nextIs : p2Next s = runOps E p2OpsF := rfl
  rw [show 22 + fuel = 1 + (2 + (2 + (2 + (3 + (2 + (2 + (2 + (2 + (4 + fuel))))))))) by omega,
    runL, runA, runC1, runC2, runB, runE1, runE2, runE3, runE4, runF, nextIs]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

/-! ### Pass 2: the loop -/

theorem p2mem_salt (M : Memory) (k i t : Nat) (ht : t < 2) (hi : i < 2 ^ 24) :
    p2Mem M k i (NW + 2 * i + t) = M (Lw k + t) := by
  have xs := xor_one_small i hi
  have nwv : NW = 704643588 := rfl
  have hwv : HW = 603980292 := rfl
  interval_cases t <;> simp only [p2Mem, writeWord, Nat.add_zero] <;>
    split_ifs <;> first | rfl | omega

theorem p2mem_mate (M : Memory) (k i t : Nat) (ht : t < 4) (hi : i < 2 ^ 24) :
    p2Mem M k i (HW + 4 * (i ^^^ 1) + t) = M (Lw k + 2 + t) := by
  have xs := xor_one_small i hi
  have nwv : NW = 704643588 := rfl
  have hwv : HW = 603980292 := rfl
  interval_cases t <;> simp only [p2Mem, writeWord, Nat.add_zero] <;>
    split_ifs <;> first | rfl | omega

theorem p2mem_other (M : Memory) (k i w : Nat) (hs : w ≠ NW + 2 * i ∧ w ≠ NW + 2 * i + 1)
    (hm : ∀ t < 4, w ≠ HW + 4 * (i ^^^ 1) + t) : p2Mem M k i w = M w := by
  have h0 := hm 0 (by decide)
  have h1 := hm 1 (by decide)
  have h2 := hm 2 (by decide)
  have h3 := hm 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [p2Mem, writeWord]
  rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0, if_neg hs.2, if_neg hs.1]

theorem xor_one_inj {a b : Nat} (h : a ^^^ 1 = b ^^^ 1) : a = b := by
  have := congrArg (· ^^^ 1) h
  simpa [Nat.xor_assoc] using this

structure P2Inv (S1 s : MachineState) (k card : Nat) (idx : Nat → Nat) : Prop where
  pc : s.pc = if k = card then opPC 1503 else opPC 1481
  idx14 : s.getReg .x14 = wordAddress (IW + k)
  list : s.getReg .x17 = wordAddress (Lw k)
  left : s.getReg .x16 = BitVec.ofNat 64 (card - k)
  keep : ∀ g, g ≠ .x6 → g ≠ .x14 → g ≠ .x16 → g ≠ .x17 → g ≠ .x30 → g ≠ .x31 → s.getReg g = S1.getReg g
  heap : S1.getReg .x15 = wordAddress HW
  salts : S1.getReg .x22 = wordAddress NW
  frame : ∀ w < 2 ^ 33, (∀ j < k, w ≠ NW + 2 * idx j ∧ w ≠ NW + 2 * idx j + 1) →
    (∀ j < k, ∀ t < 4, w ≠ HW + 4 * (idx j ^^^ 1) + t) → memoryView s w = memoryView S1 w
  saltW : ∀ j < k, ∀ t < 2, memoryView s (NW + 2 * idx j + t) = memoryView S1 (Lw j + t)
  mateW : ∀ j < k, ∀ t < 4, memoryView s (HW + 4 * (idx j ^^^ 1) + t) = memoryView S1 (Lw j + 2 + t)
  idxMem : ∀ j < card, memoryView S1 (IW + j) = BitVec.ofNat 64 (idx j)
  idxSmall : ∀ j < card, idx j < LENGTH
  idxInj : ∀ j < card, ∀ j' < card, idx j = idx j' → j = j'
  le : k ≤ card
  cardBound : card ≤ LENGTH

theorem p2_ready_of {S1 s : MachineState} {k card : Nat} {idx : Nat → Nat} (inv : P2Inv S1 s k card idx)
    (hk : k < card) : P2Ready s k (idx k) card := by
  have hc := inv.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have iwv : IW = 1023411204 := rfl
  have nwv : NW = 704643588 := rfl
  have hwv : HW = 603980292 := rfl
  refine ⟨by rw [inv.pc, if_neg (by omega)], inv.idx14, ?_, inv.list, inv.left,
    (inv.keep .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.heap,
    (inv.keep .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans inv.salts,
    inv.idxSmall k hk, hk, hc⟩
  rw [inv.frame (IW + k) (by omega)]
  · exact inv.idxMem k hk
  · intro j hj
    have := inv.idxSmall j (by omega)
    constructor <;> omega
  · intro j hj t ht
    have := inv.idxSmall j (by omega)
    have := xor_one_small (idx j) (by omega)
    omega

theorem p2_inv_step {S1 s : MachineState} {k card : Nat} {idx : Nat → Nat} (inv : P2Inv S1 s k card idx)
    (hk : k < card) : P2Inv S1 (p2Next s) (k + 1) card idx := by
  have hc := inv.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have nwv : NW = 704643588 := rfl
  have hwv : HW = 603980292 := rfl
  have hi := inv.idxSmall k hk
  have xs := xor_one_small (idx k) (by omega)
  obtain ⟨mem, x14, x17, x16, pc, keep⟩ := p2_next_facts s k (idx k) card (p2_ready_of inv hk)
  have listFrame (j t : Nat) (hj : j < card) (ht : t < 6) : memoryView s (Lw j + t) = memoryView S1 (Lw j + t) := by
    apply inv.frame _ (by unfold Lw; omega)
    · intro j' hj'
      have := inv.idxSmall j' (by omega)
      constructor <;> (unfold Lw; omega)
    · intro j' hj' u hu
      have := inv.idxSmall j' (by omega)
      have := xor_one_small (idx j') (by omega)
      unfold Lw; omega
  refine ⟨pc, x14, x17, x16, ?_, inv.heap, inv.salts, ?_, ?_, ?_, inv.idxMem, inv.idxSmall, inv.idxInj, by omega, hc⟩
  · intro g h6 h14 h16 h17 h30 h31
    exact (keep g h6 h14 h16 h17 h30 h31).trans (inv.keep g h6 h14 h16 h17 h30 h31)
  · intro w hw hs hm
    rw [mem w hw, p2mem_other _ _ _ _ (hs k (by omega)) (hm k (by omega))]
    exact inv.frame w hw (fun j hj => hs j (by omega)) (fun j hj => hm j (by omega))
  · intro j hj t ht
    have hj' := inv.idxSmall j (by omega)
    rw [mem _ (by omega)]
    by_cases last : j = k
    · subst last
      rw [p2mem_salt _ _ _ _ ht (by omega)]
      exact listFrame j t hk (by omega)
    · have ne : idx j ≠ idx k := fun e => last (inv.idxInj j (by omega) k hk e)
      rw [p2mem_other _ _ _ _ (by constructor <;> omega) (by
        intro u hu; have := xor_one_small (idx j) (by omega); omega)]
      exact inv.saltW j (by omega) t ht
  · intro j hj t ht
    have hj' := inv.idxSmall j (by omega)
    have xj := xor_one_small (idx j) (by omega)
    rw [mem _ (by omega)]
    by_cases last : j = k
    · subst last
      rw [p2mem_mate _ _ _ _ ht (by omega), Nat.add_assoc]
      exact listFrame j (2 + t) hk (by omega)
    · have ne : idx j ^^^ 1 ≠ idx k ^^^ 1 := fun e => last (inv.idxInj j (by omega) k hk (xor_one_inj e))
      rw [p2mem_other _ _ _ _ (by constructor <;> omega) (by intro u hu; omega)]
      exact inv.mateW j (by omega) t ht

theorem pass2_run (S1 : MachineState) (card : Nat) (idx : Nat → Nat) :
    ∀ n k (s : MachineState), k + n = card → P2Inv S1 s k card idx →
      ∀ fuel coins, execute openingImage (22 * n + fuel) s coins =
        (do let res ← execute openingImage fuel (iterState (fun _ => p2Next) n k s) coins
            return res.charge (22 * n) 0) := by
  intro n
  induction n with
  | zero =>
    intro k s _ _ fuel coins
    rw [iter_zero]
    have h : ∀ res : Execution, res.charge 0 0 = res := fun res => by simp [Execution.charge]
    simp only [Nat.mul_zero, Nat.zero_add, h, bind_pure]
  | succ n ih =>
    intro k s total inv fuel coins
    have hk : k < card := by omega
    rw [show 22 * (n + 1) + fuel = 22 + (22 * n + fuel) by ring,
      execute_p2 s k (idx k) card (p2_ready_of inv hk), iter_succ,
      ih (k + 1) (p2Next s) (by omega) (p2_inv_step inv hk)]
    simp only [bind_assoc, pure_bind, charge_charge]
    rw [show 22 + 22 * n = 22 * (n + 1) by ring]

theorem pass2_inv (S1 : MachineState) (card : Nat) (idx : Nat → Nat) :
    ∀ n k (s : MachineState), k + n = card → P2Inv S1 s k card idx →
      P2Inv S1 (iterState (fun _ => p2Next) n k s) card card idx := by
  intro n
  induction n with
  | zero =>
    intro k s total inv
    have e : k = card := by omega
    subst e
    rw [iter_zero]; exact inv
  | succ n ih =>
    intro k s total inv
    rw [iter_succ]
    exact ih (k + 1) _ (by omega) (p2_inv_step inv (by omega))

/-! ### Head (word 12, words 1435..1443), middle (1476..1480) and tail (1503, 1504) -/

def headOps : List Instr := [.ADDI .x14 .x8 0, .ADDI .x11 .x0 200, .LUI .x12 4, .ADDI .x13 .x0 2, .ADDI .x5 .x0 0,
  .LUI .x15 0x20000, .ADDI .x15 .x15 168, .ADD .x15 .x9 .x15, .LUI .x17 0x40000]
def midOps : List Instr := [.ADDI .x14 .x8 0, .ADDI .x16 .x18 0, .LUI .x17 0x40000, .LUI .x15 0x20000,
  .ADD .x15 .x9 .x15]
def tailOps : List Instr := [.ADDI .x27 .x0 256, .JAL .x0 2091188]

def headState (Q : MachineState) : MachineState := runOps (execInstrBr Q (.JAL .x0 5692)) headOps
def midState (T : MachineState) : MachineState := runOps T midOps
def tailState (V : MachineState) : MachineState := runOps V tailOps

theorem head_facts (Q : MachineState) (pc : Q.pc = opPC 12)
    (x8 : Q.getReg .x8 = BitVec.ofNat 64 Opening.indicesBase)
    (x9 : Q.getReg .x9 = BitVec.ofNat 64 Opening.trapdoorBase) :
    (headState Q).getReg .x14 = wordAddress (IW + 0) ∧ (headState Q).getReg .x11 = 200 ∧
    (headState Q).getReg .x12 = wordAddress scratchW ∧ (headState Q).getReg .x13 = 2 ∧
    (headState Q).getReg .x5 = 0 ∧ (headState Q).getReg .x15 = wordAddress Rw ∧
    (headState Q).getReg .x17 = wordAddress (Lw 0) ∧ (headState Q).mem = Q.mem ∧
    (headState Q).pc = opPC 1444 ∧
    (∀ g, g ≠ .x5 → g ≠ .x11 → g ≠ .x12 → g ≠ .x13 → g ≠ .x14 → g ≠ .x15 → g ≠ .x17 →
      (headState Q).getReg g = Q.getReg g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    rw [x8]; decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    rw [x9]; decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [headState, headOps, runOps, List.foldl, execInstrBr, set_mem]
  · rw [show (headState Q).pc = Q.pc + signExtend21 5692 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl, pc]
    decide
  · intro g a b c d e f h
    simp [headState, headOps, runOps, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e,
      Ne.symm f, Ne.symm h]

theorem mid_facts (T : MachineState) (pc : T.pc = opPC 1476)
    (x8 : T.getReg .x8 = BitVec.ofNat 64 Opening.indicesBase)
    (x9 : T.getReg .x9 = BitVec.ofNat 64 Opening.trapdoorBase) :
    (midState T).getReg .x14 = wordAddress (IW + 0) ∧ (midState T).getReg .x16 = T.getReg .x18 ∧
    (midState T).getReg .x17 = wordAddress (Lw 0) ∧ (midState T).getReg .x15 = wordAddress HW ∧
    (midState T).mem = T.mem ∧ (midState T).pc = opPC 1481 ∧
    (∀ g, g ≠ .x14 → g ≠ .x15 → g ≠ .x16 → g ≠ .x17 → (midState T).getReg g = T.getReg g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [midState, midOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    rw [x8]; decide
  · simp only [midState, midOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    rw [show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]
  · simp only [midState, midOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [midState, midOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    rw [x9]; decide
  · simp only [midState, midOps, runOps, List.foldl, execInstrBr, set_mem]
  · rw [show (midState T).pc = T.pc + 4 + 4 + 4 + 4 + 4 from rfl, pc]; decide
  · intro g a b c d
    simp [midState, midOps, runOps, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

theorem tail_facts (V : MachineState) (pc : V.pc = opPC 1503) :
    (tailState V).getReg .x27 = 256 ∧ (tailState V).mem = V.mem ∧ (tailState V).pc = 0x1034 ∧
    (∀ g, g ≠ .x27 → (tailState V).getReg g = V.getReg g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [tailState, tailOps, runOps, List.foldl, execInstrBr, Opening.getReg_setReg, MachineState.getReg_setPC,
      reduceCtorEq, false_and, true_and, ne_eq, not_false_eq_true, not_true_eq_false, and_false, ↓reduceIte,
      reg_zero]
    decide
  · simp only [tailState, tailOps, runOps, List.foldl, execInstrBr, set_mem]
  · rw [show (tailState V).pc = V.pc + 4 + signExtend21 2091188 from rfl, pc]; decide
  · intro g a
    simp [tailState, tailOps, runOps, execInstrBr, Ne.symm a]

theorem run_head (Q : MachineState) (pc : Q.pc = opPC 12) (fuel : Nat) (coins : Bool) :
    execute openingImage (10 + fuel) Q coins =
      (do let res ← execute openingImage fuel (headState Q) coins; return res.charge 10 0) := by
  have jumpRun : ∀ X, execute openingImage (1 + X) Q coins =
      (do let res ← execute openingImage X (runOps Q [.JAL .x0 5692]) coins; return res.charge 1 0) := fun X =>
    alu_run Q 12 [.JAL .x0 5692] X coins pc (by decide)
      (by intro j h; change j < 1 at h; interval_cases j; rfl)
      (by intro j h t; change j + 1 < 1 at h; omega)
      (by intro j h t; change j < 1 at h; interval_cases j; rfl)
      (by intro j h; change j < 1 at h; interval_cases j; rfl)
  have jpc : (execInstrBr Q (.JAL .x0 5692)).pc = opPC 1435 := by
    rw [show (execInstrBr Q (.JAL .x0 5692)).pc = Q.pc + signExtend21 5692 from rfl, pc]; decide
  have headRun : ∀ X, execute openingImage (9 + X) (execInstrBr Q (.JAL .x0 5692)) coins =
      (do let res ← execute openingImage X (headState Q) coins; return res.charge 9 0) := fun X =>
    alu_run _ 1435 headOps X coins jpc (by decide)
      (by intro j h; change j < 9 at h; interval_cases j <;> rfl)
      (by intro j h t; have hj : j < 8 := (by change j + 1 < 9 at h; omega); interval_cases j <;> rfl)
      (by intro j h t; change j < 9 at h; interval_cases j <;> rfl)
      (by intro j h; change j < 9 at h; interval_cases j <;> rfl)
  rw [show 10 + fuel = 1 + (9 + fuel) by omega, jumpRun, run_ops_singleton, headRun]
  simp only [bind_assoc, pure_bind, charge_charge, Nat.reduceAdd]

theorem run_mid (T : MachineState) (pc : T.pc = opPC 1476) (fuel : Nat) (coins : Bool) :
    execute openingImage (5 + fuel) T coins =
      (do let res ← execute openingImage fuel (midState T) coins; return res.charge 5 0) :=
  alu_run T 1476 midOps fuel coins pc (by decide)
    (by intro j h; change j < 5 at h; interval_cases j <;> rfl)
    (by intro j h t; have hj : j < 4 := (by change j + 1 < 5 at h; omega); interval_cases j <;> rfl)
    (by intro j h t; change j < 5 at h; interval_cases j <;> rfl)
    (by intro j h; change j < 5 at h; interval_cases j <;> rfl)

theorem run_tail (V : MachineState) (pc : V.pc = opPC 1503) (fuel : Nat) (coins : Bool) :
    execute openingImage (2 + fuel) V coins =
      (do let res ← execute openingImage fuel (tailState V) coins; return res.charge 2 0) :=
  alu_run V 1503 tailOps fuel coins pc (by decide)
    (by intro j h; change j < 2 at h; interval_cases j <;> rfl)
    (by intro j h t; have hj : j < 1 := (by change j + 1 < 2 at h; omega); interval_cases j <;> rfl)
    (by intro j h t; change j < 2 at h; interval_cases j <;> rfl)
    (by intro j h; change j < 2 at h; interval_cases j <;> rfl)

/-! ### The whole pre-pass, from word 12 to word 13 -/

def prePass (card : Nat) (idx : Nat → Nat) (Q : MachineState) : OracleComp World MachineState := do
  let T ← pass1Loop (memoryView Q) idx card 0 (headState Q)
  pure (tailState (iterState (fun _ => p2Next) card 0 (midState T)))

def prepassSteps (card : Nat) : Nat := 10 + 32 * card + 5 + 22 * card + 2
def prepassCycles (card : Nat) : Nat := 10 + 61 * card + 5 + 22 * card + 2

/-- What the pre-pass needs of the state after the leader's first twelve setup words. -/
structure PreReady (Q : MachineState) (card : Nat) (idx : Nat → Nat) : Prop where
  pc : Q.pc = opPC 12
  x8 : Q.getReg .x8 = BitVec.ofNat 64 Opening.indicesBase
  x9 : Q.getReg .x9 = BitVec.ofNat 64 Opening.trapdoorBase
  x16 : Q.getReg .x16 = BitVec.ofNat 64 card
  x18 : Q.getReg .x18 = BitVec.ofNat 64 card
  x22 : Q.getReg .x22 = BitVec.ofNat 64 (Opening.trapdoorBase + 80 * LENGTH)
  idxMem : ∀ j < card, memoryView Q (IW + j) = BitVec.ofNat 64 (idx j)
  idxSmall : ∀ j < card, idx j < LENGTH
  idxInj : ∀ j < card, ∀ j' < card, idx j = idx j' → j = j'
  positive : 0 < card
  cardBound : card ≤ LENGTH

/-- The state at word 13 after the pre-pass, for the answers `ys`. -/
structure PreEnd (Q : MachineState) (card : Nat) (idx : Nat → Nat) (ys : Nat → Sampling.Block) (P : MachineState) :
    Prop where
  pc : P.pc = 0x1034
  x27 : P.getReg .x27 = 256
  keep : ∀ g, g ≠ .x5 → g ≠ .x6 → g ≠ .x7 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 → g ≠ .x13 → g ≠ .x14 → g ≠ .x15 →
    g ≠ .x16 → g ≠ .x17 → g ≠ .x27 → g ≠ .x28 → g ≠ .x29 → g ≠ .x30 → g ≠ .x31 → P.getReg g = Q.getReg g
  salt : ∀ j < card, ∀ t < 2, memoryView P (NW + 2 * idx j + t) = listVal (memoryView Q) (ys j) (idx j) t
  mate : ∀ j < card, ∀ t < 4,
    memoryView P (HW + 4 * (idx j ^^^ 1) + t) = listVal (memoryView Q) (ys j) (idx j) (2 + t)
  frame : ∀ w < 2 ^ 33, (w < scratchW ∨ scratchW + 25 ≤ w) → (w < Lw 0 ∨ Lw card ≤ w) →
    (∀ j < card, w ≠ NW + 2 * idx j ∧ w ≠ NW + 2 * idx j + 1) →
    (∀ j < card, ∀ t < 4, w ≠ HW + 4 * (idx j ^^^ 1) + t) → memoryView P w = memoryView Q w

theorem salts_word : wordAddress NW = BitVec.ofNat 64 (Opening.trapdoorBase + 80 * LENGTH) := by
  unfold wordAddress NW TDw; norm_num [Opening.trapdoorBase, LENGTH, LOG_LENGTH]

theorem pre_inv0 (Q : MachineState) (card : Nat) (idx : Nat → Nat) (r : PreReady Q card idx) :
    P1Inv Q (headState Q) 0 card idx (fun _ => 0) := by
  obtain ⟨h14, h11, h12, h13, h5, h15, h17, hmem, hpc, hkeep⟩ := head_facts Q r.pc r.x8 r.x9
  refine ⟨by rw [if_neg (by have := r.positive; omega)]; exact hpc, h14, h15, h17, ?_, h11, h12, h13, h5,
    fun g a b c d e f h i j l m n o p => hkeep g a e f h i j m, ?_, fun j hj => absurd hj (Nat.not_lt_zero _),
    r.idxMem, r.idxSmall, Nat.zero_le _, r.cardBound⟩
  · rw [hkeep .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r.x16,
      Nat.sub_zero]
  · intro w _ _ _
    rw [memoryView_congr hmem]

theorem pre_inv2 (Q : MachineState) (card : Nat) (idx : Nat → Nat) (r : PreReady Q card idx)
    (T : MachineState) (ys : Nat → Sampling.Block) (inv : P1Inv Q T card card idx ys) :
    P2Inv (midState T) (midState T) 0 card idx := by
  have hc := r.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have iwv : IW = 1023411204 := rfl
  have t8 : T.getReg .x8 = BitVec.ofNat 64 Opening.indicesBase :=
    (inv.keep .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.x8
  have t9 : T.getReg .x9 = BitVec.ofNat 64 Opening.trapdoorBase :=
    (inv.keep .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.x9
  have t18 : T.getReg .x18 = BitVec.ofNat 64 card :=
    (inv.keep .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.x18
  have t22 : T.getReg .x22 = BitVec.ofNat 64 (Opening.trapdoorBase + 80 * LENGTH) :=
    (inv.keep .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.x22
  have tpc : T.pc = opPC 1476 := by rw [inv.pc, if_pos rfl]
  obtain ⟨m14, m16, m17, m15, mmem, mpc, mkeep⟩ := mid_facts T tpc t8 t9
  refine ⟨by rw [if_neg (by have := r.positive; omega)]; exact mpc, m14, m17, by rw [m16, t18]; rfl,
    fun g _ _ _ _ _ _ => rfl, m15, ?_, fun w _ _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
    fun j hj => absurd hj (Nat.not_lt_zero _), ?_, r.idxSmall, r.idxInj, Nat.zero_le _, hc⟩
  · rw [mkeep .x22 (by decide) (by decide) (by decide) (by decide), t22, salts_word]
  · intro j hj
    rw [memoryView_congr mmem, inv.frame _ (by omega) (Or.inr (by unfold scratchW; omega))
      (Or.inr (by unfold Lw; omega))]
    exact r.idxMem j hj

theorem pre_end (Q : MachineState) (card : Nat) (idx : Nat → Nat) (r : PreReady Q card idx)
    (T : MachineState) (ys : Nat → Sampling.Block) (inv : P1Inv Q T card card idx ys) :
    PreEnd Q card idx ys (tailState (iterState (fun _ => p2Next) card 0 (midState T))) := by
  have hc := r.cardBound
  have len : LENGTH = 2 ^ 24 := rfl
  have tpc : T.pc = opPC 1476 := by rw [inv.pc, if_pos rfl]
  have t8 : T.getReg .x8 = BitVec.ofNat 64 Opening.indicesBase :=
    (inv.keep .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.x8
  have t9 : T.getReg .x9 = BitVec.ofNat 64 Opening.trapdoorBase :=
    (inv.keep .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans r.x9
  obtain ⟨_, _, _, _, mmem, _, mkeep⟩ := mid_facts T tpc t8 t9
  have inv2 := pass2_inv (midState T) card idx card 0 (midState T) (by omega) (pre_inv2 Q card idx r T ys inv)
  let V := iterState (fun _ => p2Next) card 0 (midState T)
  have vpc : V.pc = opPC 1503 := by rw [inv2.pc, if_pos rfl]
  obtain ⟨p27, pmem, ppc, pkeep⟩ := tail_facts V vpc
  have mview : memoryView (midState T) = memoryView T := memoryView_congr mmem
  refine ⟨ppc, p27, ?_, ?_, ?_, ?_⟩
  · intro g h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h27 h28 h29 h30 h31
    rw [pkeep g h27, inv2.keep g h6 h14 h16 h17 h30 h31, mkeep g h14 h15 h16 h17]
    exact inv.keep g h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h28 h29 h31
  · intro j hj t ht
    rw [memoryView_congr pmem, inv2.saltW j hj t ht, mview]
    exact inv.entries j hj t (by omega)
  · intro j hj t ht
    rw [memoryView_congr pmem, inv2.mateW j hj t ht, mview, Nat.add_assoc]
    exact inv.entries j hj (2 + t) (by omega)
  · intro w hw outS outL hs hm
    rw [memoryView_congr pmem, inv2.frame w hw hs hm, mview]
    exact inv.frame w hw outS outL

theorem prepass_run (Q : MachineState) (card : Nat) (idx : Nat → Nat) (r : PreReady Q card idx) (fuel : Nat)
    (coins : Bool) :
    execute openingImage (prepassSteps card + fuel) Q coins =
      (do let P ← prePass card idx Q
          let res ← execute openingImage fuel P coins
          return res.charge (prepassCycles card) card) := by
  have inv0 := pre_inv0 Q card idx r
  rw [show prepassSteps card + fuel = 10 + (32 * card + (5 + (22 * card + (2 + fuel)))) by unfold prepassSteps; omega,
    run_head Q r.pc, pass1_run Q card idx card 0 (headState Q) _ (by omega) inv0]
  simp only [prePass, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro T hT
  obtain ⟨ys, inv1⟩ := pass1_support Q card idx card 0 (headState Q) _ (by omega) inv0 T hT
  have tpc : T.pc = opPC 1476 := by rw [inv1.pc, if_pos rfl]
  have inv2 := pass2_inv (midState T) card idx card 0 (midState T) (by omega) (pre_inv2 Q card idx r T ys inv1)
  have vpc : (iterState (fun _ => p2Next) card 0 (midState T)).pc = opPC 1503 := by rw [inv2.pc, if_pos rfl]
  rw [run_mid T tpc, pass2_run (midState T) card idx card 0 (midState T) (by omega) (pre_inv2 Q card idx r T ys inv1),
    run_tail _ vpc]
  simp only [bind_assoc, pure_bind, charge_charge]
  rw [show 10 + 61 * card + (5 + (22 * card + 2)) = prepassCycles card by unfold prepassCycles; omega,
    show 0 + card + (0 + (0 + 0)) = card by omega]

theorem prepass_support (Q : MachineState) (card : Nat) (idx : Nat → Nat) (r : PreReady Q card idx)
    (P : MachineState) (reached : P ∈ support (prePass card idx Q)) : ∃ ys, PreEnd Q card idx ys P := by
  simp only [prePass, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨T, hT, rfl⟩ := reached
  obtain ⟨ys, inv1⟩ := pass1_support Q card idx card 0 (headState Q) _ (by omega) (pre_inv0 Q card idx r) T hT
  exact ⟨ys, pre_end Q card idx r T ys inv1⟩

/-- The honest answers of the fixed oracle. -/
def honestYs (oracle : Oracle) (M : Memory) (idx : Nat → Nat) (j : Nat) : Sampling.Block :=
  inverseAnswer oracle (packBuffer (window M (Rw + 25 * idx j)))

theorem prepass_fixed (oracle : Oracle) (Q : MachineState) (card : Nat) (idx : Nat → Nat) (r : PreReady Q card idx) :
    ∃ P : MachineState, fixedOracleRun oracle (prePass card idx Q) = pure P ∧
      PreEnd Q card idx (honestYs oracle (memoryView Q) idx) P := by
  obtain ⟨ys, inv1, honest⟩ := pass1_det_inv Q card idx (inverseAnswer oracle) card 0 (headState Q) (fun _ => 0)
    (by omega) (pre_inv0 Q card idx r) (fun j hj => absurd hj (Nat.not_lt_zero _))
  refine ⟨tailState (iterState (fun _ => p2Next) card 0
    (midState (iterState (p1Honest (inverseAnswer oracle) (memoryView Q) idx) card 0 (headState Q)))), ?_, ?_⟩
  · rw [prePass, fixed_oracle_run_bind, pass1_fixed, pure_bind, fixed_oracle_run_pure]
  · have e := pre_end Q card idx r _ ys inv1
    refine ⟨e.pc, e.x27, e.keep, ?_, ?_, e.frame⟩
    · intro j hj t ht; rw [e.salt j hj t ht, honest j hj]; rfl
    · intro j hj t ht; rw [e.mate j hj t ht, honest j hj]; rfl

end TwoPermutationPrototype.PackedOpening.Prepass

