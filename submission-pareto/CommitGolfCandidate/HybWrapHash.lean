import CommitGolfCandidate.HybWrapTable
import CommitGolfCandidate.QuadCheckPentaInput
import CommitGolfCandidate.PentaGroupedContent

/-! The hashes of the 5-ary levels 14-16 (words 2697-2944). Level `L` node `j` hashes the group `j`
of level `L - 1` (zero prefix, children in slots 0-4) into slot `j % 5` of group `j / 5` of level
`L`; each level clears its ragged slots afterwards. The invariant `HashInv` keeps the nodes of the
finished levels, a zero 5-word prefix of every group and the memory outside the tables. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions
open TwoPermutationPrototype.PentaWrap (loaderReg proof_word proofWord)
open TwoPermutationPrototype.Quad.Checker (loaderReference packedImage pentaInputWords penta_input_word)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Groups of level `L` and their first word. -/
def groups (L : Nat) : Nat := (count L + 4) / 5
def groupW (L g : Nat) : Nat := HB L / 8 + 46*g
/-- First word of node `j` of level `L` (slot `j % 5` of group `j / 5`). -/
def slotW (L j : Nat) : Nat := groupW L (j/5) + 5 + 4*(j%5)

/-- End of the scratch tables (word). -/
def TEND : Nat := 33556502

theorem count_penta : ∀ L, 12 ≤ L → L ≤ 15 → count L = pentaCount L := by
  intro L h1 h2
  interval_cases L <;> decide

theorem count_half : ∀ L, 13 ≤ L → L ≤ 15 → count L = groups (L-1) := by
  intro L h1 h2
  interval_cases L <;> decide

theorem hb_val : ∀ L, 12 ≤ L → L ≤ 15 → HB L % 8 = 0 ∧ HB L / 8 + 46 * groups L ≤ TEND ∧
    33554432 ≤ HB L / 8 ∧ (L < 15 → HB (L+1) / 8 = HB L / 8 + 46 * groups L) := by
  intro L h1 h2
  interval_cases L <;> decide

theorem ragged_value : ∀ L, 13 ≤ L → L ≤ 15 → ragged L = 4*(5*groups L - count L) ∧
    ragged L ≤ 16 ∧ groups L = (count L + 4) / 5 := by
  intro L h1 h2
  interval_cases L <;> decide

/-- The upper nodes the wrapper recomputes, for the submitted input. -/
abbrev U (o : Oracle) (input : CheckInput) : Nat → Nat → BitVec 256 :=
  upNode o.permutation input.positions input.proof

structure HashInv (o : Oracle) (input : CheckInput) (L j : Nat) (t : MachineState) : Prop where
  slot : ∀ L', 12 ≤ L' → L' < L → ∀ j' < 5 * groups L', ∀ q < 4,
    memoryView t (slotW L' j' + q) = (U o input (L'-12) j').extractLsb' (64*q) 64
  cur : ∀ j' < j, ∀ q < 4, memoryView t (slotW L j' + q) = (U o input (L-12) j').extractLsb' (64*q) 64
  zero : ∀ L', 12 ≤ L' → L' ≤ 15 → ∀ g < groups L', ∀ i < 5, memoryView t (groupW L' g + i) = 0
  frame : ∀ w < 2^33, (w < 33554432 ∨ TEND ≤ w) → memoryView t w = memoryView (start input) w

/-! ### The children window -/

theorem window_penta (m : Memory) (src : Nat) (c : Fin 5 → BitVec 256)
    (words : ∀ i (h : i < 25), m (src+i) = pentaInputWords c ⟨i, h⟩) :
    packBuffer (window m src) = pentaInput c := by
  have e : window m src = replyWords (pentaInput c) := by
    funext i
    rw [window, words i.val i.isLt]
    exact (penta_input_word c i).symm
  rw [e]
  exact PentaGrouped.reply_pack (pentaInput c)

theorem extract_low (x : BitVec 1600) (q : Nat) (hq : q < 4) :
    (x.extractLsb' 0 256).extractLsb' (64*q) 64 = x.extractLsb' (64*q) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add]
  have c1 : decide (b < 64) = true := decide_eq_true hb
  have c2 : decide (64*q+b < 256) = true := decide_eq_true (by omega)
  simp only [c1, c2, Bool.true_and]

theorem reply_digest (π : Block → Block) (c : Fin 5 → BitVec 256) (q : Nat) (hq : q < 4) :
    (π (pentaInput c)).extractLsb' (64*q) 64 = (pentaFunction π c).extractLsb' (64*q) 64 :=
  (extract_low (π (pentaInput c)) q hq).symm

/-- The children of a level-`L` node `j` (`L ≥ 16`): nodes `5j … 5j+4` of `L - 1`. -/
def kids (o : Oracle) (input : CheckInput) (L j : Nat) : Fin 5 → BitVec 256 :=
  fun t => U o input (L-1-12) (5*j+t.val)

theorem up_succ (o : Oracle) (input : CheckInput) (L j : Nat) (h1 : 13 ≤ L) (h2 : L ≤ 15) (hj : j < count L) :
    U o input (L-12) j = pentaFunction o.permutation (kids o input L j) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = 13 + m := ⟨L-13, by omega⟩
  rw [show 13+m-12 = m+1 by omega]
  show upNode _ _ _ (m+1) j = _
  rw [upNode, if_pos (by rw [show 12+m+1 = 13+m by omega, ← count_penta _ (by omega) h2]; exact hj)]
  unfold kids
  rw [show 13+m-1-12 = m by omega]

/-- The 25 words of the level-`(L-1)` group `j` are the input of node `j` of level `L`. -/
theorem group_words (o : Oracle) (input : CheckInput) (L j : Nat) (t : MachineState) (h1 : 13 ≤ L) (h2 : L ≤ 15)
    (hj : j < count L) (inv : HashInv o input L 0 t) :
    ∀ i (h : i < 25), memoryView t (groupW (L-1) j + i) = pentaInputWords (kids o input L j) ⟨i, h⟩ := by
  intro i hi
  have half := count_half L h1 h2
  unfold pentaInputWords
  by_cases low : i < 5
  · rw [dif_pos low, inv.zero (L-1) (by omega) (by omega) j (by omega) i low]
  · rw [dif_neg low]
    simp only [kids]
    have node := inv.slot (L-1) (by omega) (by omega) (5*j+(i-5)/4) (by omega) ((i-5)%4) (by omega)
    have pos : slotW (L-1) (5*j+(i-5)/4) + (i-5)%4 = groupW (L-1) j + i := by
      unfold slotW
      rw [show (5*j+(i-5)/4)/5 = j by omega, show (5*j+(i-5)/4)%5 = (i-5)/4 by omega]
      omega
    rw [← pos, node]

theorem regions : ∀ L' L, 12 ≤ L' → L' < L → L ≤ 15 → HB L' / 8 + 46 * groups L' ≤ HB L / 8 := by
  intro L' L h1 h2 h3
  interval_cases L <;> interval_cases L' <;> decide

theorem write_window_at (m : Memory) (dst w : Nat) (vals : Words 25) :
    writeWindow m dst vals w = if h : dst ≤ w ∧ w < dst + 25 then vals ⟨w - dst, by omega⟩ else m w := rfl

/-! ### One hash call -/

def callImm (j : Nat) : BitVec 12 := if j % 5 = 4 then 240 else 32

def callOps (L j : Nat) : List Action :=
  [.perm (groupW (L-1) j) (slotW L j), .offset .x10 .x10 368 (BitVec.ofNat 64 (8*groupW (L-1) (j+1))),
   .offset .x12 .x12 (callImm j) (BitVec.ofNat 64 (8*slotW L (j+1)))]

theorem call_ops_op (L j : Nat) : (callOps L j).map Action.op = hashCall j := by
  unfold callOps hashCall callImm; split <;> rfl

/-- Registers during the hash calls of level `L`, before call `j`, from the table state `e`. -/
structure HashRegs (e : MachineState) (L j : Nat) (t : MachineState) : Prop where
  x10 : t.getReg .x10 = BitVec.ofNat 64 (8*groupW (L-1) j)
  x12 : t.getReg .x12 = BitVec.ofNat 64 (8*slotW L j)
  x5 : t.getReg .x5 = 0
  x11 : t.getReg .x11 = BitVec.ofNat 64 200
  x13 : t.getReg .x13 = BitVec.ofNat 64 1
  keep : ∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → t.getReg r = e.getReg r

theorem call_step (o : Oracle) (input : CheckInput) (e : MachineState) (L j : Nat) (h1 : 13 ≤ L) (h2 : L ≤ 15)
    (hj : j < count L) (t : MachineState) (inv : HashInv o input L j t) (zinv : HashInv o input L 0 t)
    (regs : HashRegs e L j t) :
    validFixed o (callOps L j) t ∧ HashInv o input L (j+1) (fixedOps o (callOps L j) t) ∧
      HashRegs e L (j+1) (fixedOps o (callOps L j) t) ∧
      (∀ L', L' ≠ L → ∀ j', HashInv o input L' j' t → HashInv o input L' j' (fixedOps o (callOps L j) t) ∨ True) := by
  have hb := hb_val L (by omega) h2
  have hbp := hb_val (L-1) (by omega) (by omega)
  have half := count_half L h1 h2
  have below := regions (L-1) L (by omega) (by omega) h2
  have gj : j / 5 < groups L := by unfold groups; omega
  let src := groupW (L-1) j
  let dst := slotW L j
  have srcB : src + 25 ≤ 2^33 := by
    show groupW (L-1) j + 25 ≤ 2^33; unfold groupW TEND at *; omega
  have dstB : dst + 25 ≤ 2^33 := by
    show slotW L j + 25 ≤ 2^33; unfold slotW groupW TEND at *; omega
  have dstIn : HB L / 8 ≤ dst ∧ dst + 25 ≤ HB L / 8 + 46 * groups L := by
    show HB L / 8 ≤ slotW L j ∧ slotW L j + 25 ≤ HB L / 8 + 46 * groups L
    unfold slotW groupW; constructor <;> omega
  let reply := o.permutation (packBuffer (window (memoryView t) src))
  have input_eq : packBuffer (window (memoryView t) src) = pentaInput (kids o input L j) :=
    window_penta _ _ _ (group_words o input L j t h1 h2 hj zinv)
  let p := fixedStep o t (.perm src dst)
  have pview : ∀ w < 2^33, memoryView p w =
      if h : dst ≤ w ∧ w < dst + 25 then replyWords reply ⟨w - dst, by omega⟩ else memoryView t w := by
    intro w hw
    rw [perm_view o t src dst w dstB hw, write_window_at]
  have preg : ∀ r, p.getReg r = t.getReg r := perm_reg o t src dst
  -- registers after the two pointer bumps
  have valid : validFixed o (callOps L j) t := by
    refine ⟨⟨?_, ?_, regs.x5, ?_, ?_, srcB, dstB⟩, ?_, ?_, trivial⟩
    · rw [regs.x10]; rfl
    · rw [regs.x12]; rfl
    · rw [regs.x11]; rfl
    · rw [regs.x13]; rfl
    · show p.getReg .x10 + signExtend12 368 = _
      rw [preg, regs.x10, show (368 : BitVec 12) = BitVec.ofNat 12 368 from rfl,
        add_small _ 368 (by decide) (by unfold groupW TEND at *; omega)]
      congr 1
    · show (putReg p .x10 _).getReg .x12 + signExtend12 (callImm j) = _
      rw [put_reg_reg, if_neg (by decide), preg, regs.x12]
      unfold callImm slotW groupW
      by_cases ev : j % 5 = 4
      · rw [if_pos ev, show (240 : BitVec 12) = BitVec.ofNat 12 240 from rfl,
          add_small _ 240 (by decide) (by unfold TEND at *; omega)]
        congr 1
        rw [show (j+1)/5 = j/5+1 by omega, show (j+1)%5 = 0 by omega, ev]; ring
      · rw [if_neg ev, show (32 : BitVec 12) = BitVec.ofNat 12 32 from rfl,
          add_small _ 32 (by decide) (by unfold TEND at *; omega)]
        congr 1
        rw [show (j+1)/5 = j/5 by omega, show (j+1)%5 = j%5+1 by omega]; ring
  have fin : fixedOps o (callOps L j) t =
      putReg (putReg p .x10 (BitVec.ofNat 64 (8*groupW (L-1) (j+1)))) .x12 (BitVec.ofNat 64 (8*slotW L (j+1))) := rfl
  have fview : ∀ w < 2^33, memoryView (fixedOps o (callOps L j) t) w = memoryView p w := by
    intro w _; rw [fin, put_reg_view, put_reg_view]
  refine ⟨valid, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun _ _ _ _ => Or.inr trivial⟩
  · intro L' hL' hL j' hj' q hq
    have hb' := hb_val L' hL' (by omega)
    have sep := regions L' L hL' hL h2
    have away : ¬ (dst ≤ slotW L' j' + q ∧ slotW L' j' + q < dst + 25) := by
      have : slotW L' j' + q < HB L' / 8 + 46 * groups L' := by unfold slotW groupW; omega
      omega
    rw [fview _ (by unfold slotW groupW TEND at *; omega), pview _ (by unfold slotW groupW TEND at *; omega),
      dif_neg away, inv.slot L' hL' hL j' hj' q hq]
  · intro j' hj' q hq
    rw [fview _ (by unfold slotW groupW TEND at *; omega), pview _ (by unfold slotW groupW TEND at *; omega)]
    by_cases same : j' = j
    · subst same
      rw [dif_pos ⟨by omega, by omega⟩]
      show reply.extractLsb' (64*(slotW L j' + q - slotW L j')) 64 = _
      rw [show slotW L j' + q - slotW L j' = q by omega]
      show (o.permutation (packBuffer (window (memoryView t) src))).extractLsb' (64*q) 64 = _
      rw [input_eq, reply_digest _ _ q hq, up_succ o input L j' h1 h2 hj]
    · have before : slotW L j' + 4 ≤ dst := by
        show slotW L j' + 4 ≤ slotW L j
        unfold slotW groupW
        have : j' < j := by omega
        omega
      rw [dif_neg (by omega), inv.cur j' (by omega) q hq]
  · intro L' hL' hL g hg i hi
    rw [fview _ (by have := hb_val L' hL' hL; unfold groupW TEND at *; omega),
      pview _ (by have := hb_val L' hL' hL; unfold groupW TEND at *; omega)]
    have away : ¬ (dst ≤ groupW L' g + i ∧ groupW L' g + i < dst + 25) := by
      by_cases same : L' = L
      · subst same
        show ¬ (slotW L' j ≤ groupW L' g + i ∧ groupW L' g + i < slotW L' j + 25)
        unfold slotW groupW
        by_cases gg : g = j/5
        · subst gg; omega
        · rcases Nat.lt_or_gt_of_ne gg with lt | gt
          · have : 46*g + 46 ≤ 46*(j/5) := by omega
            omega
          · have : 46*(j/5) + 46 ≤ 46*g := by omega
            omega
      · have hb' := hb_val L' hL' hL
        rcases Nat.lt_or_gt_of_ne same with lt | gt
        · have sep := regions L' L hL' lt h2
          have : groupW L' g + i < HB L' / 8 + 46 * groups L' := by unfold groupW; omega
          omega
        · have sep := regions L L' (by omega) gt hL
          have : HB L' / 8 ≤ groupW L' g + i := by unfold groupW; omega
          omega
    rw [dif_neg away, inv.zero L' hL' hL g hg i hi]
  · intro w hw out
    rw [fview w hw, pview w hw, dif_neg (by unfold TEND at *; omega), inv.frame w hw out]
  · rw [fin, put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  · rw [fin, put_reg_reg, if_pos ⟨rfl, by decide⟩]
  · rw [fin, put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), preg, regs.x5]
  · rw [fin, put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), preg, regs.x11]
  · rw [fin, put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), preg, regs.x13]
  · intro r a b c d f
    rw [fin, put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm), preg,
      regs.keep r a b c d f]

/-! ### One level -/

def hashOff : Nat → Nat
  | 13 => 1494 | 14 => 1603 | _ => 1640

def levelEnd (L : Nat) : Nat := hashOff L + 4 + 3 * count L + ragged L

theorem hash_codes : ∀ L, 13 ≤ L → L ≤ 15 →
    WrapAt (hashOff L) (liCode .x10 (HB (L-1)) ++ liCode .x12 (HB L + 40)) ∧
    (∀ j < count L, WrapAt (hashOff L + 4 + 3*j) (hashCall j)) ∧
    WrapAt (hashOff L + 4 + 3 * count L) (zeroStores .x12 (ragged L)) ∧
    (L < 15 → levelEnd L = hashOff (L+1)) ∧ (L = 15 → levelEnd L = 1662) ∧
    LiOK (HB (L-1)) ∧ LiOK (HB L + 40) := by
  intro L h1 h2
  interval_cases L <;> decide

theorem slot_zero_bytes (L : Nat) (h1 : 12 ≤ L) (h2 : L ≤ 15) : 8 * slotW L 0 = HB L + 40 := by
  have := hb_val L h1 h2
  unfold slotW groupW; omega

theorem group_zero_bytes (L : Nat) (h1 : 12 ≤ L) (h2 : L ≤ 15) : 8 * groupW L 0 = HB L := by
  have := hb_val L h1 h2
  unfold groupW; omega

theorem calls_run (o : Oracle) (input : CheckInput) (e : MachineState) (L : Nat) (h1 : 13 ≤ L) (h2 : L ≤ 15)
    (t₀ : MachineState) (pc₀ : t₀.pc = BitVec.ofNat 64 (4096+4*(464+(hashOff L + 4))))
    (inv₀ : HashInv o input L 0 t₀) (regs₀ : HashRegs e L 0 t₀) :
    ∀ j ≤ count L, ∃ t cycles rows, Obs o packedImage t₀ t (3*j) cycles j rows ∧ HashInv o input L j t ∧
      HashRegs e L j t ∧ t.pc = BitVec.ofNat 64 (4096+4*(464+(hashOff L + 4 + 3*j))) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨t₀, 0, [], Obs.refl o packedImage t₀, inv₀, regs₀, by simpa using pc₀⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, c, rows, obs, inv, regs, pc⟩ := ih (by omega)
    have zinv : HashInv o input L 0 t := ⟨inv.slot, fun _ h => absurd h (Nat.not_lt_zero _), inv.zero, inv.frame⟩
    obtain ⟨valid, inv', regs', _⟩ := call_step o input e L j h1 h2 (by omega) t inv zinv regs
    have code := (hash_codes L h1 h2).2.1 j (by omega)
    have ops := Obs.ops o packedImage (callOps L j) (464+(hashOff L + 4 + 3*j)) t pc
      (wrap_fetch_ops image_wrap code _ (call_ops_op L j)) valid
    have calls : opCalls (callOps L j) = 1 := rfl
    refine ⟨_, _, _, (obs.trans ops).cast (by simp [callOps]; ring) rfl (by rw [calls]) rfl, inv', regs', ?_⟩
    rw [fixed_ops_pc, pc_after _ _ _ pc]
    simp [callOps]; ring_nf

/-- Registers between hash levels. -/
structure HashBase (e : MachineState) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x11 : t.getReg .x11 = BitVec.ofNat 64 200
  x13 : t.getReg .x13 = BitVec.ofNat 64 1
  keep : ∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → t.getReg r = e.getReg r

theorem up_beyond (o : Oracle) (input : CheckInput) (L j : Nat) (h1 : 13 ≤ L) (h2 : L ≤ 15) (hj : count L ≤ j) :
    U o input (L-12) j = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = 13 + m := ⟨L-13, by omega⟩
  rw [show 13+m-12 = m+1 by omega]
  show upNode _ _ _ (m+1) j = _
  rw [upNode, if_neg (by rw [show 12+m+1 = 13+m by omega, ← count_penta _ (by omega) h2]; omega)]

theorem level_run (o : Oracle) (input : CheckInput) (e : MachineState) (L : Nat) (h1 : 13 ≤ L) (h2 : L ≤ 15)
    (t₀ : MachineState) (pc₀ : t₀.pc = BitVec.ofNat 64 (4096+4*(464+hashOff L)))
    (inv₀ : HashInv o input L 0 t₀) (base₀ : HashBase e t₀) :
    ∃ t cycles rows, Obs o packedImage t₀ t (levelEnd L - hashOff L) cycles (count L) rows ∧
      HashInv o input (L+1) 0 t ∧ HashBase e t ∧ t.pc = BitVec.ofNat 64 (4096+4*(464+levelEnd L)) := by
  obtain ⟨cSetup, cCalls, cClear, _, _, ok10, ok12⟩ := hash_codes L h1 h2
  obtain ⟨rv, rsmall, rgl⟩ := ragged_value L h1 h2
  have hb := hb_val L (by omega) h2
  -- the two constants
  obtain ⟨v₁, x10₁, keep₁, view₁⟩ := li_run o t₀ .x10 (HB (L-1)) ok10 (by decide)
  generalize hs₁ : fixedOps o (liActs .x10 (HB (L-1))) t₀ = s₁ at x10₁ keep₁ view₁
  obtain ⟨v₂, x12₂, keep₂, view₂⟩ := li_run o s₁ .x12 (HB L + 40) ok12 (by decide)
  generalize hs₂ : fixedOps o (liActs .x12 (HB L + 40)) s₁ = s₂ at x12₂ keep₂ view₂
  have split := wrap_at_split cSetup
  have obs₁ := Obs.free o packedImage (liActs .x10 (HB (L-1))) (464+hashOff L) t₀ pc₀
    (wrap_fetch_ops image_wrap split.1 _ rfl) v₁ (li_free _ _)
  rw [hs₁] at obs₁
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(464+(hashOff L+2))) := by
    rw [← hs₁, fixed_ops_pc, pc_after _ _ _ pc₀]; rfl
  have obs₂ := Obs.free o packedImage (liActs .x12 (HB L + 40)) (464+(hashOff L+2)) s₁ pc₁
    (wrap_fetch_ops image_wrap split.2 _ rfl) v₂ (li_free _ _)
  rw [hs₂] at obs₂
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*(464+(hashOff L+4))) := by
    rw [← hs₂, fixed_ops_pc, pc_after _ _ _ pc₁]; rfl
  have view : memoryView s₂ = memoryView t₀ := by rw [view₂, view₁]
  have inv₂ : HashInv o input L 0 s₂ :=
    ⟨fun L' a b j' c q d => by rw [view]; exact inv₀.slot L' a b j' c q d,
     fun _ h => absurd h (Nat.not_lt_zero _),
     fun L' a b g c i d => by rw [view]; exact inv₀.zero L' a b g c i d,
     fun w a b => by rw [view]; exact inv₀.frame w a b⟩
  have regs₂ : HashRegs e L 0 s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keep₂ .x10 (by decide), x10₁, group_zero_bytes (L-1) (by omega) (by omega)]
    · rw [x12₂, slot_zero_bytes L (by omega) h2]
    · rw [keep₂ .x5 (by decide), keep₁ .x5 (by decide), base₀.x5]
    · rw [keep₂ .x11 (by decide), keep₁ .x11 (by decide), base₀.x11]
    · rw [keep₂ .x13 (by decide), keep₁ .x13 (by decide), base₀.x13]
    · intro r a b c d f
      rw [keep₂ r d, keep₁ r b, base₀.keep r a b c d f]
  obtain ⟨t, c, rows, obsC, invC, regsC, pcC⟩ := calls_run o input e L h1 h2 s₂ pc₂ inv₂ regs₂ (count L) le_rfl
  have baseC : HashBase e t := ⟨regsC.x5, regsC.x11, regsC.x13, regsC.keep⟩
  have head := (obs₁.trans (obs₂.trans obsC))
  -- clear the ragged slots of the last group (none when the level fills its groups)
  have gl : groups L = (count L + 4) / 5 := rfl
  have hbL := hb_val L (by omega) h2
  have zIn : ragged L = 0 ∨ (HB L / 8 ≤ slotW L (count L) ∧ slotW L (count L) + ragged L ≤ HB L / 8 + 46 * groups L) := by
    unfold slotW groupW; rw [rv]; omega
  obtain ⟨vz, keepz, viewz⟩ := zero_run o t .x12 (slotW L (count L)) (ragged L) regsC.x12 (by omega)
    (by unfold slotW groupW TEND at *; omega)
  have obsZ := Obs.free o packedImage (zeroActs .x12 (slotW L (count L)) (ragged L)) (464+(hashOff L + 4 + 3 * count L)) t pcC
    (wrap_fetch_ops image_wrap cClear _ (zero_acts_op _ _ _)) vz (zero_free _ _ _)
  refine ⟨_, _, _, (head.trans obsZ).cast ?_ rfl (by simp) rfl, ?_, ?_, ?_⟩
  · simp [liActs, zero_acts_length, levelEnd]; omega
  · refine ⟨?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_, ?_⟩
    · intro L' hL' hL j' hj' q hq
      rw [viewz _ (by have := hb_val L' hL' (by omega); unfold slotW groupW TEND at *; omega)]
      by_cases same : L' = L
      · subst same
        by_cases late : count L' ≤ j'
        · have inZ : slotW L' (count L') ≤ slotW L' j' + q ∧ slotW L' j' + q < slotW L' (count L') + ragged L' := by
            unfold slotW groupW at *
            rw [rv]
            constructor <;> omega
          rw [if_pos inZ, up_beyond o input L' j' h1 h2 late]
          simp
        · have early : j' < count L' := by omega
          have : slotW L' j' + 4 ≤ slotW L' (count L') := by unfold slotW groupW; omega
          rw [if_neg (by omega), invC.cur j' early q hq]
      · have hb' := hb_val L' hL' (by omega)
        have sep := regions L' L hL' (by omega) h2
        have : slotW L' j' + q < HB L' / 8 + 46 * groups L' := by unfold slotW groupW; omega
        rw [if_neg (by omega), invC.slot L' hL' (by omega) j' hj' q hq]
    · intro L' hL' hL g hg i hi
      rw [viewz _ (by have := hb_val L' hL' hL; unfold groupW TEND at *; omega), if_neg ?_, invC.zero L' hL' hL g hg i hi]
      by_cases same : L' = L
      · subst same
        unfold slotW groupW at *
        rw [rv]
        have hc := Nat.div_add_mod (count L') 5
        have hm := Nat.mod_lt (count L') (show 0 < 5 by decide)
        rcases Nat.lt_or_ge g (count L' / 5) with hlt | hge
        · omega
        · have hg5 : g = count L' / 5 := by omega
          subst hg5
          by_cases z : count L' % 5 = 0
          · omega
          · omega
      · have hb' := hb_val L' hL' hL
        rcases Nat.lt_or_gt_of_ne same with lt | gt
        · have sep := regions L' L hL' lt h2
          have : groupW L' g + i < HB L' / 8 + 46 * groups L' := by unfold groupW; omega
          omega
        · have sep := regions L L' (by omega) gt hL
          have : HB L' / 8 ≤ groupW L' g + i := by unfold groupW; omega
          omega
    · intro w hw out
      rw [viewz w hw, if_neg (by unfold TEND at *; omega), invC.frame w hw out]
  · exact ⟨by rw [keepz]; exact baseC.x5, by rw [keepz]; exact baseC.x11, by rw [keepz]; exact baseC.x13,
      fun r a b c d f => by rw [keepz]; exact baseC.keep r a b c d f⟩
  · rw [fixed_ops_pc, pc_after _ _ _ pcC, zero_acts_length]
    unfold levelEnd; rw [Nat.add_assoc 464]

/-! ### The whole hash phase -/

theorem hash_setup_code : WrapAt 1491 hashSetup := by decide

def setupActs : List Action :=
  [.offset .x11 .x0 200 (BitVec.ofNat 64 200), .offset .x13 .x0 1 (BitVec.ofNat 64 1), .offset .x5 .x0 0 0]

theorem start_hash (o : Oracle) (input : CheckInput) (e t : MachineState) (tab : TableDone input e t) :
    HashInv o input 13 0 t := by
  have small := card_small input
  refine ⟨?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_, ?_⟩
  · intro L' h1 h2 j' hj' q hq
    have L14 : L' = 12 := by omega
    subst L14
    have hj : j' < 175 := by unfold groups count at hj'; omega
    have h14 : HB 12 / 8 = 33554432 := by decide
    have pos : slotW 12 j' + q = TW0+46*(j'/5)+4*(j'%5)+q := by unfold slotW groupW TW0; rw [h14]; omega
    rw [pos]
    by_cases real : j' < 175
    · rw [table_slot input e t tab j' q real hq,
        show proofWord + 90*input.positions.card + 4*j' + q = proofWord + (90*input.positions.card + 4*j' + q) by omega]
      show memoryView (loaderReference.initialState .check input) _ = _
      rw [proof_word loader_layout input _ (by unfold proofWord; omega)]
      show packWord input.proof (90*input.positions.card+4*j'+q) = _
      show _ = (upNode o.permutation input.positions input.proof 0 j').extractLsb' (64*q) 64
      rw [upNode, if_pos (by rw [show pentaCount 12 = 175 by decide]; exact real), tableNode,
        digest_at_word _ _ q (by omega) hq]
      congr 1; omega
    · exact absurd hj (by omega)
  · intro L' h1 h2 g hg i hi
    have hb := hb_val L' h1 h2
    have gb : groupW L' g + i < TEND := by unfold groupW at *; omega
    rw [tab.mem _ (by unfold TEND at gb; omega), if_neg ?_, scratch_zero input _ (by unfold groupW at *; omega)
      (by unfold TEND at gb; omega)]
    by_cases L14 : L' = 12
    · subst L14
      have h14 : HB 12 / 8 = 33554432 := by decide
      unfold groupW TW0
      rw [h14]
      omega
    · have h15 : HB 13 / 8 ≤ HB L' / 8 := by
        by_cases e15 : L' = 13
        · subst e15; exact le_rfl
        · have := regions 13 L' (by decide) (by omega) h2
          omega
      have : HB 13 / 8 = 33556042 := by decide
      unfold groupW TW0
      omega
  · intro w hw out
    rw [tab.mem w hw, if_neg (by unfold TW0 TEND at *; omega)]

theorem hash_phase (o : Oracle) (input : CheckInput) (e t : MachineState) (tab : TableDone input e t) :
    ∃ u cycles rows, Obs o packedImage t u 171 cycles 44 rows ∧ HashInv o input 16 0 u ∧ HashBase t u ∧
      u.pc = BitVec.ofNat 64 (4096+4*(464+1662)) := by
  have pcT : t.pc = BitVec.ofNat 64 (4096+4*(464+1491)) := by rw [tab.pc]
  have valid : validFixed o setupActs t := by
    refine ⟨?_, ?_, ?_, trivial⟩
    · show t.getReg .x0 + signExtend12 200 = _; rw [reg_zero]; decide
    · show (putReg t .x11 _).getReg .x0 + signExtend12 1 = _; rw [reg_zero]; decide
    · show (putReg (putReg t .x11 _) .x13 _).getReg .x0 + signExtend12 0 = _; rw [reg_zero]; decide
  have free : PermFree setupActs := by
    intro x hx; simp [setupActs] at hx; rcases hx with h | h | h <;> subst h <;> rfl
  have obsS := Obs.free o packedImage setupActs (464+1491) t pcT (wrap_fetch_ops image_wrap hash_setup_code _ rfl)
    valid free
  let s₀ := fixedOps o setupActs t
  have base₀ : HashBase t s₀ := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro r a b c d f
    show (putReg (putReg (putReg t .x11 _) .x13 _) .x5 _).getReg r = _
    rw [put_reg_reg, if_neg (fun h => a h.1.symm), put_reg_reg, if_neg (fun h => f h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm)]
  have view₀ : memoryView s₀ = memoryView t := by
    show memoryView (putReg (putReg (putReg t .x11 _) .x13 _) .x5 _) = _
    rw [put_reg_view, put_reg_view, put_reg_view]
  have inv₀ : HashInv o input 13 0 s₀ := by
    have h := start_hash o input e t tab
    exact ⟨fun L' a b j' c q d => by rw [view₀]; exact h.slot L' a b j' c q d,
      fun _ h => absurd h (Nat.not_lt_zero _),
      fun L' a b g c i d => by rw [view₀]; exact h.zero L' a b g c i d,
      fun w a b => by rw [view₀]; exact h.frame w a b⟩
  have pc₀ : s₀.pc = BitVec.ofNat 64 (4096+4*(464+hashOff 13)) := by
    rw [fixed_ops_pc, pc_after _ _ _ pcT]; rfl
  obtain ⟨u₁, _, _, o₁, i₁, b₁, p₁⟩ := level_run o input t 13 (by decide) (by decide) s₀ pc₀ inv₀ base₀
  rw [(hash_codes 13 (by decide) (by decide)).2.2.2.1 (by decide)] at p₁
  obtain ⟨u₂, _, _, o₂, i₂, b₂, p₂⟩ := level_run o input t 14 (by decide) (by decide) u₁ p₁ i₁ b₁
  rw [(hash_codes 14 (by decide) (by decide)).2.2.2.1 (by decide)] at p₂
  obtain ⟨u₃, _, _, o₃, i₃, b₃, p₃⟩ := level_run o input t 15 (by decide) (by decide) u₂ p₂ i₂ b₂
  rw [(hash_codes 15 (by decide) (by decide)).2.2.2.2.1 rfl] at p₃
  refine ⟨u₃, _, _, (obsS.trans (o₁.trans (o₂.trans o₃))).cast
    (by decide) rfl (by decide) rfl, i₃, b₃, p₃⟩

end TwoPermutationPrototype.HybWrap
