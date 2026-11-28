import CommitGolfCandidate.PentaGroupedCommitImage
import CommitGolfCandidate.QuadCommitGeometry
import CommitGolfCandidate.TwoPermutationProductionLeaf
import CommitGolfCandidate.TwoPermutationPackedLeafOps

/-! Symbolic action plans and address arithmetic for the 4,095-leaf penta counter-mode
leaf loop and its trailing leaf `i = 2^24 - 1`. -/
namespace TwoPermutationPrototype.PentaGrouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Quad.Commit
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def msgWord (i : Nat) : Nat := 512 + 32 * i
def groupBuffer (i : Nat) : Nat := msgWord (i - rank i) - 15
/-- Key block `K`: word `saltWord 0 = 763364356` (counter word at +0, 24-byte key at +1..3, zeros at +4..24). -/
def keyWord : Nat := saltWord 0
/-- Centered 45-leaf destination window pointer `x20`: `leafWord (45 * (i / 45)) + 192`. -/
def cursor (i : Nat) : Nat := leafWord (45 * (i / 45)) + 192
def sourceWord (i : Nat) : Nat := groupBuffer i + 2 * (rank i - 1)

def plan (i : Nat) : List Action :=
  let m := msgWord i
  let n := i % 4095
  [.offset .x12 .x10 (-32) (m - 4), .perm m (m - 4)] ++
  (if rank n = 0 then
    [.store .x24 .x10 0 keyWord, .offset .x12 .x10 (-120) (m - 15),
     .offset .x10 .x24 0 keyWord, .perm keyWord (m - 15)] ++
    (if n % 4095 = 4092 then [] else
      [.load .x14 .x12 128 (m - 15 + 16), .load .x15 .x12 136 (m - 15 + 17),
       .load .x16 .x12 144 (m - 15 + 18), .load .x17 .x12 152 (m - 15 + 19)]) ++
    [.offset .x10 .x12 176 (m + 7), .store .x10 .x10 0 (m + 7)]
  else [.offset .x10 .x10 56 (m + 7), .store .x10 .x10 0 (m + 7)] ++
     (if rank n ≤ 8 then [.load .x31 .x12 (sourceImm n) (sourceWord i), .store .x10 .x31 8 (m + 8),
                          .load .x31 .x12 (sourceImm n + 8) (sourceWord i + 1), .store .x10 .x31 16 (m + 9)]
      else if rank n = 9 then [.store .x10 .x14 8 (m + 8), .store .x10 .x15 16 (m + 9)]
      else [.store .x10 .x16 8 (m + 8), .store .x10 .x17 16 (m + 9)])) ++
  [.offset .x12 .x20 (slotImmediate n) (leafWord i), .perm (m + 7) (leafWord i),
   .offset .x10 .x10 200 (msgWord (i + 1))] ++
  (if rebase n then [.offset .x20 .x12 1776 (cursor (i + 1))] else [])

/-- Action plan for the trailing leaf `i = 16777215 = 2^24 - 1`. -/
def trailingPlan : List Action :=
  let i := 16777215
  let m := msgWord i
  [.offset .x12 .x10 (-32) (m - 4), .perm m (m - 4),
   .store .x24 .x10 0 keyWord, .offset .x12 .x10 (-120) (m - 15),
   .offset .x10 .x24 0 keyWord, .perm keyWord (m - 15),
   .offset .x10 .x12 176 (m + 7), .store .x10 .x10 0 (m + 7),
   .offset .x12 .x20 (slotImmediate 0) (leafWord i), .perm (m + 7) (leafWord i),
   .offset .x10 .x10 200 (msgWord (i + 1))]

theorem plan_words (i : Nat) : (plan i).map Action.op = packet (i % 4095) := by
  unfold plan packet; dsimp only
  split_ifs <;> rfl

theorem trailing_plan_words : trailingPlan.map Action.op = trailingPacket := rfl

theorem plan_fetch (i : Nat) : fetchOps (firstWord (i % 4095)) (plan i) := by
  intro j s pc
  have len := congrArg List.length (plan_words i)
  simp only [List.length_map] at len
  have inside : j.val < (packet (i % 4095)).length := len ▸ j.isLt
  have got := fetch_packet ⟨i % 4095, by omega⟩ j.val inside s pc
  rw [← plan_words, List.getElem?_eq_getElem (by simpa using j.isLt)] at got
  change fetch image s = some (.base (plan i)[j.val].op)
  simpa only [List.getElem_map, Option.getD_some] using got

theorem trailing_plan_fetch : fetchOps 45190 trailingPlan := by
  intro j s pc
  have inside : j.val < trailingPacket.length := by simpa [trailingPacket, trailingPlan] using j.isLt
  have got := fetch_trailing j.val inside s pc
  have eqOp : (trailingPacket[j.val]?).getD .EBREAK = trailingPlan[j.val].op := by
    rw [← trailing_plan_words, List.getElem?_map, List.getElem?_eq_getElem j.isLt]; rfl
  rwa [eqOp] at got

structure PacketRegs (s : MachineState) (i : Nat) : Prop where
  msg : s.getReg .x10 = wordAddress (msgWord i)
  heap : s.getReg .x20 = wordAddress (cursor i)
  counter : s.getReg .x24 = wordAddress keyWord
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1

theorem within_rank (i : Nat) : rank (i % 4095) = rank i := by
  unfold rank; rw [show i % 4095 % 4095 = i % 4095 by omega]

theorem within_period (i : Nat) : i % 4095 % 4095 = i % 4095 := by omega

theorem slot_immediate_mod (n : Nat) : slotImmediate (n % 4095) = slotImmediate n := by
  unfold slotImmediate
  rw [show n % 4095 % 45 = n % 45 by omega, show n % 4095 % 5 = n % 5 by omega]

theorem heap_address (i : Nat) :
    wordAddress (cursor i) + signExtend12 (slotImmediate (i % 4095)) = wordAddress (leafWord i) := by
  have tab : ∀ u : Fin 45,
      signExtend12 (slotImmediate u.val) =
        -(1536 : Word) + BitVec.ofNat 64 (368 * (u.val / 5) + 32 * (u.val % 5)) := by
    decide +kernel
  have h := tab ⟨i % 45, Nat.mod_lt i (by decide)⟩
  simp only [Fin.val_mk] at h
  rw [slot_immediate_mod]
  have immEq : slotImmediate i = slotImmediate (i % 45) := by
    unfold slotImmediate
    rw [show i % 45 % 45 = i % 45 by omega, show i % 45 % 5 = i % 5 by omega]
  rw [immEq, h]
  unfold cursor
  rw [wordAddress_add]
  change (wordAddress (leafWord (45 * (i / 45))) + 1536#64) +
    (-(1536 : Word) + BitVec.ofNat 64 (368 * (i % 45 / 5) + 32 * (i % 45 % 5))) = _
  have cancel : ∀ a b : Word, (a + 1536#64) + (-(1536 : Word) + b) = a + b := by intro a b; bv_omega
  rw [cancel]
  unfold wordAddress leafWord groupWord
  rw [← BitVec.ofNat_add]
  congr 1
  have hdiv : i / 5 = 9 * (i / 45) + (i % 45) / 5 := by omega
  have hmod : i % 5 = (i % 45) % 5 := by omega
  have h45 : 45 * (i / 45) / 5 = 9 * (i / 45) := by omega
  have h45m : 45 * (i / 45) % 5 = 0 := by omega
  rw [hdiv, hmod, h45, h45m]
  omega

theorem rebase_cursor (i : Nat) (h : rebase (i % 4095)) :
    wordAddress (leafWord i) + signExtend12 1776 = wordAddress (cursor (i + 1)) := by
  have mod45 : i % 45 = 44 := by
    unfold rebase rb at h
    omega
  change wordAddress (leafWord i) + BitVec.ofNat 64 1776 = wordAddress (cursor (i + 1))
  unfold wordAddress
  rw [← BitVec.ofNat_add]
  congr 1
  unfold cursor leafWord groupWord
  omega

theorem no_rebase_cursor (i : Nat) (h : ¬rebase (i % 4095)) : cursor (i + 1) = cursor i := by
  have mod45 : i % 45 ≠ 44 := by
    intro eq; apply h; unfold rebase rb; omega
  unfold cursor
  rw [show (i + 1) / 45 = i / 45 by omega]

theorem src_address (i : Nat) (d : Fin 2) (lo : 0 < rank i) (hi : rank i ≤ 8) :
    wordAddress (msgWord i - 4) + signExtend12 (sourceImm (i % 4095) + BitVec.ofNat 12 (8 * d.val)) =
      wordAddress (sourceWord i + d.val) := by
  have tab : ∀ r : Fin 9, ∀ j : Fin 2,
    signExtend12 (BitVec.ofNat 12 (3992 - 240 * r.val) + BitVec.ofNat 12 (8 * j.val)) =
      -(BitVec.ofNat 64 (104 + 240 * r.val - 8 * j.val)) := by decide +kernel
  have h := tab ⟨rank i, by omega⟩ d
  simp only [Fin.val_mk] at h
  unfold sourceImm; rw [within_rank, h]
  have bd : rank i ≤ i := by
    unfold rank; have := Nat.mod_le (i % 4095) 11; have := Nat.mod_le i 4095; omega
  have m : 8 * (msgWord i - 4) = 8 * (sourceWord i + d.val) + (104 + 240 * rank i - 8 * d.val) := by
    have dj := d.isLt; unfold sourceWord groupBuffer msgWord; omega
  unfold wordAddress
  rw [m, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_neg_eq_sub, BitVec.sub_self, BitVec.add_zero]

private theorem word_disp (i : Nat) (d : Nat) : wordAddress i + BitVec.ofNat 64 (8 * d) = wordAddress (i + d) :=
  (wordAddress_add i d).symm

theorem packet_addrs (i : Nat) :
    wordAddress (msgWord i) + signExtend12 (-32) = wordAddress (msgWord i - 4) ∧
    wordAddress (msgWord i) + signExtend12 (-120) = wordAddress (msgWord i - 15) ∧
    wordAddress (msgWord i) + signExtend12 56 = wordAddress (msgWord i + 7) ∧
    wordAddress (msgWord i - 15) + signExtend12 176 = wordAddress (msgWord i + 7) ∧
    wordAddress (msgWord i + 7) + signExtend12 8 = wordAddress (msgWord i + 8) ∧
    wordAddress (msgWord i + 7) + signExtend12 16 = wordAddress (msgWord i + 9) ∧
    wordAddress (msgWord i + 7) + signExtend12 200 = wordAddress (msgWord (i + 1)) := by
  have m4 : msgWord i = (msgWord i - 4) + 4 := by unfold msgWord; omega
  have m15 : msgWord i = (msgWord i - 15) + 15 := by unfold msgWord; omega
  refine ⟨?_, ?_, word_disp (msgWord i) 7, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [m4, wordAddress_add]
    rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · conv_lhs => rw [m15, wordAddress_add]
    rw [BitVec.add_assoc]; exact BitVec.add_zero _
  · exact (word_disp (msgWord i - 15) 22).trans (congrArg wordAddress (by unfold msgWord; omega))
  · exact word_disp (msgWord i + 7) 1
  · exact word_disp (msgWord i + 7) 2
  · exact (word_disp (msgWord i + 7) 25).trans (congrArg wordAddress (by unfold msgWord; omega))

end TwoPermutationPrototype.PentaGrouped
