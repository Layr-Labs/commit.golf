import CommitGolfCandidate.C3PCommitMeaning3
import CommitGolfCandidate.TwoPermutationInputWords

/-! # The paired commit under a fixed oracle: what each pair computes

A pair's two permutation inputs are `c3pPermInput` of its two leaves' original words and the two
halves of its draw; its two replies sit at `replyW + 50 k`. With the message words of the initial
state this gives every leaf's reply in the reply area. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64.C3Leaves (memoryView_congr addi_mem)
open CommitGolfCandidate (read_serialized_slice initial_input_byte inputByte)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000

/-! ### Pass-1 words -/

theorem p1_mem_ze (C : Compression) (M : Memory) (E w : Nat) (h : E + 24 ≤ w ∧ w < E + 28) :
    p1Mem C M E w = digestWords (zE C M E) ⟨w - (E + 24), by omega⟩ := by
  unfold p1Mem
  rw [write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega), write_window_at _ _ _ _ (by omega)]

theorem p1_mem_re (C : Compression) (M : Memory) (E w : Nat) (h : E + 28 ≤ w ∧ w < E + 32) :
    p1Mem C M E w = digestWords (rE C M E) ⟨w - (E + 28), by omega⟩ := by
  unfold p1Mem
  rw [write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
    write_window_at _ _ _ _ (by omega)]

theorem p1_mem_qo (C : Compression) (M : Memory) (E w : Nat) (h : E + 32 ≤ w ∧ w < E + 36) :
    p1Mem C M E w = digestWords (qO C M E) ⟨w - (E + 32), by omega⟩ := by
  unfold p1Mem
  rw [write_window_off _ _ _ _ (by omega), write_window_at _ _ _ _ (by omega)]

theorem p1_mem_zo (C : Compression) (M : Memory) (E w : Nat) (h : E + 36 ≤ w ∧ w < E + 40) :
    p1Mem C M E w = digestWords (zO C M E) ⟨w - (E + 36), by omega⟩ := by
  unfold p1Mem
  rw [write_window_at _ _ _ _ (by omega)]

/-! ### The honest answers are the model's -/

theorem qE_model (C : Compression) (M : Memory) (E : Nat) : qE C M E = c3pQ C (window M E) := by
  unfold qE c3pQ c3pQInput; congr 2

theorem rE_model (C : Compression) (M : Memory) (E : Nat) : rE C M E = c3pR C (window M E) := by
  unfold rE c3pR c3pRInput; congr 2; funext k; simp only [window, c3pRWords]; congr 1; omega

theorem zE_model (C : Compression) (M : Memory) (E : Nat) : zE C M E = c3pZ C (window M E) := by
  unfold zE c3pZ c3pZInput; rw [qE_model, rE_model]

theorem qO_model (C : Compression) (M : Memory) (E : Nat) : qO C M E = c3pQ C (window M (E + 32)) := by
  unfold qO c3pQ c3pQInput; congr 2

theorem rO_model (C : Compression) (M : Memory) (E : Nat) : rO C M E = c3pR C (window M (E + 32)) := by
  unfold rO c3pR c3pRInput; congr 2; funext k; simp only [window, c3pRWords]; congr 1; omega

theorem zO_model (C : Compression) (M : Memory) (E : Nat) : zO C M E = c3pZ C (window M (E + 32)) := by
  unfold zO c3pZ c3pZInput; rw [qO_model, rO_model]

/-! ### Salt halves -/

theorem salt_lo (a : BitVec 256) (t : Fin 2) : saltWords (pairSalt a false) t = digestWords a ⟨t.val, by omega⟩ := by
  have ht := t.isLt
  unfold saltWords pairSalt digestWords
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact BitVec.extractLsb'_extractLsb'_of_le (by omega)

theorem salt_hi (a : BitVec 256) (t : Fin 2) :
    saltWords (pairSalt a true) t = digestWords a ⟨2 + t.val, by omega⟩ := by
  have ht := t.isLt
  unfold saltWords pairSalt digestWords
  simp only [↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [BitVec.getLsbD_extractLsb', true_and_of inside, true_and_of (show 64 * t.val + bit < 128 by omega)]
  congr 1; omega

/-! ### The two permutation windows of a pair -/

theorem even_window (C : Compression) (a : BitVec 256) (M : Memory) (E j : Nat) (hj : j < 2 ^ 24)
    (hE : E = 512 + 32 * j) (ev : j % 2 = 0) :
    (window (p3M1 (writeWindow (p1Mem C M E) (E + 30) (digestWords a)) E) (E + 7) : Words 25) =
      c3pPermWords C ⟨j, hj⟩ (saltWords (pairSalt a false)) (window M E) := by
  have even : c3pEven ⟨j, hj⟩ := ev
  unfold c3pPermWords
  rw [if_pos even, ← zE_model, ← rE_model]
  funext ⟨k, hk⟩
  simp only [window, c3pEvenWords, p3M1]
  by_cases h1 : k < 17
  · rw [dif_pos h1, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
      p1_mem_frame _ _ _ _ (by omega)]
    congr 1; omega
  · rw [dif_neg h1]
    by_cases h2 : k < 21
    · rw [dif_pos h2, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
        p1_mem_ze _ _ _ _ (by omega)]
      congr 1; apply Fin.ext; simp only; omega
    · rw [dif_neg h2]
      by_cases h3 : k = 21
      · rw [if_pos h3, show E + 7 + k = E + 28 by omega, write_word_at]
        unfold c3pTag; rw [if_pos even]; unfold wordAddress; congr 1; simp only; omega
      · rw [if_neg h3]
        by_cases h4 : k = 22
        · rw [if_pos h4, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
            p1_mem_re _ _ _ _ (by omega)]
          congr 1; apply Fin.ext; simp only; omega
        · rw [if_neg h4, write_word_off _ _ _ _ (by omega), write_window_at _ _ _ _ (by omega), salt_lo]
          congr 1; apply Fin.ext; simp only; omega

theorem odd_window (C : Compression) (P : Sampling.Block → Sampling.Block) (a : BitVec 256) (M : Memory)
    (E D j : Nat) (hj : j < 2 ^ 24) (hE : E + 32 = 512 + 32 * j) (od : j % 2 = 1) (sep : E + 64 ≤ D) :
    (window (p3M3 P (writeWindow (p1Mem C M E) (E + 30) (digestWords a)) E D) (E + 32) : Words 25) =
      c3pPermWords C ⟨j, hj⟩ (saltWords (pairSalt a true)) (window M (E + 32)) := by
  have odd : ¬ c3pEven ⟨j, hj⟩ := by unfold c3pEven; simp only; omega
  unfold c3pPermWords
  rw [if_neg odd, ← zO_model, ← qO_model]
  funext ⟨k, hk⟩
  simp only [window, c3pOddWords, p3M3, p3M2, p3M1]
  by_cases h1 : k < 2
  · rw [dif_pos h1, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
      write_word_off _ _ _ _ (by omega), write_window_at _ _ _ _ (by omega), salt_hi]
    congr 1; apply Fin.ext; simp only; omega
  · rw [dif_neg h1]
    by_cases h2 : k = 2
    · rw [if_pos h2, show E + 32 + k = E + 34 by omega, write_word_at]
      unfold c3pTag; rw [if_neg odd]; unfold wordAddress; congr 1; simp only; omega
    · rw [if_neg h2]
      by_cases h3 : k = 3
      · rw [if_pos h3, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
          write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega), p1_mem_qo _ _ _ _ (by omega)]
        congr 1; apply Fin.ext; simp only; omega
      · rw [if_neg h3]
        by_cases h4 : k < 8
        · rw [dif_pos h4, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
            write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega), p1_mem_zo _ _ _ _ (by omega)]
          congr 1; apply Fin.ext; simp only; omega
        · rw [dif_neg h4, write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega),
            write_word_off _ _ _ _ (by omega), write_window_off _ _ _ _ (by omega), p1_mem_frame _ _ _ _ (by omega)]

/-! ### The two replies of a pair -/

theorem pair_reply_even (C : Compression) (P : Sampling.Block → Sampling.Block) (a : BitVec 256) (M : Memory)
    (E D j : Nat) (hj : j < 2 ^ 24) (hE : E = 512 + 32 * j) (ev : j % 2 = 0) (sep : E + 64 ≤ D) :
    (window (pairMem C P E D a M) D : Words 25) =
      replyWords (P (c3pPermInput C ⟨j, hj⟩ (saltWords (pairSalt a false)) (window M E))) := by
  funext ⟨k, hk⟩
  simp only [window]
  unfold pairMem p3Mem p3M3 p3M2
  rw [write_window_off _ _ _ _ (by omega), write_word_off _ _ _ _ (by omega), write_window_at _ _ _ _ (by omega)]
  unfold p3Y1 c3pPermInput
  rw [even_window C a M E j hj hE ev]
  congr 1; apply Fin.ext; simp only; omega

theorem pair_reply_odd (C : Compression) (P : Sampling.Block → Sampling.Block) (a : BitVec 256) (M : Memory)
    (E D j : Nat) (hj : j < 2 ^ 24) (hE : E + 32 = 512 + 32 * j) (od : j % 2 = 1) (sep : E + 64 ≤ D) :
    (window (pairMem C P E D a M) (D + 25) : Words 25) =
      replyWords (P (c3pPermInput C ⟨j, hj⟩ (saltWords (pairSalt a true)) (window M (E + 32)))) := by
  funext ⟨k, hk⟩
  simp only [window]
  unfold pairMem p3Mem
  rw [write_window_at _ _ _ _ (by omega)]
  unfold p3Y2 c3pPermInput
  rw [odd_window C P a M E D j hj hE od sep]
  congr 1; apply Fin.ext; simp only; omega

/-! ### Every leaf's reply -/

theorem flatten_get {α : Type} (n : Nat) : ∀ (wss : List (List α)) (g p : Nat), (∀ ws ∈ wss, ws.length = n) →
    p < n → wss.flatten[n * g + p]? = (wss[g]?.getD [])[p]? := by
  intro wss
  induction wss with
  | nil => intro g p _ _; simp
  | cons ws rest ih =>
    intro g p lens hp
    have hws : ws.length = n := lens ws (List.mem_cons_self ..)
    rw [List.flatten_cons]
    cases g with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega)]
      rfl
    | succ g =>
      have le : ws.length ≤ n * (g + 1) + p := by rw [hws, Nat.mul_succ]; omega
      rw [List.getElem?_append_right le, hws, show n * (g + 1) + p - n = n * g + p by rw [Nat.mul_succ]; omega,
        ih g p (fun w hw => lens w (List.mem_cons_of_mem _ hw)) hp]
      rfl

theorem paired_salt_at (wss : List (List (BitVec 256))) (len : wss.length = 8192) (lens : ∀ ws ∈ wss, ws.length = 1024)
    (j : Nat) (hj : j < 2 ^ 24) :
    pairedSaltTape wss.flatten ⟨j, hj⟩ =
      pairSalt ((wss[j / 2 / 1024]'(by omega))[j / 2 % 1024]?.getD 0) (j.testBit 0) := by
  have e := flatten_get 1024 wss (j / 2 / 1024) (j / 2 % 1024) lens (by omega)
  rw [show 1024 * (j / 2 / 1024) + j / 2 % 1024 = j / 2 by omega,
    List.getElem?_eq_getElem (show j / 2 / 1024 < wss.length by omega), Option.getD_some] at e
  unfold pairedSaltTape
  simp only
  rw [e]

/-- **Every leaf's reply** after the leaf phase, under a fixed oracle and given draws. -/
theorem leaf_reply (oracle : Oracle) (x8 x9 x19 : Word) (wss : List (List (BitVec 256))) (S : MachineState)
    (len : wss.length = 8192) (lens : ∀ ws ∈ wss, ws.length = 1024) (inv : LoopRegs S 0 x8 x9 x19)
    (j : Nat) (hj : j < 2 ^ 24) :
    (window (memoryView (leafDet oracle wss 0 S)) (replyW + 25 * j) : Words 25) =
      replyWords (oracle.permutation (c3pPermInput oracle.compression ⟨j, hj⟩
        (saltWords (pairedSaltTape wss.flatten ⟨j, hj⟩)) (window (memoryView S) (512 + 32 * j)))) := by
  obtain ⟨_, inside, _⟩ := leaf_det oracle x8 x9 x19 wss S len lens inv
  have hg : j / 2 / 1024 < 8192 := by omega
  have hp : j / 2 % 1024 < 1024 := by omega
  let g := j / 2 / 1024
  let p := j / 2 % 1024
  let a := (wss[g]'(by omega))[p]?.getD 0
  have hkg : 1024 * g + p = j / 2 := by omega
  have hEk : E0 g + 64 * p = 512 + 64 * (j / 2) := by unfold E0; omega
  have hDk : D0 g + 50 * p = replyW + 50 * (j / 2) := by unfold D0; omega
  have sep : E0 g + 64 * p + 64 ≤ D0 g + 50 * p := by rw [hEk, hDk]; unfold replyW; omega
  have pt : ∀ k < 25, memoryView (leafDet oracle wss 0 S) (replyW + 25 * j + k) =
      pairMem oracle.compression (fun x => oracle.permutation x) (E0 g + 64 * p) (D0 g + 50 * p) a
        (memoryView S) (replyW + 25 * j + k) := by
    intro k hk
    have mem : pairR (E0 g + 64 * p) (D0 g + 50 * p) (replyW + 25 * j + k) := Or.inr ⟨by omega, by omega⟩
    rw [inside g hg _ (pair_in_block g p _ hp mem), block_mem_pair _ _ g _ _ p _ hg hp mem]
  rw [paired_salt_at wss len lens j hj]
  by_cases ev : j % 2 = 0
  · have tb : j.testBit 0 = false := by rw [Nat.testBit_zero]; simp [ev]
    have hE : E0 g + 64 * p = 512 + 32 * j := by omega
    have pr := pair_reply_even oracle.compression (fun x => oracle.permutation x) a (memoryView S)
      (E0 g + 64 * p) (D0 g + 50 * p) j hj hE ev sep
    have wq : (window (memoryView (leafDet oracle wss 0 S)) (replyW + 25 * j) : Words 25) =
        window (pairMem oracle.compression (fun x => oracle.permutation x) (E0 g + 64 * p) (D0 g + 50 * p) a
          (memoryView S)) (D0 g + 50 * p) := by
      funext ⟨k, hk⟩
      simp only [window]
      rw [show D0 g + 50 * p + k = replyW + 25 * j + k by omega]
      exact pt k hk
    rw [wq, pr, tb, ← hE]
  · have tb : j.testBit 0 = true := by rw [Nat.testBit_zero]; simp; omega
    have od : j % 2 = 1 := by omega
    have hE : E0 g + 64 * p + 32 = 512 + 32 * j := by omega
    have pr := pair_reply_odd oracle.compression (fun x => oracle.permutation x) a (memoryView S)
      (E0 g + 64 * p) (D0 g + 50 * p) j hj hE od sep
    have wq : (window (memoryView (leafDet oracle wss 0 S)) (replyW + 25 * j) : Words 25) =
        window (pairMem oracle.compression (fun x => oracle.permutation x) (E0 g + 64 * p) (D0 g + 50 * p) a
          (memoryView S)) (D0 g + 50 * p + 25) := by
      funext ⟨k, hk⟩
      simp only [window]
      rw [show D0 g + 50 * p + 25 + k = replyW + 25 * j + k by omega]
      exact pt k hk
    rw [wq, pr, tb, ← hE]

/-! ### Memory of the setup and exit words -/

theorem lui_mem (s : MachineState) (rd : Reg) (imm : BitVec 20) : (execInstrBr s (.LUI rd imm)).mem = s.mem := by
  cases rd <;> rfl
theorem add_mem (s : MachineState) (rd a b : Reg) : (execInstrBr s (.ADD rd a b)).mem = s.mem := by
  cases rd <;> rfl
theorem slli_mem (s : MachineState) (rd a : Reg) (sh : BitVec 6) : (execInstrBr s (.SLLI rd a sh)).mem = s.mem := by
  cases rd <;> rfl

theorem first_state_mem (s : MachineState) : memoryView (firstState s) = memoryView s := by
  apply memoryView_congr
  rw [show firstState s = (runOpsC s setupOps).setPC (cpc blockStart) from rfl, set_pc_mem_c]
  simp only [runOpsC, setupOps, List.foldl, addi_mem, lui_mem, add_mem, slli_mem]

theorem exit_state_mem (t : MachineState) : memoryView (exitState t) = memoryView t := by
  apply memoryView_congr
  rw [show exitState t = (runOpsC t exitOps).setPC 217572 from rfl, set_pc_mem_c]
  simp only [runOpsC, exitOps, List.foldl, addi_mem, add_mem]

/-! ### Message words of the initial state -/

theorem paired_message_byte (s : Submission) (messageBase : s.layout.message = 4096) (msg : Message) (i : Index)
    (j : Nat) (hj : j < 256) :
    (s.initialState .commit msg).getByte (BitVec.ofNat 64 (4096 + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8 := by
  have n : i.val < 2 ^ 24 := i.isLt
  rw [initial_input_byte s .commit msg _ (by omega)]
  have selected : 4096 ≤ 4096 + 256 * i.val + j ∧ 4096 + 256 * i.val + j < 4096 + LENGTH * (LEAF_SIZE / 8) := by
    change _ ∧ _ < 4096 + 16777216 * 256; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, messageBase,
    selected, and_self, decide_true]
  have quotient : (4096 + 256 * i.val + j - 4096) / (LEAF_SIZE / 8) = i.val := by change _ / 256 = _; omega
  have remainder : (4096 + 256 * i.val + j - 4096) % (LEAF_SIZE / 8) = j := by change _ % 256 = _; omega
  simp only [quotient, remainder, i.isLt, dite_true]

theorem message_window (s : Submission) (messageBase : s.layout.message = 4096) (msg : Message) (j : Nat)
    (hj : j < 2 ^ 24) :
    (window (memoryView (s.initialState .commit msg)) (512 + 32 * j) : Words 32) = messageWords msg ⟨j, hj⟩ := by
  funext ⟨k, hk⟩
  simp only [window]
  rw [← read_word]
  have slice := read_serialized_slice (s.initialState .commit msg) (msg ⟨j, hj⟩) (8 * (512 + 32 * j + k)) (8 * k) 8
    (by
      intro t ht
      rw [show 8 * (512 + 32 * j + k) + t = 4096 + 256 * j + (8 * k + t) by omega]
      exact paired_message_byte s messageBase msg ⟨j, hj⟩ (8 * k + t) (by omega))
  rw [slice]
  simp only [messageWords]
  congr 1; omega

/-! ### Digests in the reply area -/

theorem slice_digest (x : BitVec 1600) (s : Nat) (h : s + 4 ≤ 25) :
    x.extractLsb' (64 * s) 256 = packDigestWords (fun k => replyWords x ⟨s + k.val, by omega⟩) := by
  apply digest_words_injective
  rw [digest_words_pack]
  funext k
  have hk := k.isLt
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [digestWords, replyWords, BitVec.getLsbD_extractLsb', true_and_of inside,
    true_and_of (show 64 * k.val + bit < 256 by omega)]
  congr 1; omega

/-- The parent input read at a pair's digests: the odd leaf's first 32 bytes above the even leaf's last
32 bytes. -/
theorem pair_parent_input (M : Memory) (D : Nat) (r0 r1 : BitVec 1600)
    (h0 : (window M D : Words 25) = replyWords r0) (h1 : (window M (D + 25) : Words 25) = replyWords r1) :
    packWords8 (window M (D + 21) : Words 8) = outputDigest r1 ++ c3pEvenDigest r0 := by
  unfold packWords8 outputDigest c3pEvenDigest
  congr 1
  · rw [show (0 : Nat) = 64 * 0 from rfl]
    erw [slice_digest r1 0 (by decide)]
    congr 1; funext k
    have e := congrFun h1 ⟨k.val, by omega⟩
    simp only [window] at e ⊢
    rw [show D + 21 + (k.val + 4) = D + 25 + k.val by omega, e]
    congr 1; apply Fin.ext; simp
  · erw [show (1344 : Nat) = 64 * 21 from rfl, slice_digest r0 21 (by decide)]
    congr 1; funext k
    have e := congrFun h0 ⟨21 + k.val, by omega⟩
    simp only [window] at e ⊢
    rw [show D + 21 + k.val = D + (21 + k.val) by omega, e]

end TwoPermutationPrototype.RV64.C3P
