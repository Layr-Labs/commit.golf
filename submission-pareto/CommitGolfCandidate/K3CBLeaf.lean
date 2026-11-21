import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationBindingLeaf

/-!
# Word views of the K3-lite quartet window

The group call of quartet `g` reads the record window `0^72 ‖ d0 d1 d2 d3` (`quartetEncode`, the
payload `d3 ‖ d2 ‖ d1 ‖ d0` in bits `576..1600`): words `0..8` are zero and word `9 + 4 j + t` is
word `t` of the child `j` of the group.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

theorem reply_pack (v : BitVec 1600) : packBuffer (replyWords v)=v := by
  apply BitVec.eq_of_getLsbD_eq;intro k hk
  let j : Fin 25 := ⟨k/64,by omega⟩
  have h:=congrArg (fun w : BitVec 64 => w.getLsbD (k%64)) (packed_word (replyWords v) j)
  have b : k%64<64 := by omega
  unfold replyWords at h
  dsimp only [j] at h
  change ((packBuffer _).extractLsb' (64*(k/64)) 64).getLsbD (k%64) =
    (v.extractLsb' (64*(k/64)) 64).getLsbD (k%64) at h
  unfold replyWords
  simpa only [BitVec.getLsbD_extractLsb',b,decide_true,Bool.true_and,Nat.div_add_mod] using h

theorem bit_congr {n : Nat} (v : BitVec n) (p q : Nat) (h : p = q) : v.getLsbD p = v.getLsbD q := by rw [h]

theorem quad_word_zero (P : BitVec 1024) (w : Fin 25) (h : w.val<9) : replyWords (quartetEncode P) w = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [replyWords, quartetEncode, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    BitVec.getLsbD_append, show 64*w.val+b<576 by omega, ite_true]
  simp

theorem quad_word_leaf (a b c d : BitVec 256) (w : Fin 25) (h : 9≤w.val) :
    replyWords (quartetEncode (a ++ b ++ c ++ d)) w =
      ((if (w.val-9)/4 = 0 then d else if (w.val-9)/4 = 1 then c else if (w.val-9)/4 = 2 then b else a).extractLsb' (64*((w.val-9)%4)) 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro x hx
  have hw := w.isLt
  have lt : 64*((w.val-9)%4)+x < 256 := by omega
  simp only [replyWords, quartetEncode, BitVec.getLsbD_extractLsb', hx, decide_true, Bool.true_and,
    BitVec.getLsbD_append, show ¬ 64*w.val+x<576 by omega, ite_false]
  rcases (show (w.val-9)/4=0 ∨ (w.val-9)/4=1 ∨ (w.val-9)/4=2 ∨ (w.val-9)/4=3 by omega) with e|e|e|e <;>
  · simp only [e, ↓reduceIte, Nat.reduceEqDiff, BitVec.getLsbD_extractLsb', decide_true, Bool.true_and, lt]
    repeat' split
    all_goals first | omega | exact bit_congr _ _ _ (by omega)

end TwoPermutationPrototype.Grouped
