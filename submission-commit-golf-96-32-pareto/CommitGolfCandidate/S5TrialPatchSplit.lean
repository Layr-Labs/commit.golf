import CommitGolfCandidate.S5TrialPatchField

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Reader (window)
attribute [local irreducible] S5.atProof S5.packedInput readBuffer S5.complete Reader.window slotValue

private theorem high_bits (v k : Nat) (q : Fin 4) :
    ((v%2^k+2^k*q.val)/2^k)%4=q.val := by
  rw [Nat.add_mul_div_left (v%2^k) q.val (Nat.two_pow_pos k),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k)),Nat.zero_add,Nat.mod_eq_of_lt q.isLt]

private theorem tail_window (v : Nat) (q : Fin 4) :
    window (S5.complete v q.val) S5.wireBits 2=q.val := by
  unfold window S5.complete
  exact high_bits v S5.wireBits q

private theorem split_window (v start : Nat) (q : Fin 4) (cut : start+36=S5.wireBits) :
    window (S5.complete v q.val) start (36+2)=window v start 36+2^36*q.val := by
  have low:=S5.before_cut v q.val start 36 cut.le
  have tail : window (S5.complete v q.val) (start+36) 2=q.val:=
    (congrArg (fun n=>window (S5.complete v q.val) n 2) cut).trans (tail_window v q)
  exact (Reader.append_window (S5.complete v q.val) start 36 2).trans
    (congrArg₂ (fun l r : Nat=>l+2^36*r) low tail)

theorem last_slot_split (x : CheckInput) (q : Fin 4) :
    (slotValue x q 170).extractLsb' 192 64 =
    W (window (S5.packedInput x) 555132 36+2^36*q.val) := by
  let v:=S5.packedInput x
  have h:=last_field_word x q 3
  have index:=congrArg₂ (fun b w : Nat=> W (window (S5.complete v q.val) b w))
    (show 554940+64*3=555132 by decide) (show min (230-64*3) 64=36+2 by decide)
  exact (h.trans index).trans (congrArg W (split_window v 555132 q (by decide)))

end CommitGolfCandidate.S5Machine.Check
