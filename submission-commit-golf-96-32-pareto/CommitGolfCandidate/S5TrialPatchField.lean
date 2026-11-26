import CommitGolfCandidate.S5CapPairHead

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
open Reader (window)

attribute [local irreducible] S5.atProof S5.packedInput readBuffer S5.complete Reader.window

theorem last_field_word (x : CheckInput) (trial : Fin 4) (j : Nat) :
    (slotValue x trial 170).extractLsb' (64*j) 64 =
      W (window (S5.complete (S5.packedInput x) trial.val) (554940+64*j) (min (230-64*j) 64)) :=
  by
    have h:=Reader.field_slice (S5.complete (S5.packedInput x) trial.val) (515840+230*170) 230 j (by decide)
    unfold slotValue S5.batchView
    simp only [Reader.fieldSlice,Reader.decoded] at h
    rw [show 554940=515840+230*170 by decide]
    exact h

attribute [local irreducible] slotValue

theorem last_slot_low (x : CheckInput) (old new : Fin 4) (j : Nat) (small : j<3) :
    (slotValue x old 170).extractLsb' (64*j) 64 = (slotValue x new 170).extractLsb' (64*j) 64 := by
  let n:=554940+64*j
  let w:=min (230-64*j) 64
  have inside : n+w≤S5.wireBits:=by dsimp [n,w,S5.wireBits];omega
  rw [last_field_word x old j,last_field_word x new j,S5.before_cut _ old.val n w inside,S5.before_cut _ new.val n w inside]

end CommitGolfCandidate.S5Machine.Check
