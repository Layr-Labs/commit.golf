import CommitGolfCandidate.GroupOpenCarryKernel

namespace TwoPermutationPrototype.GroupedOpening.Carry
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 PackedOpening Wide Shifted30
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

local macro "verifyCarryPlan" : tactic =>
  `(tactic| (
    simp only [Valid, validOp, update, assign, amount, Width.n,
      ite_true, ite_false, and_true, true_and, Nat.add_zero, Nat.zero_add,
      reduceCtorEq, Nat.reduceAdd, Nat.reduceMod, Nat.reduceLT, BitVec.reduceToNat]
    repeat' apply And.intro
    all_goals try omega
    all_goals intro i; fin_cases i <;>
      apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
      simp [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    all_goals first | rfl | omega | (interval_cases j <;> simp (disch := decide) [BitVec.getLsbD_of_ge])))


def s16r2 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .put .word .a,
   .shr .a .a 32,
   .ld .b 1,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .put .half .a]

theorem s16r2_valid (D : Nat → Word) (v : Values) : Valid D 2 16 0 v s16r2 := by
  unfold s16r2
  verifyCarryPlan

def s16r6 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .ld .b 1,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .put .word .a,
   .shr .a .a 32,
   .put .half .a]

theorem s16r6_valid (D : Nat → Word) (v : Values) : Valid D 6 16 0 v s16r6 := by
  unfold s16r6
  verifyCarryPlan

def s28r2 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .put .word .a,
   .shr .a .a 32,
   .ld .b 1,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .ld .b 2,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .put .half .a,
   .ld .a 3,
   .put .half .a,
   .shr .a .a 16,
   .put .half .a]

theorem s28r2_valid (D : Nat → Word) (v : Values) : Valid D 2 28 0 v s28r2 := by
  unfold s28r2
  verifyCarryPlan

def s28r6 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .ld .b 1,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .ld .b 2,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .ld .b 3,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .put .half .a]

theorem s28r6_valid (D : Nat → Word) (v : Values) : Valid D 6 28 0 v s28r6 := by
  unfold s28r6
  verifyCarryPlan

def s30r2 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .put .word .a,
   .shr .a .a 32,
   .ld .b 1,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .ld .b 2,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .ld .b 3,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a]

theorem s30r2_valid (D : Nat → Word) (v : Values) : Valid D 2 30 0 v s30r2 := by
  unfold s30r2
  verifyCarryPlan

def s30r6 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .ld .b 1,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .ld .b 2,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .ld .b 3,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .put .word .a]

theorem s30r6_valid (D : Nat → Word) (v : Values) : Valid D 6 30 0 v s30r6 := by
  unfold s30r6
  verifyCarryPlan

def s32r2 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .put .word .a,
   .shr .a .a 32,
   .ld .b 1,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .ld .b 2,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .ld .b 3,
   .shl .c .b 16,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 48,
   .put .half .a]

theorem s32r2_valid (D : Nat → Word) (v : Values) : Valid D 2 32 0 v s32r2 := by
  unfold s32r2
  verifyCarryPlan

def s32r6 : List Op :=
  [.ld .a 0,
   .put .half .a,
   .shr .a .a 16,
   .ld .b 1,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .ld .b 2,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .ld .b 3,
   .shl .c .b 48,
   .bor .a .a .c,
   .put .dword .a,
   .shr .a .b 16,
   .put .word .a,
   .shr .a .a 32,
   .put .half .a]

theorem s32r6_valid (D : Nat → Word) (v : Values) : Valid D 6 32 0 v s32r6 := by
  unfold s32r6
  verifyCarryPlan

end TwoPermutationPrototype.GroupedOpening.Carry
