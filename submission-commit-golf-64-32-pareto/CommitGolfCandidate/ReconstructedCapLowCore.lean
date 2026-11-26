import CommitGolfCandidate.ReconstructedCapWriter
import CommitGolfCandidate.ReconstructedCapLowStart

namespace CommitGolfCandidate.Reconstruction.CapLowCore
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut
open TwoPermutationPrototype (Memory writeWord)
open TwoPermutationPrototype.RV64

def changes (op : Op) (r : Reg) := match op with
  | .reg rd _ | .ld rd .. => rd==r
  | .sd .. => false

theorem sameReg (m : Model) (ops : List Op) (r : Reg) (keep : ops.any (fun op => changes op r)=false) :
    (after m ops).reg r=m.reg r := by
  induction ops generalizing m with
  | nil => rfl
  | cons op tail ih =>
    simp only [List.any_cons,Bool.or_eq_false_iff] at keep
    rw [show after m (op::tail)=after (op.apply m) tail from rfl,ih _ keep.2]
    cases op with
    | sd => rfl
    | reg rd e =>
      have h := beq_eq_false_iff_ne.mp keep.1
      change (if rd=r ∧ rd≠.x0 then _ else _) = _
      rw [ite_eq_right (fun z => h z.1)]
    | ld rd rs imm w =>
      have h := beq_eq_false_iff_ne.mp keep.1
      change (if rd=r ∧ rd≠.x0 then _ else _) = _
      rw [ite_eq_right (fun z => h z.1)]

def fixed : List Reg := [.x2,.x5,.x8,.x9,.x10,.x11,.x13,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x28,.x31]

structure Before (m : Model) (c : Nat) : Prop where
  cursor : m.reg .x7 = W c
  firstAddr : m.reg .x6 = wordAddress (cell c)
  secondCursor : m.reg .x15 = W (c+64)
  thirdCursor : m.reg .x30 = W (c+128)
  offset : m.reg .x26 = W (c%64)
  baseReg : m.reg .x17 = wordAddress base

def lowThree (m : Model) (c : Nat) : Memory :=
  put (put (put m.mem c 64 (m.reg .x14)) (c+64) 64 (m.reg .x1)) (c+128) 64 (m.reg .x16)

def top (m : Model) := m.reg .x27 &&& m.reg .x22

structure Prepared (m t : Model) (c : Nat) : Prop where
  memory : t.mem=lowThree m c
  regTop : t.reg .x30=top m
  firstWord : t.reg .x14=first t.mem (c+192) (top m)
  topAddr : t.reg .x16=wordAddress (cell (c+192))
  cursor : t.reg .x7=W (c+192)
  offset : t.reg .x26=W (c%64)
  keep : ∀ r∈fixed, t.reg r=m.reg r

theorem arrive (m : Model) (c : Nat) (bound : c<2^64) (cursor : m.reg .x7=W c) (baseReg : m.reg .x17=wordAddress base) :
    Before (after m CapLowStart.ops) c := by
  obtain ⟨off,dst,second,third,_,same⟩ := CapLowStart.values m c bound cursor baseReg
  exact ⟨(same _ (by decide) (by decide) (by decide) (by decide)).trans cursor,dst,second,third,off,
    (same _ (by decide) (by decide) (by decide) (by decide)).trans baseReg⟩

theorem room (c : Nat) (capacityOK : (c+192)/64<capacity) (k : Nat) (lim : k≤192) :
    cell (c+k)+1 < 2^33 := by unfold cell base;unfold capacity at capacityOK;omega

theorem next (c : Nat) : cell (c+64)=cell c+1 := by unfold cell;omega

end CommitGolfCandidate.Reconstruction.CapLowCore
