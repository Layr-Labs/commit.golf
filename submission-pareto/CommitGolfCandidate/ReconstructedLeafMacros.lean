import CommitGolfCandidate.ReconstructedLeafModel

namespace CommitGolfCandidate.Reconstruction.LeafMacros
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open LeafModel CommitWindows

theorem plus (base n : Nat) (imm : BitVec 12) (h : signExtend12 imm = wordAddress n) :
    wordAddress base + signExtend12 imm = wordAddress (base+n) := by rw [h,wordAddress_add]

theorem minus (base n : Nat) (imm : BitVec 12) (lo : n ≤ base)
    (h : wordAddress n + signExtend12 imm = 0) :
    wordAddress base + signExtend12 imm = wordAddress (base-n) := by
  calc
    _ = (wordAddress (base-n)+wordAddress n)+signExtend12 imm :=
      congrArg (·+signExtend12 imm) (by rw [← wordAddress_add,Nat.sub_add_cancel lo])
    _ = _ := by rw [BitVec.add_assoc,h]; exact BitVec.add_zero _

def rawCode : List Instr := [.ADDI .x10 .x10 200,.ADDI .x12 .x10 4064,.ECALL]
def rawState (o : Oracle) (m : Model) (src : Nat) : Model :=
  ((m.set .x10 (wordAddress src)).set .x12 (wordAddress (src-4))).permute o src (src-4)

/-- From the previous leaf's tag pointer, load the exact 200-byte raw prefix and
write its reply 32 bytes back from the entry pointer. -/
theorem raw_call (o : Oracle) (m : Model) (src : Nat) (lo : 25 ≤ src) (room : src+32 ≤ 2^33)
    (entry : m.reg .x10 = wordAddress (src-25)) (mode : m.reg .x5 = 0)
    (len : m.reg .x11 = 200) (kind : m.reg .x13 = 1) :
    Contract o rawCode m (rawState o m src) := by
  let a := m.set .x10 (wordAddress src)
  let b := a.set .x12 (wordAddress (src-4))
  have s1 : Contract o [.ADDI .x10 .x10 200] m a := LeafModel.addi _ _ _ _ _ _ (by
    rw [entry,plus (src-25) 25 _ rfl,Nat.sub_add_cancel lo])
  have s2 : Contract o [.ADDI .x12 .x10 4064] a b := LeafModel.addi _ _ _ _ _ _ (by
    change wordAddress src + _ = _; exact minus src 4 _ (by omega) rfl)
  have s3 : Contract o [.ECALL] b (rawState o m src) :=
    LeafModel.permutation _ _ _ _ (by omega) (by omega) rfl rfl mode len kind
  exact LeafModel.combine s1 (LeafModel.combine s2 s3)

def tapeCode (g : Fin 342) : List Instr :=
  [.ADDI .x12 .x10 3976,.ADDI .x10 .x8 (BitVec.ofNat 12 (4096-8*(g.val%16+1))),.ECALL]

def tapeState (o : Oracle) (m : Model) (src : Nat) (g : Fin 342) : Model :=
  ((m.set .x12 (wordAddress (src-15))).set .x10 (wordAddress (generatorBase-Generator.marker g))).permute
    o (generatorBase-Generator.marker g) (src-15)

private theorem gen_disp (g : Fin 342) :
    wordAddress (Generator.marker g) + signExtend12 (BitVec.ofNat 12 (4096-8*(g.val%16+1))) = 0 := by
  have tbl : ∀ k : Fin 16, wordAddress (1+k.val) + signExtend12
      (BitVec.ofNat 12 (4096-8*(k.val+1))) = 0 := by decide
  exact tbl ⟨g.val%16,by omega⟩

theorem generator_call (o : Oracle) (m : Model) (src : Nat) (g : Fin 342)
    (lo : 15 ≤ src) (room : src+32 ≤ 2^33) (entry : m.reg .x10 = wordAddress src)
    (base : m.reg .x8 = wordAddress generatorBase) (mode : m.reg .x5 = 0)
    (len : m.reg .x11 = 200) (kind : m.reg .x13 = 1) :
    Contract o (tapeCode g) m (tapeState o m src g) := by
  let a := m.set .x12 (wordAddress (src-15))
  let b := a.set .x10 (wordAddress (generatorBase-Generator.marker g))
  have sz : Generator.marker g ≤ 16 := by unfold Generator.marker; omega
  have s1 : Contract o [.ADDI .x12 .x10 3976] m a := LeafModel.addi _ _ _ _ _ _ (by
    rw [entry]; exact minus src 15 _ lo rfl)
  have s2 : Contract o [.ADDI .x10 .x8 (BitVec.ofNat 12 (4096-8*(g.val%16+1)))] a b := LeafModel.addi _ _ _ _ _ _ (by
    change m.reg .x8 + _ = _
    rw [base]
    exact minus _ _ _ (by unfold generatorBase; omega) (gen_disp g))
  have s3 : Contract o [.ECALL] b (tapeState o m src g) := LeafModel.permutation _ _ _ _
    (by unfold generatorBase; omega) (by omega) rfl rfl mode len kind
  exact LeafModel.combine s1 (LeafModel.combine s2 s3)

def finishCode (slot : Fin 63) : List Instr :=
  [.SB .x10 .x0 23,.ADDI .x12 .x19 (BitVec.ofNat 12 (32*slot.val)),.ECALL,.SH .x12 .x17 30]

def finishState (o : Oracle) (m : Model) (p dst : Nat) : Model :=
  let a := m.store (p+2) (m.mem (p+2) &&& 0x00ffffffffffffff)
  let b := (a.set .x12 (wordAddress dst)).permute o p dst
  b.store (dst+3) (b.mem (dst+3) ||| 0xffff000000000000)

theorem finish (o : Oracle) (m : Model) (p center : Nat) (slot : Fin 63)
    (room : p+25 ≤ 2^33) (destRoom : center+4*slot.val+25 ≤ 2^33)
    (src : m.reg .x10 = wordAddress p) (dst : m.reg .x19 = wordAddress center)
    (mode : m.reg .x5 = 0) (len : m.reg .x11 = 200) (kind : m.reg .x13 = 1) (tag : m.reg .x17 = -1) :
    Contract o (finishCode slot) m (finishState o m p (center+4*slot.val)) := by
  let dest := center+4*slot.val
  let a := m.store (p+2) (m.mem (p+2) &&& 0x00ffffffffffffff)
  let b := a.set .x12 (wordAddress dest)
  let c := b.permute o p dest
  have s1 : Contract o [.SB .x10 .x0 23] m a := clearByte _ _ _ _ _ (by omega) (by
    rw [src]
    change BitVec.ofNat 64 (8*p) + BitVec.ofNat 64 23 = _
    rw [← BitVec.ofNat_add]; congr 1 <;> omega)
  have s2 : Contract o [.ADDI .x12 .x19 (BitVec.ofNat 12 (32*slot.val))] a b := LeafModel.addi _ _ _ _ _ _ (by
    change m.reg .x19+_ = _
    rw [dst]
    have tbl : ∀ k : Fin 63, signExtend12 (BitVec.ofNat 12 (32*k.val)) = wordAddress (4*k.val) := by decide
    exact plus center (4*slot.val) _ (tbl slot))
  have s3 : Contract o [.ECALL] b c := LeafModel.permutation _ _ _ _ room destRoom src rfl mode len kind
  have s4 : Contract o [.SH .x12 .x17 30] c (finishState o m p dest) := markHalf _ _ _ _ _ _
    (by dsimp [dest]; omega) (by
      change BitVec.ofNat 64 (8*dest) + BitVec.ofNat 64 30 = _
      rw [← BitVec.ofNat_add]; congr 1 <;> omega) tag
  exact LeafModel.combine s1 (LeafModel.combine s2 (LeafModel.combine s3 s4))

end CommitGolfCandidate.Reconstruction.LeafMacros
