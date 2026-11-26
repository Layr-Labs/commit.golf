import CommitGolfCandidate.ReconstructedOpeningHeader237

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v248 (x : Context) : Word := (v238 x) >>> (8 : Nat)
def s249 (x : Context) := (s248 x).set .x12 (v248 x)
def v249 (x : Context) : Word := (v248 x) &&& signExtend12 4064
def s250 (x : Context) := (s249 x).set .x12 (v249 x)
def v250 (x : Context) : Word := (v249 x) ^^^ signExtend12 32
def s251 (x : Context) := (s250 x).set .x12 (v250 x)
def v251 (x : Context) : Word := basePtr x.index 11
def s252 (x : Context) := (s251 x).set .x12 (v251 x)
def v252 (x : Context) : Word := (((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
def s253 (x : Context) := (s252 x).set .x13 (v252 x)
def v253 (x : Context) : Word := (68719476336 : Word) - (v252 x)
def s254 (x : Context) := (s253 x).set .x13 (v253 x)
def s255 (x : Context) := (s254 x).store 8589934268 (v251 x)
theorem tree255 (x : Context) (d w : Nat) (p : 0<d) (q : d≤24) (u : w<4) :
    (s255 x).mem (wordAt x.index d w)=x.initial.mem (wordAt x.index d w) := by
  have sep : wordAt x.index d w ≠ 8589934268 := by have := word_room x.index d w p q u;omega
  change (if wordAt x.index d w=8589934268 then _ else _) = _
  rw [if_neg sep]
  exact tree247 x d w p q u
def v255 (x : Context) := top x 11
def s256 (x : Context) := (s255 x).set .x12 (v255 x)
def v256 (x : Context) : Word := (v247 x) <<< (24 : Nat)
def s257 (x : Context) := (s256 x).set .x11 (v256 x)
def v257 (x : Context) : Word := (v256 x) >>> (53 : Nat)
def s258 (x : Context) := (s257 x).set .x11 (v257 x)
def v258 (x : Context) : Word := (0 : Word) + signExtend12 1325
def s259 (x : Context) := (s258 x).set .x14 (v258 x)
def v259 (x : Context) : Word := (v257 x) * (v258 x)
def s260 (x : Context) := (s259 x).set .x11 (v259 x)
def v260 (x : Context) : Word := (v255 x) <<< (24 : Nat)
def s261 (x : Context) := (s260 x).set .x12 (v260 x)

def code248 : List Instr := [
  (Expr.instr .x12 (.srli .x10 8)),
  (Expr.instr .x12 (.andi .x12 4064)),
  (Expr.instr .x12 (.xori .x12 32)),
  (Expr.instr .x12 (.add .x12 .x22)),
  (Expr.instr .x13 (.lui 1)),
  (Expr.instr .x13 (.sub .x8 .x13)),
  .SD .x13 .x12 1904,
  .LD .x12 .x12 376,
  (Expr.instr .x11 (.slli .x11 24)),
  (Expr.instr .x11 (.srli .x11 53)),
  (Expr.instr .x14 (.addi .x0 1325)),
  (Expr.instr .x11 (.mul .x11 .x14)),
  (Expr.instr .x12 (.slli .x12 24))]
theorem entries248 : OpeningStraight.Listed 248 code248 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span248 (o : Oracle) (x : Context) : Contract o code248 (s248 x) (s261 x) := by
  have h248 := OpeningLinear.register o (s248 x) .x12 (.srli .x10 8) (v248 x) rfl
  have h249 := OpeningLinear.register o (s249 x) .x12 (.andi .x12 4064) (v249 x) rfl
  have h250 := OpeningLinear.register o (s250 x) .x12 (.xori .x12 32) (v250 x) rfl
  have h251 := OpeningLinear.register o (s251 x) .x12 (.add .x12 .x22) (v251 x) (OpeningHeaderAddress.sibling_ptr x.index 11 (by decide))
  have h252 := OpeningLinear.register o (s252 x) .x13 (.lui 1) (v252 x) rfl
  have h253 := OpeningLinear.register o (s253 x) .x13 (.sub .x8 .x13) (v253 x) rfl
  have h254 := OpeningLinear.write o (s254 x) .x13 .x12 1904 8589934268 (v251 x) (by decide) (by change ((v253 x) + signExtend12 1904)=wordAddress 8589934268; exact (by decide : ((68719476336 : Word)-(((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))+signExtend12 1904=wordAddress 8589934268)) rfl
  have h255 := OpeningLinear.read o (s255 x) .x12 .x12 376 (wordAt x.index 11 3) (top x 11) (by have := word_room x.index 11 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 11 3 376 rfl) (tree255 x 11 3 (by decide) (by decide) (by decide))
  have h256 := OpeningLinear.register o (s256 x) .x11 (.slli .x11 24) (v256 x) rfl
  have h257 := OpeningLinear.register o (s257 x) .x11 (.srli .x11 53) (v257 x) rfl
  have h258 := OpeningLinear.register o (s258 x) .x14 (.addi .x0 1325) (v258 x) rfl
  have h259 := OpeningLinear.register o (s259 x) .x11 (.mul .x11 .x14) (v259 x) rfl
  have h260 := OpeningLinear.register o (s260 x) .x12 (.slli .x12 24) (v260 x) rfl
  exact LeafModel.combine h248 (LeafModel.combine h249 (LeafModel.combine h250 (LeafModel.combine h251 (LeafModel.combine h252 (LeafModel.combine h253 (LeafModel.combine h254 (LeafModel.combine h255 (LeafModel.combine h256 (LeafModel.combine h257 (LeafModel.combine h258 (LeafModel.combine h259 (LeafModel.combine h260 (LeafModel.empty _ _)))))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
