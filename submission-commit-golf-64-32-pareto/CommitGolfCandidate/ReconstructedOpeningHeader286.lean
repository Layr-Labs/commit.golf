import CommitGolfCandidate.ReconstructedOpeningHeader273

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v286 (x : Context) : Word := (v238 x) >>> (5 : Nat)
def s287 (x : Context) := (s286 x).set .x11 (v286 x)
def v287 (x : Context) : Word := (v286 x) &&& signExtend12 4064
def s288 (x : Context) := (s287 x).set .x11 (v287 x)
def v288 (x : Context) : Word := (v287 x) ^^^ signExtend12 32
def s289 (x : Context) := (s288 x).set .x23 (v288 x)
def v289 (x : Context) : Word := basePtr x.index 14
def s290 (x : Context) := (s289 x).set .x23 (v289 x)
def v290 (x : Context) : Word := (((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
def s291 (x : Context) := (s290 x).set .x11 (v290 x)
def v291 (x : Context) : Word := (68719476336 : Word) - (v290 x)
def s292 (x : Context) := (s291 x).set .x11 (v291 x)
def s293 (x : Context) := (s292 x).store 8589934265 (v289 x)
theorem tree293 (x : Context) (d w : Nat) (p : 0<d) (q : d≤24) (u : w<4) :
    (s293 x).mem (wordAt x.index d w)=x.initial.mem (wordAt x.index d w) := by
  have sep : wordAt x.index d w ≠ 8589934265 := by have := word_room x.index d w p q u;omega
  change (if wordAt x.index d w=8589934265 then _ else _) = _
  rw [if_neg sep]
  exact tree280 x d w p q u
def v293 (x : Context) := top x 14
def s294 (x : Context) := (s293 x).set .x11 (v293 x)
def v294 (x : Context) : Word := (v285 x) >>> (53 : Nat)
def s295 (x : Context) := (s294 x).set .x12 (v294 x)
def v295 (x : Context) : Word := (v284 x) + (v294 x)
def s296 (x : Context) := (s295 x).set .x17 (v295 x)
def v296 (x : Context) : Word := (v295 x) * (v283 x)
def s297 (x : Context) := (s296 x).set .x9 (v296 x)
def v297 (x : Context) : Word := (v293 x) <<< (24 : Nat)
def s298 (x : Context) := (s297 x).set .x11 (v297 x)

def code286 : List Instr := [
  (Expr.instr .x11 (.srli .x10 5)),
  (Expr.instr .x11 (.andi .x11 4064)),
  (Expr.instr .x23 (.xori .x11 32)),
  (Expr.instr .x23 (.add .x23 .x22)),
  (Expr.instr .x11 (.lui 1)),
  (Expr.instr .x11 (.sub .x8 .x11)),
  .SD .x11 .x23 1880,
  .LD .x11 .x23 472,
  (Expr.instr .x12 (.srli .x12 53)),
  (Expr.instr .x17 (.add .x17 .x12)),
  (Expr.instr .x9 (.mul .x17 .x13)),
  (Expr.instr .x11 (.slli .x11 24))]
theorem entries286 : OpeningStraight.Listed 286 code286 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span286 (o : Oracle) (x : Context) : Contract o code286 (s286 x) (s298 x) := by
  have h286 := OpeningLinear.register o (s286 x) .x11 (.srli .x10 5) (v286 x) rfl
  have h287 := OpeningLinear.register o (s287 x) .x11 (.andi .x11 4064) (v287 x) rfl
  have h288 := OpeningLinear.register o (s288 x) .x23 (.xori .x11 32) (v288 x) rfl
  have h289 := OpeningLinear.register o (s289 x) .x23 (.add .x23 .x22) (v289 x) (OpeningHeaderAddress.sibling_ptr x.index 14 (by decide))
  have h290 := OpeningLinear.register o (s290 x) .x11 (.lui 1) (v290 x) rfl
  have h291 := OpeningLinear.register o (s291 x) .x11 (.sub .x8 .x11) (v291 x) rfl
  have h292 := OpeningLinear.write o (s292 x) .x11 .x23 1880 8589934265 (v289 x) (by decide) (by change ((v291 x) + signExtend12 1880)=wordAddress 8589934265; exact (by decide : ((68719476336 : Word)-(((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))+signExtend12 1880=wordAddress 8589934265)) rfl
  have h293 := OpeningLinear.read o (s293 x) .x11 .x23 472 (wordAt x.index 14 3) (top x 14) (by have := word_room x.index 14 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 14 3 472 rfl) (tree293 x 14 3 (by decide) (by decide) (by decide))
  have h294 := OpeningLinear.register o (s294 x) .x12 (.srli .x12 53) (v294 x) rfl
  have h295 := OpeningLinear.register o (s295 x) .x17 (.add .x17 .x12) (v295 x) rfl
  have h296 := OpeningLinear.register o (s296 x) .x9 (.mul .x17 .x13) (v296 x) rfl
  have h297 := OpeningLinear.register o (s297 x) .x11 (.slli .x11 24) (v297 x) rfl
  exact LeafModel.combine h286 (LeafModel.combine h287 (LeafModel.combine h288 (LeafModel.combine h289 (LeafModel.combine h290 (LeafModel.combine h291 (LeafModel.combine h292 (LeafModel.combine h293 (LeafModel.combine h294 (LeafModel.combine h295 (LeafModel.combine h296 (LeafModel.combine h297 (LeafModel.empty _ _))))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
