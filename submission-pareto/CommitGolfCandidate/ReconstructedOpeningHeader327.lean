import CommitGolfCandidate.ReconstructedOpeningHeader318

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v327 (x : Context) : Word := (v238 x) >>> (1 : Nat)
def s328 (x : Context) := (s327 x).set .x11 (v327 x)
def v328 (x : Context) : Word := (v327 x) &&& signExtend12 4064
def s329 (x : Context) := (s328 x).set .x11 (v328 x)
def v329 (x : Context) : Word := (v328 x) ^^^ signExtend12 32
def s330 (x : Context) := (s329 x).set .x26 (v329 x)
def v330 (x : Context) : Word := basePtr x.index 18
def s331 (x : Context) := (s330 x).set .x26 (v330 x)
def v331 (x : Context) := top x 18
def s332 (x : Context) := (s331 x).set .x11 (v331 x)
def v332 (x : Context) : Word := (v326 x) >>> (53 : Nat)
def s333 (x : Context) := (s332 x).set .x12 (v332 x)
def v333 (x : Context) : Word := (v325 x) + (v332 x)
def s334 (x : Context) := (s333 x).set .x21 (v333 x)
def v334 (x : Context) : Word := (v333 x) * (v283 x)
def s335 (x : Context) := (s334 x).set .x14 (v334 x)
def v335 (x : Context) : Word := (v331 x) <<< (22 : Nat)
def s336 (x : Context) := (s335 x).set .x11 (v335 x)

def code327 : List Instr := [
  (Expr.instr .x11 (.srli .x10 1)),
  (Expr.instr .x11 (.andi .x11 4064)),
  (Expr.instr .x26 (.xori .x11 32)),
  (Expr.instr .x26 (.add .x26 .x22)),
  .LD .x11 .x26 600,
  (Expr.instr .x12 (.srli .x12 53)),
  (Expr.instr .x21 (.add .x16 .x12)),
  (Expr.instr .x14 (.mul .x21 .x13)),
  (Expr.instr .x11 (.slli .x11 22))]
theorem entries327 : OpeningStraight.Listed 327 code327 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span327 (o : Oracle) (x : Context) : Contract o code327 (s327 x) (s336 x) := by
  have h327 := OpeningLinear.register o (s327 x) .x11 (.srli .x10 1) (v327 x) rfl
  have h328 := OpeningLinear.register o (s328 x) .x11 (.andi .x11 4064) (v328 x) rfl
  have h329 := OpeningLinear.register o (s329 x) .x26 (.xori .x11 32) (v329 x) rfl
  have h330 := OpeningLinear.register o (s330 x) .x26 (.add .x26 .x22) (v330 x) (OpeningHeaderAddress.sibling_ptr x.index 18 (by decide))
  have h331 := OpeningLinear.read o (s331 x) .x11 .x26 600 (wordAt x.index 18 3) (top x 18) (by have := word_room x.index 18 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 18 3 600 rfl) (tree293 x 18 3 (by decide) (by decide) (by decide))
  have h332 := OpeningLinear.register o (s332 x) .x12 (.srli .x12 53) (v332 x) rfl
  have h333 := OpeningLinear.register o (s333 x) .x21 (.add .x16 .x12) (v333 x) rfl
  have h334 := OpeningLinear.register o (s334 x) .x14 (.mul .x21 .x13) (v334 x) rfl
  have h335 := OpeningLinear.register o (s335 x) .x11 (.slli .x11 22) (v335 x) rfl
  exact LeafModel.combine h327 (LeafModel.combine h328 (LeafModel.combine h329 (LeafModel.combine h330 (LeafModel.combine h331 (LeafModel.combine h332 (LeafModel.combine h333 (LeafModel.combine h334 (LeafModel.combine h335 (LeafModel.empty _ _)))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
