import CommitGolfCandidate.ReconstructedOpeningHeader298

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v308 (x : Context) : Word := (v238 x) >>> (3 : Nat)
def s309 (x : Context) := (s308 x).set .x11 (v308 x)
def v309 (x : Context) : Word := (v308 x) &&& signExtend12 4064
def s310 (x : Context) := (s309 x).set .x11 (v309 x)
def v310 (x : Context) : Word := (v309 x) ^^^ signExtend12 32
def s311 (x : Context) := (s310 x).set .x27 (v310 x)
def v311 (x : Context) : Word := basePtr x.index 16
def s312 (x : Context) := (s311 x).set .x27 (v311 x)
def v312 (x : Context) := top x 16
def s313 (x : Context) := (s312 x).set .x11 (v312 x)
def v313 (x : Context) : Word := (v307 x) >>> (56 : Nat)
def s314 (x : Context) := (s313 x).set .x12 (v313 x)
def v314 (x : Context) : Word := (v306 x) + (v313 x)
def s315 (x : Context) := (s314 x).set .x30 (v314 x)
def v315 (x : Context) : Word := (0 : Word) + signExtend12 1491
def s316 (x : Context) := (s315 x).set .x5 (v315 x)
def v316 (x : Context) : Word := (v314 x) * (v315 x)
def s317 (x : Context) := (s316 x).set .x1 (v316 x)
def v317 (x : Context) : Word := (v312 x) <<< (23 : Nat)
def s318 (x : Context) := (s317 x).set .x11 (v317 x)

def code308 : List Instr := [
  (Expr.instr .x11 (.srli .x10 3)),
  (Expr.instr .x11 (.andi .x11 4064)),
  (Expr.instr .x27 (.xori .x11 32)),
  (Expr.instr .x27 (.add .x27 .x22)),
  .LD .x11 .x27 536,
  (Expr.instr .x12 (.srli .x12 56)),
  (Expr.instr .x30 (.add .x24 .x12)),
  (Expr.instr .x5 (.addi .x0 1491)),
  (Expr.instr .x1 (.mul .x30 .x5)),
  (Expr.instr .x11 (.slli .x11 23))]
theorem entries308 : OpeningStraight.Listed 308 code308 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span308 (o : Oracle) (x : Context) : Contract o code308 (s308 x) (s318 x) := by
  have h308 := OpeningLinear.register o (s308 x) .x11 (.srli .x10 3) (v308 x) rfl
  have h309 := OpeningLinear.register o (s309 x) .x11 (.andi .x11 4064) (v309 x) rfl
  have h310 := OpeningLinear.register o (s310 x) .x27 (.xori .x11 32) (v310 x) rfl
  have h311 := OpeningLinear.register o (s311 x) .x27 (.add .x27 .x22) (v311 x) (OpeningHeaderAddress.sibling_ptr x.index 16 (by decide))
  have h312 := OpeningLinear.read o (s312 x) .x11 .x27 536 (wordAt x.index 16 3) (top x 16) (by have := word_room x.index 16 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 16 3 536 rfl) (tree293 x 16 3 (by decide) (by decide) (by decide))
  have h313 := OpeningLinear.register o (s313 x) .x12 (.srli .x12 56) (v313 x) rfl
  have h314 := OpeningLinear.register o (s314 x) .x30 (.add .x24 .x12) (v314 x) rfl
  have h315 := OpeningLinear.register o (s315 x) .x5 (.addi .x0 1491) (v315 x) rfl
  have h316 := OpeningLinear.register o (s316 x) .x1 (.mul .x30 .x5) (v316 x) rfl
  have h317 := OpeningLinear.register o (s317 x) .x11 (.slli .x11 23) (v317 x) rfl
  exact LeafModel.combine h308 (LeafModel.combine h309 (LeafModel.combine h310 (LeafModel.combine h311 (LeafModel.combine h312 (LeafModel.combine h313 (LeafModel.combine h314 (LeafModel.combine h315 (LeafModel.combine h316 (LeafModel.combine h317 (LeafModel.empty _ _))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
