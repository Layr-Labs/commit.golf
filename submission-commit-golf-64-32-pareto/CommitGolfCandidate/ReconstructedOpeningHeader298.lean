import CommitGolfCandidate.ReconstructedOpeningHeader286

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v298 (x : Context) : Word := (v238 x) >>> (4 : Nat)
def s299 (x : Context) := (s298 x).set .x12 (v298 x)
def v299 (x : Context) : Word := (v298 x) &&& signExtend12 4064
def s300 (x : Context) := (s299 x).set .x12 (v299 x)
def v300 (x : Context) : Word := (v299 x) ^^^ signExtend12 32
def s301 (x : Context) := (s300 x).set .x15 (v300 x)
def v301 (x : Context) : Word := basePtr x.index 15
def s302 (x : Context) := (s301 x).set .x15 (v301 x)
def v302 (x : Context) := top x 15
def s303 (x : Context) := (s302 x).set .x12 (v302 x)
def v303 (x : Context) : Word := (v297 x) >>> (53 : Nat)
def s304 (x : Context) := (s303 x).set .x11 (v303 x)
def v304 (x : Context) : Word := (v296 x) + (v303 x)
def s305 (x : Context) := (s304 x).set .x29 (v304 x)
def v305 (x : Context) : Word := (0 : Word) + signExtend12 137
def s306 (x : Context) := (s305 x).set .x11 (v305 x)
def v306 (x : Context) : Word := (v304 x) * (v305 x)
def s307 (x : Context) := (s306 x).set .x24 (v306 x)
def v307 (x : Context) : Word := (v302 x) <<< (23 : Nat)
def s308 (x : Context) := (s307 x).set .x12 (v307 x)

def code298 : List Instr := [
  (Expr.instr .x12 (.srli .x10 4)),
  (Expr.instr .x12 (.andi .x12 4064)),
  (Expr.instr .x15 (.xori .x12 32)),
  (Expr.instr .x15 (.add .x15 .x22)),
  .LD .x12 .x15 504,
  (Expr.instr .x11 (.srli .x11 53)),
  (Expr.instr .x29 (.add .x9 .x11)),
  (Expr.instr .x11 (.addi .x0 137)),
  (Expr.instr .x24 (.mul .x29 .x11)),
  (Expr.instr .x12 (.slli .x12 23))]
theorem entries298 : OpeningStraight.Listed 298 code298 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span298 (o : Oracle) (x : Context) : Contract o code298 (s298 x) (s308 x) := by
  have h298 := OpeningLinear.register o (s298 x) .x12 (.srli .x10 4) (v298 x) rfl
  have h299 := OpeningLinear.register o (s299 x) .x12 (.andi .x12 4064) (v299 x) rfl
  have h300 := OpeningLinear.register o (s300 x) .x15 (.xori .x12 32) (v300 x) rfl
  have h301 := OpeningLinear.register o (s301 x) .x15 (.add .x15 .x22) (v301 x) (OpeningHeaderAddress.sibling_ptr x.index 15 (by decide))
  have h302 := OpeningLinear.read o (s302 x) .x12 .x15 504 (wordAt x.index 15 3) (top x 15) (by have := word_room x.index 15 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 15 3 504 rfl) (tree293 x 15 3 (by decide) (by decide) (by decide))
  have h303 := OpeningLinear.register o (s303 x) .x11 (.srli .x11 53) (v303 x) rfl
  have h304 := OpeningLinear.register o (s304 x) .x29 (.add .x9 .x11) (v304 x) rfl
  have h305 := OpeningLinear.register o (s305 x) .x11 (.addi .x0 137) (v305 x) rfl
  have h306 := OpeningLinear.register o (s306 x) .x24 (.mul .x29 .x11) (v306 x) rfl
  have h307 := OpeningLinear.register o (s307 x) .x12 (.slli .x12 23) (v307 x) rfl
  exact LeafModel.combine h298 (LeafModel.combine h299 (LeafModel.combine h300 (LeafModel.combine h301 (LeafModel.combine h302 (LeafModel.combine h303 (LeafModel.combine h304 (LeafModel.combine h305 (LeafModel.combine h306 (LeafModel.combine h307 (LeafModel.empty _ _))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
