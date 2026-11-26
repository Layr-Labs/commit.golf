import CommitGolfCandidate.ReconstructedOpeningHeader261

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v273 (x : Context) : Word := (v238 x) >>> (6 : Nat)
def s274 (x : Context) := (s273 x).set .x12 (v273 x)
def v274 (x : Context) : Word := (v273 x) &&& signExtend12 4064
def s275 (x : Context) := (s274 x).set .x12 (v274 x)
def v275 (x : Context) : Word := (v274 x) ^^^ signExtend12 32
def s276 (x : Context) := (s275 x).set .x5 (v275 x)
def v276 (x : Context) : Word := basePtr x.index 13
def s277 (x : Context) := (s276 x).set .x5 (v276 x)
def v277 (x : Context) : Word := (((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
def s278 (x : Context) := (s277 x).set .x12 (v277 x)
def v278 (x : Context) : Word := (68719476336 : Word) - (v277 x)
def s279 (x : Context) := (s278 x).set .x12 (v278 x)
def s280 (x : Context) := (s279 x).store 8589934266 (v276 x)
theorem tree280 (x : Context) (d w : Nat) (p : 0<d) (q : d≤24) (u : w<4) :
    (s280 x).mem (wordAt x.index d w)=x.initial.mem (wordAt x.index d w) := by
  have sep : wordAt x.index d w ≠ 8589934266 := by have := word_room x.index d w p q u;omega
  change (if wordAt x.index d w=8589934266 then _ else _) = _
  rw [if_neg sep]
  exact tree268 x d w p q u
def v280 (x : Context) := top x 13
def s281 (x : Context) := (s280 x).set .x12 (v280 x)
def v281 (x : Context) : Word := (v272 x) >>> (53 : Nat)
def s282 (x : Context) := (s281 x).set .x13 (v281 x)
def v282 (x : Context) : Word := (v271 x) + (v281 x)
def s283 (x : Context) := (s282 x).set .x11 (v282 x)
def v283 (x : Context) : Word := (0 : Word) + signExtend12 1677
def s284 (x : Context) := (s283 x).set .x13 (v283 x)
def v284 (x : Context) : Word := (v282 x) * (v283 x)
def s285 (x : Context) := (s284 x).set .x17 (v284 x)
def v285 (x : Context) : Word := (v280 x) <<< (24 : Nat)
def s286 (x : Context) := (s285 x).set .x12 (v285 x)

def code273 : List Instr := [
  (Expr.instr .x12 (.srli .x10 6)),
  (Expr.instr .x12 (.andi .x12 4064)),
  (Expr.instr .x5 (.xori .x12 32)),
  (Expr.instr .x5 (.add .x5 .x22)),
  (Expr.instr .x12 (.lui 1)),
  (Expr.instr .x12 (.sub .x8 .x12)),
  .SD .x12 .x5 1888,
  .LD .x12 .x5 440,
  (Expr.instr .x13 (.srli .x13 53)),
  (Expr.instr .x11 (.add .x11 .x13)),
  (Expr.instr .x13 (.addi .x0 1677)),
  (Expr.instr .x17 (.mul .x11 .x13)),
  (Expr.instr .x12 (.slli .x12 24))]
theorem entries273 : OpeningStraight.Listed 273 code273 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span273 (o : Oracle) (x : Context) : Contract o code273 (s273 x) (s286 x) := by
  have h273 := OpeningLinear.register o (s273 x) .x12 (.srli .x10 6) (v273 x) rfl
  have h274 := OpeningLinear.register o (s274 x) .x12 (.andi .x12 4064) (v274 x) rfl
  have h275 := OpeningLinear.register o (s275 x) .x5 (.xori .x12 32) (v275 x) rfl
  have h276 := OpeningLinear.register o (s276 x) .x5 (.add .x5 .x22) (v276 x) (OpeningHeaderAddress.sibling_ptr x.index 13 (by decide))
  have h277 := OpeningLinear.register o (s277 x) .x12 (.lui 1) (v277 x) rfl
  have h278 := OpeningLinear.register o (s278 x) .x12 (.sub .x8 .x12) (v278 x) rfl
  have h279 := OpeningLinear.write o (s279 x) .x12 .x5 1888 8589934266 (v276 x) (by decide) (by change ((v278 x) + signExtend12 1888)=wordAddress 8589934266; exact (by decide : ((68719476336 : Word)-(((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))+signExtend12 1888=wordAddress 8589934266)) rfl
  have h280 := OpeningLinear.read o (s280 x) .x12 .x5 440 (wordAt x.index 13 3) (top x 13) (by have := word_room x.index 13 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 13 3 440 rfl) (tree280 x 13 3 (by decide) (by decide) (by decide))
  have h281 := OpeningLinear.register o (s281 x) .x13 (.srli .x13 53) (v281 x) rfl
  have h282 := OpeningLinear.register o (s282 x) .x11 (.add .x11 .x13) (v282 x) rfl
  have h283 := OpeningLinear.register o (s283 x) .x13 (.addi .x0 1677) (v283 x) rfl
  have h284 := OpeningLinear.register o (s284 x) .x17 (.mul .x11 .x13) (v284 x) rfl
  have h285 := OpeningLinear.register o (s285 x) .x12 (.slli .x12 24) (v285 x) rfl
  exact LeafModel.combine h273 (LeafModel.combine h274 (LeafModel.combine h275 (LeafModel.combine h276 (LeafModel.combine h277 (LeafModel.combine h278 (LeafModel.combine h279 (LeafModel.combine h280 (LeafModel.combine h281 (LeafModel.combine h282 (LeafModel.combine h283 (LeafModel.combine h284 (LeafModel.combine h285 (LeafModel.empty _ _)))))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
