import CommitGolfCandidate.ReconstructedOpeningHeader248

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v261 (x : Context) : Word := (v238 x) >>> (7 : Nat)
def s262 (x : Context) := (s261 x).set .x13 (v261 x)
def v262 (x : Context) : Word := (v261 x) &&& signExtend12 4064
def s263 (x : Context) := (s262 x).set .x13 (v262 x)
def v263 (x : Context) : Word := (v262 x) ^^^ signExtend12 32
def s264 (x : Context) := (s263 x).set .x13 (v263 x)
def v264 (x : Context) : Word := basePtr x.index 12
def s265 (x : Context) := (s264 x).set .x13 (v264 x)
def v265 (x : Context) : Word := (((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)
def s266 (x : Context) := (s265 x).set .x15 (v265 x)
def v266 (x : Context) : Word := (68719476336 : Word) - (v265 x)
def s267 (x : Context) := (s266 x).set .x15 (v266 x)
def s268 (x : Context) := (s267 x).store 8589934267 (v264 x)
theorem tree268 (x : Context) (d w : Nat) (p : 0<d) (q : d≤24) (u : w<4) :
    (s268 x).mem (wordAt x.index d w)=x.initial.mem (wordAt x.index d w) := by
  have sep : wordAt x.index d w ≠ 8589934267 := by have := word_room x.index d w p q u;omega
  change (if wordAt x.index d w=8589934267 then _ else _) = _
  rw [if_neg sep]
  exact tree255 x d w p q u
def v268 (x : Context) := top x 12
def s269 (x : Context) := (s268 x).set .x13 (v268 x)
def v269 (x : Context) : Word := (v260 x) >>> (53 : Nat)
def s270 (x : Context) := (s269 x).set .x12 (v269 x)
def v270 (x : Context) : Word := (v259 x) + (v269 x)
def s271 (x : Context) := (s270 x).set .x11 (v270 x)
def v271 (x : Context) : Word := (v270 x) * (v258 x)
def s272 (x : Context) := (s271 x).set .x11 (v271 x)
def v272 (x : Context) : Word := (v268 x) <<< (24 : Nat)
def s273 (x : Context) := (s272 x).set .x13 (v272 x)

def code261 : List Instr := [
  (Expr.instr .x13 (.srli .x10 7)),
  (Expr.instr .x13 (.andi .x13 4064)),
  (Expr.instr .x13 (.xori .x13 32)),
  (Expr.instr .x13 (.add .x13 .x22)),
  (Expr.instr .x15 (.lui 1)),
  (Expr.instr .x15 (.sub .x8 .x15)),
  .SD .x15 .x13 1896,
  .LD .x13 .x13 408,
  (Expr.instr .x12 (.srli .x12 53)),
  (Expr.instr .x11 (.add .x11 .x12)),
  (Expr.instr .x11 (.mul .x11 .x14)),
  (Expr.instr .x13 (.slli .x13 24))]
theorem entries261 : OpeningStraight.Listed 261 code261 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span261 (o : Oracle) (x : Context) : Contract o code261 (s261 x) (s273 x) := by
  have h261 := OpeningLinear.register o (s261 x) .x13 (.srli .x10 7) (v261 x) rfl
  have h262 := OpeningLinear.register o (s262 x) .x13 (.andi .x13 4064) (v262 x) rfl
  have h263 := OpeningLinear.register o (s263 x) .x13 (.xori .x13 32) (v263 x) rfl
  have h264 := OpeningLinear.register o (s264 x) .x13 (.add .x13 .x22) (v264 x) (OpeningHeaderAddress.sibling_ptr x.index 12 (by decide))
  have h265 := OpeningLinear.register o (s265 x) .x15 (.lui 1) (v265 x) rfl
  have h266 := OpeningLinear.register o (s266 x) .x15 (.sub .x8 .x15) (v266 x) rfl
  have h267 := OpeningLinear.write o (s267 x) .x15 .x13 1896 8589934267 (v264 x) (by decide) (by change ((v266 x) + signExtend12 1896)=wordAddress 8589934267; exact (by decide : ((68719476336 : Word)-(((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64))+signExtend12 1896=wordAddress 8589934267)) rfl
  have h268 := OpeningLinear.read o (s268 x) .x13 .x13 408 (wordAt x.index 12 3) (top x 12) (by have := word_room x.index 12 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 12 3 408 rfl) (tree268 x 12 3 (by decide) (by decide) (by decide))
  have h269 := OpeningLinear.register o (s269 x) .x12 (.srli .x12 53) (v269 x) rfl
  have h270 := OpeningLinear.register o (s270 x) .x11 (.add .x11 .x12) (v270 x) rfl
  have h271 := OpeningLinear.register o (s271 x) .x11 (.mul .x11 .x14) (v271 x) rfl
  have h272 := OpeningLinear.register o (s272 x) .x13 (.slli .x13 24) (v272 x) rfl
  exact LeafModel.combine h261 (LeafModel.combine h262 (LeafModel.combine h263 (LeafModel.combine h264 (LeafModel.combine h265 (LeafModel.combine h266 (LeafModel.combine h267 (LeafModel.combine h268 (LeafModel.combine h269 (LeafModel.combine h270 (LeafModel.combine h271 (LeafModel.combine h272 (LeafModel.empty _ _))))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
