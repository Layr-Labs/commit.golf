import CommitGolfCandidate.ReconstructedOpeningHeader327

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v336 (x : Context) : Word := (v238 x) &&& signExtend12 4064
def s337 (x : Context) := (s336 x).set .x12 (v336 x)
def v337 (x : Context) : Word := (v336 x) ^^^ signExtend12 32
def s338 (x : Context) := (s337 x).set .x28 (v337 x)
def v338 (x : Context) : Word := basePtr x.index 19
def s339 (x : Context) := (s338 x).set .x28 (v338 x)
def v339 (x : Context) := upper (top x 19)
def s340 (x : Context) := (s339 x).set .x12 (v339 x)
def v340 (x : Context) : Word := (v335 x) >>> (53 : Nat)
def s341 (x : Context) := (s340 x).set .x11 (v340 x)
def v341 (x : Context) : Word := (v334 x) + (v340 x)
def s342 (x : Context) := (s341 x).set .x31 (v341 x)
def v342 (x : Context) : Word := (v341 x) * (v315 x)
def s343 (x : Context) := (s342 x).set .x11 (v342 x)
def v343 (x : Context) : Word := (v339 x) &&& signExtend12 2047
def s344 (x : Context) := (s343 x).set .x18 (v343 x)
def v344 (x : Context) : Word := (v342 x) + (v343 x)
def s345 (x : Context) := (s344 x).set .x18 (v344 x)

def code336 : List Instr := [
  (Expr.instr .x12 (.andi .x10 4064)),
  (Expr.instr .x28 (.xori .x12 32)),
  (Expr.instr .x28 (.add .x28 .x22)),
  .LWU .x12 .x28 636,
  (Expr.instr .x11 (.srli .x11 53)),
  (Expr.instr .x31 (.add .x14 .x11)),
  (Expr.instr .x11 (.mul .x31 .x5)),
  (Expr.instr .x18 (.andi .x12 2047)),
  (Expr.instr .x18 (.add .x11 .x18))]
theorem entries336 : OpeningStraight.Listed 336 code336 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span336 (o : Oracle) (x : Context) : Contract o code336 (s336 x) (s345 x) := by
  have h336 := OpeningLinear.register o (s336 x) .x12 (.andi .x10 4064) (v336 x) rfl
  have h337 := OpeningLinear.register o (s337 x) .x28 (.xori .x12 32) (v337 x) rfl
  have h338 := OpeningLinear.register o (s338 x) .x28 (.add .x28 .x22) (v338 x) (OpeningHeaderAddress.sibling_ptr x.index 19 (by decide))
  have h339 := OpeningLinear.readUpper o (s339 x) .x12 .x28 636 (wordAt x.index 19 3) (top x 19) (by have := word_room x.index 19 3 (by decide) (by decide) (by decide);omega) (by change basePtr x.index 19 + signExtend12 636=W (8*(wordAt x.index 19 3)+4);rw [show signExtend12 636=W (32*19+8*3)+W 4 by rfl,←BitVec.add_assoc,←show signExtend12 632=W (32*19+8*3) by rfl,OpeningHeaderAddress.offset x.index 19 3 632 rfl];exact (BitVec.ofNat_add ..).symm) (tree293 x 19 3 (by decide) (by decide) (by decide))
  have h340 := OpeningLinear.register o (s340 x) .x11 (.srli .x11 53) (v340 x) rfl
  have h341 := OpeningLinear.register o (s341 x) .x31 (.add .x14 .x11) (v341 x) rfl
  have h342 := OpeningLinear.register o (s342 x) .x11 (.mul .x31 .x5) (v342 x) rfl
  have h343 := OpeningLinear.register o (s343 x) .x18 (.andi .x12 2047) (v343 x) rfl
  have h344 := OpeningLinear.register o (s344 x) .x18 (.add .x11 .x18) (v344 x) rfl
  exact LeafModel.combine h336 (LeafModel.combine h337 (LeafModel.combine h338 (LeafModel.combine h339 (LeafModel.combine h340 (LeafModel.combine h341 (LeafModel.combine h342 (LeafModel.combine h343 (LeafModel.combine h344 (LeafModel.empty _ _)))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
