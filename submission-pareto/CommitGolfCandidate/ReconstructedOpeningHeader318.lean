import CommitGolfCandidate.ReconstructedOpeningHeader308

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

def v318 (x : Context) : Word := (v238 x) >>> (2 : Nat)
def s319 (x : Context) := (s318 x).set .x12 (v318 x)
def v319 (x : Context) : Word := (v318 x) &&& signExtend12 4064
def s320 (x : Context) := (s319 x).set .x12 (v319 x)
def v320 (x : Context) : Word := (v319 x) ^^^ signExtend12 32
def s321 (x : Context) := (s320 x).set .x20 (v320 x)
def v321 (x : Context) : Word := basePtr x.index 17
def s322 (x : Context) := (s321 x).set .x20 (v321 x)
def v322 (x : Context) := top x 17
def s323 (x : Context) := (s322 x).set .x12 (v322 x)
def v323 (x : Context) : Word := (v317 x) >>> (53 : Nat)
def s324 (x : Context) := (s323 x).set .x11 (v323 x)
def v324 (x : Context) : Word := (v316 x) + (v323 x)
def s325 (x : Context) := (s324 x).set .x6 (v324 x)
def v325 (x : Context) : Word := (v324 x) * (v315 x)
def s326 (x : Context) := (s325 x).set .x16 (v325 x)
def v326 (x : Context) : Word := (v322 x) <<< (23 : Nat)
def s327 (x : Context) := (s326 x).set .x12 (v326 x)

def code318 : List Instr := [
  (Expr.instr .x12 (.srli .x10 2)),
  (Expr.instr .x12 (.andi .x12 4064)),
  (Expr.instr .x20 (.xori .x12 32)),
  (Expr.instr .x20 (.add .x20 .x22)),
  .LD .x12 .x20 568,
  (Expr.instr .x11 (.srli .x11 53)),
  (Expr.instr .x6 (.add .x1 .x11)),
  (Expr.instr .x16 (.mul .x6 .x5)),
  (Expr.instr .x12 (.slli .x12 23))]
theorem entries318 : OpeningStraight.Listed 318 code318 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem span318 (o : Oracle) (x : Context) : Contract o code318 (s318 x) (s327 x) := by
  have h318 := OpeningLinear.register o (s318 x) .x12 (.srli .x10 2) (v318 x) rfl
  have h319 := OpeningLinear.register o (s319 x) .x12 (.andi .x12 4064) (v319 x) rfl
  have h320 := OpeningLinear.register o (s320 x) .x20 (.xori .x12 32) (v320 x) rfl
  have h321 := OpeningLinear.register o (s321 x) .x20 (.add .x20 .x22) (v321 x) (OpeningHeaderAddress.sibling_ptr x.index 17 (by decide))
  have h322 := OpeningLinear.read o (s322 x) .x12 .x20 568 (wordAt x.index 17 3) (top x 17) (by have := word_room x.index 17 3 (by decide) (by decide) (by decide);omega) (OpeningHeaderAddress.offset x.index 17 3 568 rfl) (tree293 x 17 3 (by decide) (by decide) (by decide))
  have h323 := OpeningLinear.register o (s323 x) .x11 (.srli .x11 53) (v323 x) rfl
  have h324 := OpeningLinear.register o (s324 x) .x6 (.add .x1 .x11) (v324 x) rfl
  have h325 := OpeningLinear.register o (s325 x) .x16 (.mul .x6 .x5) (v325 x) rfl
  have h326 := OpeningLinear.register o (s326 x) .x12 (.slli .x12 23) (v326 x) rfl
  exact LeafModel.combine h318 (LeafModel.combine h319 (LeafModel.combine h320 (LeafModel.combine h321 (LeafModel.combine h322 (LeafModel.combine h323 (LeafModel.combine h324 (LeafModel.combine h325 (LeafModel.combine h326 (LeafModel.empty _ _)))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
