import CommitGolfCandidate.ReconstructedOpeningHeader336
import CommitGolfCandidate.ReconstructedOpeningHorner

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

/-- At the carry chain entry, the alignment branch has only written these
four registers and possibly the next word of proof memory. -/
def s357 (x : Context) (q : Model) : Model := ⟨fun
  | .x5 => q.reg .x5 | .x12 => q.reg .x12 | .x13 => q.reg .x13 | .x19 => q.reg .x19
  | r => (s345 x).reg r, q.mem⟩

def v357 (x : Context) : Word := (0 : Word)+signExtend12 1677
def s358 (x : Context) (q : Model) := (s357 x q).set .x23 (v357 x)
def v358 (x : Context) : Word := rv64_mulhu (v295 x) (v357 x)
def s359 (x : Context) (q : Model) := (s358 x q).set .x13 (v358 x)
def v359 (x : Context) : Word := OpeningHorner.carry (v304 x) (v296 x)
def s360 (x : Context) (q : Model) := (s359 x q).set .x17 (v359 x)
def v360 (x : Context) : Word := (v358 x)+(v359 x)
def s361 (x : Context) (q : Model) := (s360 x q).set .x13 (v360 x)
def v361 (x : Context) : Word := (0 : Word)+signExtend12 137
def s362 (x : Context) (q : Model) := (s361 x q).set .x17 (v361 x)
def v362 (x : Context) : Word := (v360 x)*(v361 x)
def s363 (x : Context) (q : Model) := (s362 x q).set .x13 (v362 x)
def v363 (x : Context) : Word := rv64_mulhu (v304 x) (v361 x)
def s364 (x : Context) (q : Model) := (s363 x q).set .x17 (v363 x)
def v364 (x : Context) : Word := (v363 x)+(v362 x)
def s365 (x : Context) (q : Model) := (s364 x q).set .x13 (v364 x)
def v365 (x : Context) : Word := OpeningHorner.carry (v314 x) (v306 x)
def s366 (x : Context) (q : Model) := (s365 x q).set .x17 (v365 x)
def v366 (x : Context) : Word := (v364 x)+(v365 x)
def s367 (x : Context) (q : Model) := (s366 x q).set .x13 (v366 x)
def v367 (x : Context) : Word := (0 : Word)+signExtend12 1491
def s368 (x : Context) (q : Model) := (s367 x q).set .x29 (v367 x)
def v368 (x : Context) : Word := (v366 x)*(v367 x)
def s369 (x : Context) (q : Model) := (s368 x q).set .x13 (v368 x)
def v369 (x : Context) : Word := rv64_mulhu (v314 x) (v367 x)
def s370 (x : Context) (q : Model) := (s369 x q).set .x17 (v369 x)
def v370 (x : Context) : Word := OpeningHorner.carry (v324 x) (v316 x)
def s371 (x : Context) (q : Model) := (s370 x q).set .x5 (v370 x)
def v371 (x : Context) : Word := (v369 x)+(v370 x)
def s372 (x : Context) (q : Model) := (s371 x q).set .x17 (v371 x)
def v372 (x : Context) : Word := (v371 x)+(v368 x)
def s373 (x : Context) (q : Model) := (s372 x q).set .x13 (v372 x)
def v373 (x : Context) : Word := (v372 x)*(v367 x)
def s374 (x : Context) (q : Model) := (s373 x q).set .x13 (v373 x)
def v374 (x : Context) : Word := rv64_mulhu (v324 x) (v367 x)
def s375 (x : Context) (q : Model) := (s374 x q).set .x17 (v374 x)
def v375 (x : Context) : Word := OpeningHorner.carry (v333 x) (v325 x)
def s376 (x : Context) (q : Model) := (s375 x q).set .x16 (v375 x)
def v376 (x : Context) : Word := (v374 x)+(v375 x)
def s377 (x : Context) (q : Model) := (s376 x q).set .x16 (v376 x)
def v377 (x : Context) : Word := (v376 x)+(v373 x)
def s378 (x : Context) (q : Model) := (s377 x q).set .x13 (v377 x)
def v378 (x : Context) : Word := (v377 x)*(v357 x)
def s379 (x : Context) (q : Model) := (s378 x q).set .x13 (v378 x)
def v379 (x : Context) : Word := rv64_mulhu (v333 x) (v357 x)
def s380 (x : Context) (q : Model) := (s379 x q).set .x16 (v379 x)
def v380 (x : Context) : Word := OpeningHorner.carry (v341 x) (v334 x)
def s381 (x : Context) (q : Model) := (s380 x q).set .x14 (v380 x)
def v381 (x : Context) : Word := (v379 x)+(v380 x)
def s382 (x : Context) (q : Model) := (s381 x q).set .x14 (v381 x)
def v382 (x : Context) : Word := (v381 x)+(v378 x)
def s383 (x : Context) (q : Model) := (s382 x q).set .x13 (v382 x)
def v383 (x : Context) : Word := (v382 x)*(v367 x)
def s384 (x : Context) (q : Model) := (s383 x q).set .x13 (v383 x)
def v384 (x : Context) : Word := rv64_mulhu (v341 x) (v367 x)
def s385 (x : Context) (q : Model) := (s384 x q).set .x14 (v384 x)
def v385 (x : Context) : Word := OpeningHorner.carry (v344 x) (v342 x)
def s386 (x : Context) (q : Model) := (s385 x q).set .x11 (v385 x)
def v386 (x : Context) : Word := (v384 x)+(v385 x)
def s387 (x : Context) (q : Model) := (s386 x q).set .x11 (v386 x)
def v387 (x : Context) : Word := (v386 x)+(v383 x)
def s388 (x : Context) (q : Model) := (s387 x q).set .x13 (v387 x)

def carryCode : List Instr := [
  Expr.instr .x23 (.addi .x0 1677),
  Expr.instr .x13 (.mulhu .x17 .x23),
  Expr.instr .x17 (.sltu .x29 .x9),
  Expr.instr .x13 (.add .x13 .x17),
  Expr.instr .x17 (.addi .x0 137),
  Expr.instr .x13 (.mul .x13 .x17),
  Expr.instr .x17 (.mulhu .x29 .x17),
  Expr.instr .x13 (.add .x17 .x13),
  Expr.instr .x17 (.sltu .x30 .x24),
  Expr.instr .x13 (.add .x13 .x17),
  Expr.instr .x29 (.addi .x0 1491),
  Expr.instr .x13 (.mul .x13 .x29),
  Expr.instr .x17 (.mulhu .x30 .x29),
  Expr.instr .x5 (.sltu .x6 .x1),
  Expr.instr .x17 (.add .x17 .x5),
  Expr.instr .x13 (.add .x17 .x13),
  Expr.instr .x13 (.mul .x13 .x29),
  Expr.instr .x17 (.mulhu .x6 .x29),
  Expr.instr .x16 (.sltu .x21 .x16),
  Expr.instr .x16 (.add .x17 .x16),
  Expr.instr .x13 (.add .x16 .x13),
  Expr.instr .x13 (.mul .x13 .x23),
  Expr.instr .x16 (.mulhu .x21 .x23),
  Expr.instr .x14 (.sltu .x31 .x14),
  Expr.instr .x14 (.add .x16 .x14),
  Expr.instr .x13 (.add .x14 .x13),
  Expr.instr .x13 (.mul .x13 .x29),
  Expr.instr .x14 (.mulhu .x31 .x29),
  Expr.instr .x11 (.sltu .x18 .x11),
  Expr.instr .x11 (.add .x14 .x11),
  Expr.instr .x13 (.add .x11 .x13)]
theorem carryTable : OpeningStraight.Listed 357 carryCode := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
theorem carryRun (o : Oracle) (x : Context) (q : Model) : Contract o carryCode (s357 x q) (s388 x q) := by
  have h357 := OpeningLinear.register o (s357 x q) .x23 (.addi .x0 1677) (v357 x) rfl
  have h358 := OpeningLinear.register o (s358 x q) .x13 (.mulhu .x17 .x23) (v358 x) rfl
  have h359 := OpeningLinear.register o (s359 x q) .x17 (.sltu .x29 .x9) (v359 x) rfl
  have h360 := OpeningLinear.register o (s360 x q) .x13 (.add .x13 .x17) (v360 x) rfl
  have h361 := OpeningLinear.register o (s361 x q) .x17 (.addi .x0 137) (v361 x) rfl
  have h362 := OpeningLinear.register o (s362 x q) .x13 (.mul .x13 .x17) (v362 x) rfl
  have h363 := OpeningLinear.register o (s363 x q) .x17 (.mulhu .x29 .x17) (v363 x) rfl
  have h364 := OpeningLinear.register o (s364 x q) .x13 (.add .x17 .x13) (v364 x) rfl
  have h365 := OpeningLinear.register o (s365 x q) .x17 (.sltu .x30 .x24) (v365 x) rfl
  have h366 := OpeningLinear.register o (s366 x q) .x13 (.add .x13 .x17) (v366 x) rfl
  have h367 := OpeningLinear.register o (s367 x q) .x29 (.addi .x0 1491) (v367 x) rfl
  have h368 := OpeningLinear.register o (s368 x q) .x13 (.mul .x13 .x29) (v368 x) rfl
  have h369 := OpeningLinear.register o (s369 x q) .x17 (.mulhu .x30 .x29) (v369 x) rfl
  have h370 := OpeningLinear.register o (s370 x q) .x5 (.sltu .x6 .x1) (v370 x) rfl
  have h371 := OpeningLinear.register o (s371 x q) .x17 (.add .x17 .x5) (v371 x) rfl
  have h372 := OpeningLinear.register o (s372 x q) .x13 (.add .x17 .x13) (v372 x) rfl
  have h373 := OpeningLinear.register o (s373 x q) .x13 (.mul .x13 .x29) (v373 x) rfl
  have h374 := OpeningLinear.register o (s374 x q) .x17 (.mulhu .x6 .x29) (v374 x) rfl
  have h375 := OpeningLinear.register o (s375 x q) .x16 (.sltu .x21 .x16) (v375 x) rfl
  have h376 := OpeningLinear.register o (s376 x q) .x16 (.add .x17 .x16) (v376 x) rfl
  have h377 := OpeningLinear.register o (s377 x q) .x13 (.add .x16 .x13) (v377 x) rfl
  have h378 := OpeningLinear.register o (s378 x q) .x13 (.mul .x13 .x23) (v378 x) rfl
  have h379 := OpeningLinear.register o (s379 x q) .x16 (.mulhu .x21 .x23) (v379 x) rfl
  have h380 := OpeningLinear.register o (s380 x q) .x14 (.sltu .x31 .x14) (v380 x) rfl
  have h381 := OpeningLinear.register o (s381 x q) .x14 (.add .x16 .x14) (v381 x) rfl
  have h382 := OpeningLinear.register o (s382 x q) .x13 (.add .x14 .x13) (v382 x) rfl
  have h383 := OpeningLinear.register o (s383 x q) .x13 (.mul .x13 .x29) (v383 x) rfl
  have h384 := OpeningLinear.register o (s384 x q) .x14 (.mulhu .x31 .x29) (v384 x) rfl
  have h385 := OpeningLinear.register o (s385 x q) .x11 (.sltu .x18 .x11) (v385 x) rfl
  have h386 := OpeningLinear.register o (s386 x q) .x11 (.add .x14 .x11) (v386 x) rfl
  have h387 := OpeningLinear.register o (s387 x q) .x13 (.add .x11 .x13) (v387 x) rfl
  exact LeafModel.combine h357 (LeafModel.combine h358 (LeafModel.combine h359 (LeafModel.combine h360 (LeafModel.combine h361 (LeafModel.combine h362 (LeafModel.combine h363 (LeafModel.combine h364 (LeafModel.combine h365 (LeafModel.combine h366 (LeafModel.combine h367 (LeafModel.combine h368 (LeafModel.combine h369 (LeafModel.combine h370 (LeafModel.combine h371 (LeafModel.combine h372 (LeafModel.combine h373 (LeafModel.combine h374 (LeafModel.combine h375 (LeafModel.combine h376 (LeafModel.combine h377 (LeafModel.combine h378 (LeafModel.combine h379 (LeafModel.combine h380 (LeafModel.combine h381 (LeafModel.combine h382 (LeafModel.combine h383 (LeafModel.combine h384 (LeafModel.combine h385 (LeafModel.combine h386 (LeafModel.combine h387 (LeafModel.empty _ _)))))))))))))))))))))))))))))))

end CommitGolfCandidate.Reconstruction.OpeningHeader
