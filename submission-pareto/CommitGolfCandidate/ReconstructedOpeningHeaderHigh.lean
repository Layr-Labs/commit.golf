import CommitGolfCandidate.ReconstructedOpeningHeaderValue
import CommitGolfCandidate.ReconstructedOpeningHeaderCarry

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps OpeningOps
open TwoPermutationPrototype.RV64 OpeningCursor OpeningHeaderAddress OpeningLinear
set_option maxRecDepth 24000
set_option maxHeartbeats 1200000
attribute [local irreducible] ArtifactEncoding.decode execute

theorem high14 (x : Context) : v360 x=W (partialHeader x 5/2^64) := by
  have bound : digitAt x 14<2^64 := (smallDigit x 14 (by decide)).trans (by decide)
  have h := OpeningHorner.high (partialHeader x 4) 1677 (digitAt x 14) (by decide) bound
  rw [Nat.div_eq_of_lt (small13 x)] at h
  rw [show W 0*W 1677=(0 : Word) from rfl,show (0:Word)+rv64_mulhu (W (partialHeader x 4)) (W 1677)=_ from BitVec.zero_add _] at h
  calc
    v360 x = rv64_mulhu (v295 x) (W 1677)+OpeningHorner.carry (v304 x) (v296 x) := by
      rfl
    _ = _ := by rw [low13,low14,product14];exact h
theorem high15 (x : Context) : v366 x=W (partialHeader x 6/2^64) := by
  have bound : digitAt x 15<2^64 := (smallDigit x 15 (by decide)).trans (by decide)
  have h := OpeningHorner.high (partialHeader x 5) 137 (digitAt x 15) (by decide) bound
  calc
    v366 x = (v360 x*W 137+rv64_mulhu (v304 x) (W 137))+OpeningHorner.carry (v314 x) (v306 x) := by
      change (rv64_mulhu (v304 x) (W 137)+v360 x*W 137)+OpeningHorner.carry (v314 x) (v306 x) = _;ac_rfl
    _ = _ := by rw [high14,low14,low15,product15];exact h
theorem high16 (x : Context) : v372 x=W (partialHeader x 7/2^64) := by
  have bound : digitAt x 16<2^64 := (smallDigit x 16 (by decide)).trans (by decide)
  have h := OpeningHorner.high (partialHeader x 6) 1491 (digitAt x 16) (by decide) bound
  calc
    v372 x = (v366 x*W 1491+rv64_mulhu (v314 x) (W 1491))+OpeningHorner.carry (v324 x) (v316 x) := by
      change (rv64_mulhu (v314 x) (W 1491)+OpeningHorner.carry (v324 x) (v316 x))+v366 x*W 1491 = _;ac_rfl
    _ = _ := by rw [high15,low15,low16,product16];exact h
theorem high17 (x : Context) : v377 x=W (partialHeader x 8/2^64) := by
  have bound : digitAt x 17<2^64 := (smallDigit x 17 (by decide)).trans (by decide)
  have h := OpeningHorner.high (partialHeader x 7) 1491 (digitAt x 17) (by decide) bound
  calc
    v377 x = (v372 x*W 1491+rv64_mulhu (v324 x) (W 1491))+OpeningHorner.carry (v333 x) (v325 x) := by
      change (rv64_mulhu (v324 x) (W 1491)+OpeningHorner.carry (v333 x) (v325 x))+v372 x*W 1491 = _;ac_rfl
    _ = _ := by rw [high16,low16,low17,product17];exact h
theorem high18 (x : Context) : v382 x=W (partialHeader x 9/2^64) := by
  have bound : digitAt x 18<2^64 := (smallDigit x 18 (by decide)).trans (by decide)
  have h := OpeningHorner.high (partialHeader x 8) 1677 (digitAt x 18) (by decide) bound
  calc
    v382 x = (v377 x*W 1677+rv64_mulhu (v333 x) (W 1677))+OpeningHorner.carry (v341 x) (v334 x) := by
      change (rv64_mulhu (v333 x) (W 1677)+OpeningHorner.carry (v341 x) (v334 x))+v377 x*W 1677 = _;ac_rfl
    _ = _ := by rw [high17,low17,low18,product18];exact h
theorem high19 (x : Context) : v387 x=W (partialHeader x 10/2^64) := by
  have bound : digitAt x 19<2^64 := (smallDigit x 19 (by decide)).trans (by decide)
  have h := OpeningHorner.high (partialHeader x 9) 1491 (digitAt x 19) (by decide) bound
  calc
    v387 x = (v382 x*W 1491+rv64_mulhu (v341 x) (W 1491))+OpeningHorner.carry (v344 x) (v342 x) := by
      change (rv64_mulhu (v341 x) (W 1491)+OpeningHorner.carry (v344 x) (v342 x))+v382 x*W 1491 = _;ac_rfl
    _ = _ := by rw [high18,low18,low19,product19];exact h

end CommitGolfCandidate.Reconstruction.OpeningHeader
