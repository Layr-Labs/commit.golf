import CommitGolfCandidate.GroupedImageBase
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
/-- Every word of the 64 pair packets of tile `t` decodes to the parametric `pairPacket`. -/
def PairTile (t : Nat) : Prop :=
  ∀ u : Fin 64, ∀ i : Fin 23,
    let p := 64*t+u.val
    i.val < (pairPacket p).length →
      Manifest.decodeBase (codeWord (pairWord p+i.val)) = some ((pairPacket p)[i.val]?.getD .EBREAK)

private theorem pairTile0 : PairTile 0 := by unfold PairTile; decide +kernel
private theorem pairTile1 : PairTile 1 := by unfold PairTile; decide +kernel
private theorem pairTile2 : PairTile 2 := by unfold PairTile; decide +kernel
private theorem pairTile3 : PairTile 3 := by unfold PairTile; decide +kernel
private theorem pairTile4 : PairTile 4 := by unfold PairTile; decide +kernel
private theorem pairTile5 : PairTile 5 := by unfold PairTile; decide +kernel
private theorem pairTile6 : PairTile 6 := by unfold PairTile; decide +kernel
private theorem pairTile7 : PairTile 7 := by unfold PairTile; decide +kernel
private theorem pairTile8 : PairTile 8 := by unfold PairTile; decide +kernel
private theorem pairTile9 : PairTile 9 := by unfold PairTile; decide +kernel
private theorem pairTile10 : PairTile 10 := by unfold PairTile; decide +kernel
private theorem pairTile11 : PairTile 11 := by unfold PairTile; decide +kernel
private theorem pairTile12 : PairTile 12 := by unfold PairTile; decide +kernel
private theorem pairTile13 : PairTile 13 := by unfold PairTile; decide +kernel
private theorem pairTile14 : PairTile 14 := by unfold PairTile; decide +kernel
private theorem pairTile15 : PairTile 15 := by unfold PairTile; decide +kernel
private theorem pairTile16 : PairTile 16 := by unfold PairTile; decide +kernel
private theorem pairTile17 : PairTile 17 := by unfold PairTile; decide +kernel
private theorem pairTile18 : PairTile 18 := by unfold PairTile; decide +kernel
private theorem pairTile19 : PairTile 19 := by unfold PairTile; decide +kernel
private theorem pairTile20 : PairTile 20 := by unfold PairTile; decide +kernel
private theorem pairTile21 : PairTile 21 := by unfold PairTile; decide +kernel
private theorem pairTile22 : PairTile 22 := by unfold PairTile; decide +kernel
private theorem pairTile23 : PairTile 23 := by unfold PairTile; decide +kernel
private theorem pairTile24 : PairTile 24 := by unfold PairTile; decide +kernel
private theorem pairTile25 : PairTile 25 := by unfold PairTile; decide +kernel
private theorem pairTile26 : PairTile 26 := by unfold PairTile; decide +kernel
private theorem pairTile27 : PairTile 27 := by unfold PairTile; decide +kernel
private theorem pairTile28 : PairTile 28 := by unfold PairTile; decide +kernel
private theorem pairTile29 : PairTile 29 := by unfold PairTile; decide +kernel
private theorem pairTile30 : PairTile 30 := by unfold PairTile; decide +kernel
private theorem pairTile31 : PairTile 31 := by unfold PairTile; decide +kernel

theorem pair_tiles (t : Fin 32) : PairTile t.val := by
  fin_cases t
  · exact pairTile0
  · exact pairTile1
  · exact pairTile2
  · exact pairTile3
  · exact pairTile4
  · exact pairTile5
  · exact pairTile6
  · exact pairTile7
  · exact pairTile8
  · exact pairTile9
  · exact pairTile10
  · exact pairTile11
  · exact pairTile12
  · exact pairTile13
  · exact pairTile14
  · exact pairTile15
  · exact pairTile16
  · exact pairTile17
  · exact pairTile18
  · exact pairTile19
  · exact pairTile20
  · exact pairTile21
  · exact pairTile22
  · exact pairTile23
  · exact pairTile24
  · exact pairTile25
  · exact pairTile26
  · exact pairTile27
  · exact pairTile28
  · exact pairTile29
  · exact pairTile30
  · exact pairTile31

end TwoPermutationPrototype.Grouped
