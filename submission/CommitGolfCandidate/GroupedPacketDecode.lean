import CommitGolfCandidate.GroupedImageBase
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
/-- Kernel check of the code words of 64 consecutive slots of the K3-lite tile body. -/
def PacketTile (t : Nat) : Prop :=
  ∀ u : Fin 64, ∀ i : Fin 18,
    let n := 64*t+u.val
    i.val < (packet n).length →
      Manifest.decodeBase (codeWord (firstWord n+i.val)) = some ((packet n)[i.val]?.getD .EBREAK)

private theorem packetTile0 : PacketTile 0 := by unfold PacketTile; decide +kernel
private theorem packetTile1 : PacketTile 1 := by unfold PacketTile; decide +kernel
private theorem packetTile2 : PacketTile 2 := by unfold PacketTile; decide +kernel
private theorem packetTile3 : PacketTile 3 := by unfold PacketTile; decide +kernel
private theorem packetTile4 : PacketTile 4 := by unfold PacketTile; decide +kernel
private theorem packetTile5 : PacketTile 5 := by unfold PacketTile; decide +kernel
private theorem packetTile6 : PacketTile 6 := by unfold PacketTile; decide +kernel
private theorem packetTile7 : PacketTile 7 := by unfold PacketTile; decide +kernel
private theorem packetTile8 : PacketTile 8 := by unfold PacketTile; decide +kernel
private theorem packetTile9 : PacketTile 9 := by unfold PacketTile; decide +kernel
private theorem packetTile10 : PacketTile 10 := by unfold PacketTile; decide +kernel
private theorem packetTile11 : PacketTile 11 := by unfold PacketTile; decide +kernel
private theorem packetTile12 : PacketTile 12 := by unfold PacketTile; decide +kernel
private theorem packetTile13 : PacketTile 13 := by unfold PacketTile; decide +kernel
private theorem packetTile14 : PacketTile 14 := by unfold PacketTile; decide +kernel
private theorem packetTile15 : PacketTile 15 := by unfold PacketTile; decide +kernel
private theorem packetTile16 : PacketTile 16 := by unfold PacketTile; decide +kernel
private theorem packetTile17 : PacketTile 17 := by unfold PacketTile; decide +kernel
private theorem packetTile18 : PacketTile 18 := by unfold PacketTile; decide +kernel
private theorem packetTile19 : PacketTile 19 := by unfold PacketTile; decide +kernel
private theorem packetTile20 : PacketTile 20 := by unfold PacketTile; decide +kernel
private theorem packetTile21 : PacketTile 21 := by unfold PacketTile; decide +kernel
private theorem packetTile22 : PacketTile 22 := by unfold PacketTile; decide +kernel
private theorem packetTile23 : PacketTile 23 := by unfold PacketTile; decide +kernel
private theorem packetTile24 : PacketTile 24 := by unfold PacketTile; decide +kernel
private theorem packetTile25 : PacketTile 25 := by unfold PacketTile; decide +kernel
private theorem packetTile26 : PacketTile 26 := by unfold PacketTile; decide +kernel
private theorem packetTile27 : PacketTile 27 := by unfold PacketTile; decide +kernel
private theorem packetTile28 : PacketTile 28 := by unfold PacketTile; decide +kernel
private theorem packetTile29 : PacketTile 29 := by unfold PacketTile; decide +kernel
private theorem packetTile30 : PacketTile 30 := by unfold PacketTile; decide +kernel
private theorem packetTile31 : PacketTile 31 := by unfold PacketTile; decide +kernel
private theorem packetTile32 : PacketTile 32 := by unfold PacketTile; decide +kernel
private theorem packetTile33 : PacketTile 33 := by unfold PacketTile; decide +kernel
private theorem packetTile34 : PacketTile 34 := by unfold PacketTile; decide +kernel
private theorem packetTile35 : PacketTile 35 := by unfold PacketTile; decide +kernel
private theorem packetTile36 : PacketTile 36 := by unfold PacketTile; decide +kernel
private theorem packetTile37 : PacketTile 37 := by unfold PacketTile; decide +kernel
private theorem packetTile38 : PacketTile 38 := by unfold PacketTile; decide +kernel
private theorem packetTile39 : PacketTile 39 := by unfold PacketTile; decide +kernel
private theorem packetTile40 : PacketTile 40 := by unfold PacketTile; decide +kernel
private theorem packetTile41 : PacketTile 41 := by unfold PacketTile; decide +kernel
private theorem packetTile42 : PacketTile 42 := by unfold PacketTile; decide +kernel
private theorem packetTile43 : PacketTile 43 := by unfold PacketTile; decide +kernel
private theorem packetTile44 : PacketTile 44 := by unfold PacketTile; decide +kernel
private theorem packetTile45 : PacketTile 45 := by unfold PacketTile; decide +kernel
private theorem packetTile46 : PacketTile 46 := by unfold PacketTile; decide +kernel
private theorem packetTile47 : PacketTile 47 := by unfold PacketTile; decide +kernel
private theorem packetTile48 : PacketTile 48 := by unfold PacketTile; decide +kernel
private theorem packetTile49 : PacketTile 49 := by unfold PacketTile; decide +kernel
private theorem packetTile50 : PacketTile 50 := by unfold PacketTile; decide +kernel
private theorem packetTile51 : PacketTile 51 := by unfold PacketTile; decide +kernel
private theorem packetTile52 : PacketTile 52 := by unfold PacketTile; decide +kernel
private theorem packetTile53 : PacketTile 53 := by unfold PacketTile; decide +kernel
private theorem packetTile54 : PacketTile 54 := by unfold PacketTile; decide +kernel
private theorem packetTile55 : PacketTile 55 := by unfold PacketTile; decide +kernel
private theorem packetTile56 : PacketTile 56 := by unfold PacketTile; decide +kernel
private theorem packetTile57 : PacketTile 57 := by unfold PacketTile; decide +kernel
private theorem packetTile58 : PacketTile 58 := by unfold PacketTile; decide +kernel
private theorem packetTile59 : PacketTile 59 := by unfold PacketTile; decide +kernel
private theorem packetTile60 : PacketTile 60 := by unfold PacketTile; decide +kernel
private theorem packetTile61 : PacketTile 61 := by unfold PacketTile; decide +kernel
private theorem packetTile62 : PacketTile 62 := by unfold PacketTile; decide +kernel
private theorem packetTile63 : PacketTile 63 := by unfold PacketTile; decide +kernel

theorem packet_tiles (t : Fin 64) : PacketTile t.val := by
  fin_cases t
  · exact packetTile0
  · exact packetTile1
  · exact packetTile2
  · exact packetTile3
  · exact packetTile4
  · exact packetTile5
  · exact packetTile6
  · exact packetTile7
  · exact packetTile8
  · exact packetTile9
  · exact packetTile10
  · exact packetTile11
  · exact packetTile12
  · exact packetTile13
  · exact packetTile14
  · exact packetTile15
  · exact packetTile16
  · exact packetTile17
  · exact packetTile18
  · exact packetTile19
  · exact packetTile20
  · exact packetTile21
  · exact packetTile22
  · exact packetTile23
  · exact packetTile24
  · exact packetTile25
  · exact packetTile26
  · exact packetTile27
  · exact packetTile28
  · exact packetTile29
  · exact packetTile30
  · exact packetTile31
  · exact packetTile32
  · exact packetTile33
  · exact packetTile34
  · exact packetTile35
  · exact packetTile36
  · exact packetTile37
  · exact packetTile38
  · exact packetTile39
  · exact packetTile40
  · exact packetTile41
  · exact packetTile42
  · exact packetTile43
  · exact packetTile44
  · exact packetTile45
  · exact packetTile46
  · exact packetTile47
  · exact packetTile48
  · exact packetTile49
  · exact packetTile50
  · exact packetTile51
  · exact packetTile52
  · exact packetTile53
  · exact packetTile54
  · exact packetTile55
  · exact packetTile56
  · exact packetTile57
  · exact packetTile58
  · exact packetTile59
  · exact packetTile60
  · exact packetTile61
  · exact packetTile62
  · exact packetTile63

end TwoPermutationPrototype.Grouped
