import CommitGolfCandidate.S4NodeCode
namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw4 : listed .check (nodePC true 4) (nodeCode true 4) := by decide
theorem batchNode4 : Matches .check (nodePC true 4) (nodeCode true 4):=matchesListed raw4
private theorem raw5 : listed .check (nodePC true 5) (nodeCode true 5) := by decide
theorem batchNode5 : Matches .check (nodePC true 5) (nodeCode true 5):=matchesListed raw5
private theorem raw6 : listed .check (nodePC true 6) (nodeCode true 6) := by decide
theorem batchNode6 : Matches .check (nodePC true 6) (nodeCode true 6):=matchesListed raw6
private theorem raw7 : listed .check (nodePC true 7) (nodeCode true 7) := by decide
theorem batchNode7 : Matches .check (nodePC true 7) (nodeCode true 7):=matchesListed raw7
end CommitGolfCandidate.S4.Machine
