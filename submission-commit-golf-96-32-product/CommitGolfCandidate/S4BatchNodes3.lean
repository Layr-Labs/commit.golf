import CommitGolfCandidate.S4NodeCode
namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw12 : listed .check (nodePC true 12) (nodeCode true 12) := by decide
theorem batchNode12 : Matches .check (nodePC true 12) (nodeCode true 12):=matchesListed raw12
private theorem raw13 : listed .check (nodePC true 13) (nodeCode true 13) := by decide
theorem batchNode13 : Matches .check (nodePC true 13) (nodeCode true 13):=matchesListed raw13
private theorem raw14 : listed .check (nodePC true 14) (nodeCode true 14) := by decide
theorem batchNode14 : Matches .check (nodePC true 14) (nodeCode true 14):=matchesListed raw14
end CommitGolfCandidate.S4.Machine
