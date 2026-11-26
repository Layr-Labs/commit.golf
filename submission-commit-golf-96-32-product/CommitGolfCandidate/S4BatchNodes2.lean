import CommitGolfCandidate.S4NodeCode
namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw8 : listed .check (nodePC true 8) (nodeCode true 8) := by decide
theorem batchNode8 : Matches .check (nodePC true 8) (nodeCode true 8):=matchesListed raw8
private theorem raw9 : listed .check (nodePC true 9) (nodeCode true 9) := by decide
theorem batchNode9 : Matches .check (nodePC true 9) (nodeCode true 9):=matchesListed raw9
private theorem raw10 : listed .check (nodePC true 10) (nodeCode true 10) := by decide
theorem batchNode10 : Matches .check (nodePC true 10) (nodeCode true 10):=matchesListed raw10
private theorem raw11 : listed .check (nodePC true 11) (nodeCode true 11) := by decide
theorem batchNode11 : Matches .check (nodePC true 11) (nodeCode true 11):=matchesListed raw11
end CommitGolfCandidate.S4.Machine
