import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw0 : listed .check (nodePC true 0) (nodeCode true 0) := by decide
theorem batchNode0 : Matches .check (nodePC true 0) (nodeCode true 0):=matchesListed raw0
private theorem raw1 : listed .check (nodePC true 1) (nodeCode true 1) := by decide
theorem batchNode1 : Matches .check (nodePC true 1) (nodeCode true 1):=matchesListed raw1
private theorem raw2 : listed .check (nodePC true 2) (nodeCode true 2) := by decide
theorem batchNode2 : Matches .check (nodePC true 2) (nodeCode true 2):=matchesListed raw2
private theorem raw3 : listed .check (nodePC true 3) (nodeCode true 3) := by decide
theorem batchNode3 : Matches .check (nodePC true 3) (nodeCode true 3):=matchesListed raw3
end CommitGolfCandidate.S4.Machine
