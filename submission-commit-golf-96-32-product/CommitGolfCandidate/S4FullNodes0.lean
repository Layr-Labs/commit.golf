import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw0 : listed .check (nodePC false 0) (nodeCode false 0) := by decide
theorem fullNode0 : Matches .check (nodePC false 0) (nodeCode false 0):=matchesListed raw0
private theorem raw1 : listed .check (nodePC false 1) (nodeCode false 1) := by decide
theorem fullNode1 : Matches .check (nodePC false 1) (nodeCode false 1):=matchesListed raw1
private theorem raw2 : listed .check (nodePC false 2) (nodeCode false 2) := by decide
theorem fullNode2 : Matches .check (nodePC false 2) (nodeCode false 2):=matchesListed raw2
private theorem raw3 : listed .check (nodePC false 3) (nodeCode false 3) := by decide
theorem fullNode3 : Matches .check (nodePC false 3) (nodeCode false 3):=matchesListed raw3
end CommitGolfCandidate.S4.Machine
