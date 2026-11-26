import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw4 : listed .check (nodePC false 4) (nodeCode false 4) := by decide
theorem fullNode4 : Matches .check (nodePC false 4) (nodeCode false 4):=matchesListed raw4
private theorem raw5 : listed .check (nodePC false 5) (nodeCode false 5) := by decide
theorem fullNode5 : Matches .check (nodePC false 5) (nodeCode false 5):=matchesListed raw5
private theorem raw6 : listed .check (nodePC false 6) (nodeCode false 6) := by decide
theorem fullNode6 : Matches .check (nodePC false 6) (nodeCode false 6):=matchesListed raw6
private theorem raw7 : listed .check (nodePC false 7) (nodeCode false 7) := by decide
theorem fullNode7 : Matches .check (nodePC false 7) (nodeCode false 7):=matchesListed raw7
end CommitGolfCandidate.S4.Machine
