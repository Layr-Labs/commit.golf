import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw8 : listed .check (nodePC false 8) (nodeCode false 8) := by decide
theorem fullNode8 : Matches .check (nodePC false 8) (nodeCode false 8):=matchesListed raw8
private theorem raw9 : listed .check (nodePC false 9) (nodeCode false 9) := by decide
theorem fullNode9 : Matches .check (nodePC false 9) (nodeCode false 9):=matchesListed raw9
private theorem raw10 : listed .check (nodePC false 10) (nodeCode false 10) := by decide
theorem fullNode10 : Matches .check (nodePC false 10) (nodeCode false 10):=matchesListed raw10
private theorem raw11 : listed .check (nodePC false 11) (nodeCode false 11) := by decide
theorem fullNode11 : Matches .check (nodePC false 11) (nodeCode false 11):=matchesListed raw11
end CommitGolfCandidate.S4.Machine
