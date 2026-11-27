import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw12 : listed .check (nodePC false 12) (nodeCode false 12) := by decide
theorem fullNode12 : Matches .check (nodePC false 12) (nodeCode false 12):=matchesListed raw12
private theorem raw13 : listed .check (nodePC false 13) (nodeCode false 13) := by decide
theorem fullNode13 : Matches .check (nodePC false 13) (nodeCode false 13):=matchesListed raw13
private theorem raw14 : listed .check (nodePC false 14) (nodeCode false 14) := by decide
theorem fullNode14 : Matches .check (nodePC false 14) (nodeCode false 14):=matchesListed raw14
private theorem raw15 : listed .check (nodePC false 15) (nodeCode false 15) := by decide
theorem fullNode15 : Matches .check (nodePC false 15) (nodeCode false 15):=matchesListed raw15
end CommitGolfCandidate.S4.Machine
