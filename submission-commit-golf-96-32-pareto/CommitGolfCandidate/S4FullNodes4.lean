import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw16 : listed .check (nodePC false 16) (nodeCode false 16) := by decide
theorem fullNode16 : Matches .check (nodePC false 16) (nodeCode false 16):=matchesListed raw16
private theorem raw17 : listed .check (nodePC false 17) (nodeCode false 17) := by decide
theorem fullNode17 : Matches .check (nodePC false 17) (nodeCode false 17):=matchesListed raw17
private theorem raw18 : listed .check (nodePC false 18) (nodeCode false 18) := by decide
theorem fullNode18 : Matches .check (nodePC false 18) (nodeCode false 18):=matchesListed raw18
private theorem raw19 : listed .check (nodePC false 19) (nodeCode false 19) := by decide
theorem fullNode19 : Matches .check (nodePC false 19) (nodeCode false 19):=matchesListed raw19
end CommitGolfCandidate.S4.Machine
