import CommitGolfCandidate.S4NodeCode
set_option Elab.async false

namespace CommitGolfCandidate.S4.Machine
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000
private theorem raw20 : listed .check (nodePC false 20) (nodeCode false 20) := by decide
theorem fullNode20 : Matches .check (nodePC false 20) (nodeCode false 20):=matchesListed raw20
private theorem raw21 : listed .check (nodePC false 21) (nodeCode false 21) := by decide
theorem fullNode21 : Matches .check (nodePC false 21) (nodeCode false 21):=matchesListed raw21
private theorem raw22 : listed .check (nodePC false 22) (nodeCode false 22) := by decide
theorem fullNode22 : Matches .check (nodePC false 22) (nodeCode false 22):=matchesListed raw22
private theorem raw23 : listed .check (nodePC false 23) (nodeCode false 23) := by decide
theorem fullNode23 : Matches .check (nodePC false 23) (nodeCode false 23):=matchesListed raw23
end CommitGolfCandidate.S4.Machine
