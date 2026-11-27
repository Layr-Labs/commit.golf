namespace CommitGolfCandidate.Chained.BinaryMachine
/-- First byte of the salt-and-message rows. Shared by the layout and the draw loop. -/
def rowBase := 5905588224
def saltAddress (i : Nat) := rowBase + 184*(i/2) + 72 + 16*(i%2)
end CommitGolfCandidate.Chained.BinaryMachine
