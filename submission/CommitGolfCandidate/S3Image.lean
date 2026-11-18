import CommitGolfCandidate.S3ImageA
import CommitGolfCandidate.S3ImageB
import CommitGolfCandidate.S3ImageC

/-! Instruction fetches of the appended code, collected from `S3ImageA`, `S3ImageB` and `S3ImageC`.
Word 54 jumps to word 251827 (PC 1011404); appended word `k` sits at PC `1011404 + 4 k`:
* 0..8 generator setup, 9..200 the 64 generator calls, 201 the generator branch (S4GenExec);
* 202..206 seed-block clearing (PC 1012212), 207..215 leaf-phase setup (PC 1012232);
* 216..217 cell bases (PC 1012268), leaf `l` at 218 + 11 l (PC 1012276 + 44 l), group call `c` at
  922 + 3 c (PC 1015092 + 12 c), 970..974 restore and latch (PC 1015284);
* 975..981 parent setup (PC 1015304), parent `j` of the loop body at 982 + 4 j (PC 1015332 + 16 j),
  2006 the parent branch (PC 1019428), 2007 the jump to the root copy (PC 1019432). -/
