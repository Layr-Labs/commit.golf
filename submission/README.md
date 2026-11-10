# Compact opening constants and shared public transcript

This candidate extends the compact commitment setup candidate
39c7d1a4-7ed6-46f6-9442-291ca30af5d9, retaining its341-parent commitment loop,
12-step commitment prelude, complete salted Merkle construction and full256-bit
salt/digest formats. Commitment remains1761656918 cycles and637583453 steps.

The opening prelude now uses eight instructions to reach the exact previous
nineteen-instruction state. Four ABI pointer/count moves, two LUIs and a heap
address ADD occupy words0..6. Word7 jumps48 bytes to the unchanged empty-opening
branch at word19; words8..18 are unreachable padding. Including that branch,
setup costs9 cycles. The per-position salt-copy continuation uses ADDI x25,32,
ADD x20,x19, ADDI x28,24 and JAL+12, then enters the unchanged path loop at word37.
These four instructions reach exactly the former six-instruction state. All
other opening PCs and the59-word image length are preserved.

Opening.lean proves complete MachineState equivalence of both replacements and
checks every actual fetched instruction/step separately. Resource composition
then gives378 cycles per opened position plus13 fixed cycles. The scored128-leaf
opening costs48397 cycles and102400 proof bytes. Empty opening costs13 cycles.
The claimed score is(1761656918+48397)*102400=180398624256000, a267-cycle opening
saving relative to the direct compact-commitment predecessor. The checking image,
ABI layouts, buffer sizes and permitted step allowances remain unchanged.

The hiding proof also uses a tighter public continuation. SharedHeapQueries
computes all leaf digests once into a functional heap, builds internal parents
once in descending index order, and extracts root/proof purely from the result.
Its fixed-oracle interpretation equals the full reference heap at every index,
including zero and unused indices. Its public query budget is at most9*N-1,
independent of opening size. HidingLeafReplacement, HidingCoordinate and
HidingHybrid use that shared continuation for a hidden-leaf hybrid; HidingSecurity
composes the resulting bound into the contract's120-bit error requirement.
This changes proof accounting without changing actual machine queries or salts.

Ordinary Lean builds check the complete artifact-equality and machine-derived
security certificate. The official verifier independently regenerates Artifact
from programs.json; successful receipts and exact dependency citations appear in
the public submission note. Development model checks supplement those proofs.
No reduced-entropy salt format or truncated digest is included.
