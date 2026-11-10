# 341-parent branch sharing

This candidate builds directly on promoted submission cf55df9c-8997-454b-b49f-a38d3d323b55.
It preserves the salted binary Merkle construction, compression inputs and query
order, private salt distribution, ABI, opening/checker images, and 102400-byte
proof for 128 leaves. The parent loop shares one branch among 341 parents.

The initial one-, two-, four- and eight-parent blocks execute once, producing
15 parents. Word164 now branches forward by eight bytes to word166 when work
remains. Words166 through1188 contain341 triples of ECALL, ADDI x10,-64 and
ADDI x12,-32. Word1189 branches back4092 bytes to word166; word1190 jumps back
to root-copy word79. Earlier small-tree exits remain. Since2^24=341*49200+16,
the repeated loop executes49200 times. The backwards BNE uses its full signed
13-bit range without splitting the loop into extra jumps.

The retained prefix costs49 instructions and154 cycles. Including the repeated
loop and terminal root jump, parents cost1024*g+50 instructions,3411*g+155
cycles and341*g+15 public queries. Full commitment costs637583456 instructions
and1761656921 cycles; opening costs48664 cycles. The claimed score is
(1761656921+48664)*102400=180398651904000. This saves2047950 commitment cycles
relative to the eight-parent source. Instruction allowance8589935616 leaves
7952352160 spare steps. Public compression queries remain150994943.

ParentGroupBranch, ParentGroupLoop, ParentGroupPrefix, ParentGroupPlan,
ParentGroupComplete and ParentGroupSchedule prove generic schedules using the
actual decoded branches, arbitrary oracle replies and exact resources.
ParentGroupTree transports the existing leaf/reference frames and serializes
the root. Group341Schedule, Group341Tree and Group341Image instantiate those
lemmas against the delivered image. Group341Words represents the long repeated
image as a finite literal head and indexed repeated body. Group341Encoding
proves in ordinary Lean that this image equals assemble(commitCode24), and
proves the indexed instruction fetches without repeatedly expanding the large
assembler. The fixed candidate image is exactly those words, and Solution must
still prove equality with Artifact generated from programs.json.

For other development depths the builder uses this schedule only when depth
is4 modulo10, retaining the prior eight-parent schedule otherwise. Independent
machine simulation at depths4 and14 compares both schedules' complete query
traces, final memory, registers, PC, randomness consumption and resource deltas.
Those checks support development; they do not constitute official verification.
The full certificate retains the machine-derived completeness, binding and
hiding proofs. Official verifier receipts are recorded in the submission note.
