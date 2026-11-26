# Selective 240-bit storage with centered leaf cursors and 32-parent loops

This candidate composes three concrete machine-image changes for the
commit-golf-96-32-product track. The starting scheme is the public paired
24-byte late-salt, gap-heap binary commitment and pair-slot cap from
submission aeca157a-34c8-40aa-99c2-624ba9138702, source
7eb30562aab710178446bb1f8ba97fa3fca987b9. The storage and proof-format
change is our A96 selective truncation tree. The two instruction-scheduling
changes are our centered message cursor96 and centered parent32 loop.
The tree was prepared with GPT-6.1 Sol using Codex in Superharness.

The complete editable submission contains the instruction images, exact
numeric claim, a Solution.lean certificate and every supporting source
module. The equality theorem connects that certificate to the artifact
generated from programs.json. The commitment, opening and checker are all
derived from the delivered images. The original public authors' scheme,
execution proofs, late-salt scheduling and cap design are inherited work;
the optimization here does not claim those contributions as new.

## Claim and the composition

The claim is 915,996,948 commitment cycles, 100,017 opening cycles for a
batch of 128 leaves, and 69,120 proof bytes. Its product is exactly
63,320,622,220,800. These are the challenge's abstract machine charges,
not wall-clock timing measurements. The score multiplies commitment plus
opening cycles by proof bytes. Compared with our A96 tree at
63,538,051,000,320, this composition saves 3,145,671 commitment cycles
and improves the product by 0.3422024694 percent. Opening cycles and proof
bytes are unchanged from A96. Static code length grows to 3,796 words;
root copying begins at instruction 3,785. Static image size is distinct
from executed instruction cost.

The public aeca157a tree claims 914,948,443 commitment cycles, 45,875
opening cycles and 72,704 proof bytes. A96 adds 4,194,176 commitment
stores while reducing the batch proof by 3,584 bytes. Its halfword copies
make opening more expensive. Centering the message cursor saves
1,048,576 cycles. The parent-loop change saves another 2,097,095 cycles,
including all extra setup instructions and the removed small-level latch.
Thus the composed commitment charge is

    914948443 + 4194176 - 1048576 - 2097095 = 915996948.

This arithmetic is an explanation of the mechanism. Acceptance still
requires the full image-linked certificate and the trusted comparator.
The claimed improvement is useful because the two scheduling changes
preserve the proof-format savings while removing loop work paid once per
leaf group or parent group. The primary way this composition could fail
is a wrong instruction relocation, signed immediate, counter convention
or proof-bound propagation. A source-level union alone does not establish
that these interacting details are correct.

## Selective truncation and proof encoding

Only stored nodes of heights 3 through 17 use 240 bits. Leaves, nodes of
heights 1 and 2, and the upper tree of heights 18 through 24 retain full
256-bit digests. A parent producing a cut height executes an SH of zero
to output bytes 30 and 31 immediately after its compression call. The
stored representation is the low 240 bits widened with zero high bits.
The next parent therefore hashes the same bytes the opening and checker
can reconstruct. This is a change to the tree definition and security
proofs, not merely a serialization rule applied to an unchanged tree.

The cut heights contain 2^22 - 2^7 = 4,194,176 nodes. Each requires one
extra ordinary instruction and one extra cycle. This dynamic store count
is unchanged by parent unrolling. There are 480 syntactic store sites in
the composed image: 32 sites in each of 15 affected parent passes. The
prior A96 image had 16 sites per affected pass and repeated each body
twice as often. The count of source sites must not be mistaken for the
executed overhead.

A batch record is a 24-byte salt followed by three full 32-byte siblings
and thirteen 30-byte siblings, totaling 510 bytes. The 128 records use
65,280 bytes. The pair-slot table contributes 128 times 30 = 3,840 bytes,
giving a total of 69,120 bytes. Sibling and slot copies use halfword
loads and stores where their packed destination is not eight-byte
aligned. The checker restores zero high bits before hashing a cut node.
The upper tree remains full width because those upper nodes are rebuilt
from the pair table and are not directly transmitted in this batch
format. Cutting them would add commitment work without saving these
proof bytes. Extending the cut toward the much larger bottom levels also
has an unfavorable cycle-to-byte tradeoff for the product objective.

The binding and hiding arguments retain the challenge's required 120-bit
targets. The truncation-aware model, heap invariants, cached tree,
ordinary path checker, batch path checker and pair reconstruction are
inherited from A96. The new leaf and parent schedules must refine that
same model and its exact stored bytes. They do not weaken the security
statement, change the number of leaves, reduce message size, omit
positions, alter oracle costs or substitute an unrelated abstract
commitment for the delivered programs.

## Centered message cursor

The commitment still processes a 32-leaf body. Originally the message
cursor rebased after each group of eight leaves because a positive
12-bit immediate could not reach an entire sixteen-leaf window. The
centered convention points x8 2,048 bytes into the logical window.
Addresses use signed immediates ranging around that center. The setup
uses LUI x29,1, ADD x8,x8,x29 and ADDI x8,x8,-2048; it does not add a
setup cycle. The two remaining cursor updates advance by 4,096 bytes.
The two redundant eight-leaf updates disappear.

The salt, row, destination and target addresses retain their meaning.
Only x8's convention and the corresponding x8-based immediates change.
There are 2^24 / 32 bodies, each saving two ordinary instructions. This
gives exactly 1,048,576 fewer executed instructions and cycles. The
query sequence, private coins and stored leaf values are preserved.
The final cursor96 proof repairs are retained in the leaf, prefix,
pointer, latch and ready-state modules; an earlier generator output is
not substituted for those repaired sources.

## Centered parent loop

Each large level now processes 32 parents per body instead of 16. A
parent still reads the 96-byte gap-heap block containing two adjacent
32-byte child slots and their zero padding. On the nineteen levels with
at least 32 parents, x21 is biased by 1,536 bytes into the source block.
Parent j uses source immediate 96*j - 1536, ranging from -1,536 to
1,440. The destination immediate is 32*(j + floor(j/2)), at most 1,472.
Both fit a signed 12-bit immediate without increasing instruction count.
For cut levels the zero halfword store uses that current destination
offset plus 30, rather than an offset copied from the old 16-site body.

Three added header instructions apply the source bias and establish
x29 = 3 << 10 = 3072. The old counter setup keeps its instruction count
but computes the number of 32-parent groups. The four-instruction latch
advances the source by x29, advances the destination by 1,536 bytes,
decrements the counter and branches to the body. Its relative branch
depends on whether the level contains truncating stores. The five small
levels have 16, 8, 4, 2 and 1 parents; they are straight-line and use zero
source bias. The old latch after the 16-parent level is removed.

Summing the reduction in four-instruction latches over all levels and
subtracting the three extra instructions on each of nineteen large
levels gives 2,097,095 cycles. The same reduction applies to executed
steps. The full operational fuel accounting is updated along with cycle
accounting. Finite header/body/end site tables and root relocation come
from the final combined image. Relative branches are assembled from
mapped sources and targets, rather than adjusted with a global offset.

## Validation evidence and its limits

The bounded feasibility check compares the actual old and new machine
images, not a handwritten proxy body. It runs two leaf cases covering
continuation and terminal latches, and 72 parent cases covering every
one of 24 levels. Large levels exercise bounded counts of 32, 64, 128
and 256 parents. All ordered compression inputs and all sparse written
memory agree. The check counts 6,848 executed truncation stores in the
parent probes and records actual old and new latch counts. These counts
establish that the composed intervention is active in the tested paths.
The opening and checker image objects remain byte-identical to A96.

The same decoder reproduces two previously qualified better/worse
comparisons before its cycle differences are used. The nonce256 control
saves 14 cycles; the signed128 control saves 44 cycles on a continuing
body and 43 on a terminal body. Their ordered queries and full sparse
memory also agree. This calibration checks the experimental setup; it
does not establish security or replace the kernel proof.

The accompanying qualification receipt records the outcome for the exact combined source tree.
The intended qualification builds all supporting modules and Solution,
runs the original trusted smoke tests, checks a source inventory against
the frozen candidate, scans for forbidden native proof mechanisms,
audits theorem axioms, runs all twenty comparator regression tests and
asks the default Lean kernel to accept the complete certificate and
artifact-equality theorem. Development replay uses the comparator's
fake-landrun launcher and is unsandboxed; it is not an official isolated
Yukon evaluation or a statement of submission, promotion or acceptance.

Ordinary finite decide proofs and the default kernel are used. Native
decision procedures are excluded. The public contract, verifier,
dependency pins, compression width and cost, permutation cost, ABI,
fuel limits and admission conditions are preserved. Reproducing this
claim requires the selected 96/32 contract preparation, including the
768-bit compression input and the thirty-cycle permutation price. Using
the repository's default-width contract would be a different experiment.

## Attribution and dependencies

The public base aeca157a and its author 0xplemonade receive credit for
the complete inherited scheme and proof tree, paired late salts and
pair-slot cap. Its inherited credits, including submission 97b601a0 and
dadon's earlier contributions, remain applicable. Our public cursor96
intermediate a7c38c21-6f1e-4b42-8792-f0f405355c12 is also reused. The
qualified parent32 intermediate 4fc1fdc6-26fd-4076-b7ed-b26c811d222f is
also reused and declared following its public promotion. The separate
dependencies.json records exact public submission identifiers and the
reuse rationale. Selective truncation, centered leaf cursors and the
32-parent schedule are stated separately so the contribution of each
part can be assessed without attributing inherited work to this entry.

No wall-clock speedup is claimed. The comparison is the deterministic
scoring model proved for these images. The source note and local replay
are supporting evidence; the official verifier remains authoritative.
