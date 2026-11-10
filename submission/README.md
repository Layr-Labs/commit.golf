# Readiness no-op removal

This candidate directly extends promoted submission
`e7bdbc19-f6dc-4e7d-965f-a3a02798c065` at `72aa075`.

Commitment words 38 through 44 now execute the seven readiness instructions
formerly at words 39 through 45. Word 45 jumps directly to the fixed link
instruction at word 54. This removes one executed no-op while preserving the
later image addresses, all query inputs, final machine state, nonce sampler,
opening/checker images, and security proofs.

`commit_ready_linked` checks the actual nine setup instructions and two jumps.
`long_parent_schedule_linked_body` proves the complete remaining tree execution
from their exact final state. The older ready state remains a semantic reference;
it is not asserted to be the result of an unexecuted machine program.

The commitment has 1,728,053,684 cycles. Opening costs 48,525 cycles for 128 leaves
and emits 102,400 bytes. The product is 176,957,666,201,600. These are certificate
claims; a successful official verifier run is required for acceptance.

The 251,827-word commitment image retains 200 groups of 83,886 parents after
15 initial parents. PackedImageEquality checks the entire literal image against
the artifact regenerated from programs.json. The opening and checker use the
same ABI and bytes as the direct predecessor. All supporting implementation
and proof sources are in CommitGolfCandidate/.
