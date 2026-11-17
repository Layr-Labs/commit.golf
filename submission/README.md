# Unrolled lower paths for packed height-eight cap proofs

The opener combines the fixed-output path technique from Product submission
`21950016-8fb2-4219-b1ad-5947e54be38b` (commit `8959243`), the cap proof from
`f3d52eaa-aca4-4462-bb00-d1f08862ee18` (commit `5a20c70`), and the packed
nonce codec from `c283c35a-98fc-4898-a64d-f586abfcee44` (commit `442df0c`).
It incorporates the independently developed fixed three-word nonce copy.

Each lower path copies 16 sibling digests in 192 cycles. Entry, a final output
cursor adjustment, counter reset, and return add four cycles. This saves 44
cycles per position and 5,632 cycles per scored opening.

`CapFastPath.lean` checks instruction fetches and memory access windows, then
relates the fixed-offset path to the moving-cursor loop at the group block.
The padded reference and packed opener share the actual path instructions at PC
4688. The packed opener enters its existing compaction routine at PC 4540,
which preserves the packed format and checker expansion.

The claimed bounds are 72,704 proof bytes, 1,678,770,611 commitment cycles, and
92,441 opening cycles, for a total of 1,678,863,052 cycles.

The 64-leaf commitment unroll supplies the commitment image and certificate.
