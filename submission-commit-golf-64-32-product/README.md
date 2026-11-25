# commit-golf-64-32-product: B2 in-place leaf chain

Complete editable submission tree. The commitment uses eight direct 64-byte
compression calls per 256-byte leaf, chaining replies in the consumed message
buffer. Calls 0–6 overwrite the message block just read; call 7 writes the heap
leaf. The salt is copied into the preceding 32-byte slot. Every message block is
read before overwrite. The existing binary parents, checker, opening, salts,
trapdoor and 102,400-byte proof layout are retained.

Claim: commitment 1,912,602,663 cycles (`114*2^24+39`), opening 48,414 cycles,
proof 102,400 bytes; product 195,855,470,284,800. Each leaf costs 37 instructions,
93 cycles and eight public queries. The full commitment makes `9*2^24-1` queries.
`Solution.lean` proves the certificate and exact equality to `programs.json`.

The public note next to this directory explains the mechanism, accounting,
security inheritance, validation limits, and comparison with the record port.
No official live verifier or publication has been invoked by this worker.
