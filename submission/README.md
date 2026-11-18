# Prefetched quartet commitment with 368-byte slots

The commitment takes 518,591,774 cycles. For 128 positions the opening takes at most 78,794 cycles and contains at most 72,192 bytes. The Product is 37,443,865,645,056. The positions 131,072 × j for j from zero through 127 attain both opening bounds.

This entry trims the per-position salt pass by one instruction: `slli rank,4; add 1536` with the
rank-0 fixup at `200 + 1536 = 1736` and salt loads at `-16`/`-8` replace `addi rank,-1; slli 4;
add 1536` with a `184` fixup and loads at `0`/`8`. The addresses read are unchanged, `a2 = 1536`
(the group-reply buffer) is not moved, so every salt, record and proof byte is unchanged; the block
stays 762 words (NOP at 761) so all downstream PCs are unchanged. One instruction per opened
position, −128 cycles. `GroupOpenStep` proves the base-register lemmas and `GroupOpenSelect`
re-proves `chosen`, `copy_legal` and `copied_mem` for the negative immediates.

The commitment uses the 368-byte quartet slots and 4,096-leaf tiles of PR 164. Each tile crosses 92 quartet-pointer windows. Reading the first eight salts relative to the leaf pointer and prefetching the last two salts into registers removes 187 salt-pointer writes per tile. Across 4,096 tiles this saves 765,952 cycles.

The 534-byte proof records cycle through four destination alignments. Four paths select aligned 8-, 4-, and 2-byte loads and stores. They execute 404, 532, 446 and 532 instructions. Each path includes one four-cycle multiply for the 368-byte slot address. The 128-record writer therefore costs 61,632 cycles. The upper cap walk, proof format and checker follow PR 164.

The record execution proof tracks instruction fuel separately from RV64 cycle charges. PhaseBridge checks the delivered instruction table. PhaseContext proves the written proof bytes and restores the execution state needed by the cap walk for every opening cardinality. Solution proves the stated bounds for the submitted programs.

## Provenance

The direct public base is @kaankolcu's PR 164, submission 4dbc847a-414f-41f2-854d-79e6c80f26fc at commit 9d18b75ec02d707254c81a834cd3898fbffeeeb8. It supplies the 368-byte layout, its pointer arithmetic and memory bounds, the commitment and hiding and binding proofs, the opening semantics, and the verifier.

The register-prefetch commit and four-phase opening proofs derive from our frozen 4,096-leaf quartet implementation. That implementation uses @kaankolcu's PR 160 at 78742d21cab7e048823cf47567a6381f4da82766 and PR 157 at 795b5d66793d3c546c3cfe3fd725b220bb5fb30f. The keyed salt groups and their opening proof originate with @dadon's PR 144, submission 2b2405a1. The public lineage also includes @kaankolcu's bc5cc89e, b64a994e, c08b0128 and 33bdbed6 and @dadon's 20182e74 and c28dd9ca. PR 164 credits AdamGagol's 1a9bc5f4 for an independent use of 368-byte quartet blocks.
