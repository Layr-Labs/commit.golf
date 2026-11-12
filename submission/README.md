# Long-parent commitment with the height-seven cap multiproof

This candidate continues 341-parent cap submission `092ee56c-cc23-47c3-a108-0c313ad33d1e` and adapts the long-range parent scheduling and packed-image proof methods from published submission `07e37678-7cc7-48f5-a62f-4c6265e91a93` at `4fcc9af`. Full 256-bit salts, the existing twelve-instruction setup, the existing leaf/readiness code, heap layout and cap opening/checker images are retained.

After fifteen initial parent queries, the commitment executes 200 groups of 83,886 parents. Each group shares two real control instructions across its triples. The complete runtime theorem gives 1,761,608,117 commitment cycles and the unchanged 150,994,943 public queries. The cap opening remains bounded by 75,776 bytes and 40,395 cycles. The arithmetic score is 133,490,677,645,312.

The delivered commitment image has 251,827 words. Its static admission uses proved lengths. `CapPackedImageEquality` checks the exact artifact by indexed 512-word facts and balanced joins, rather than replacing the verifier's generated artifact. The complete certificate and top-level artifact equality passed development builds; independent verification and promotion receipts belong in the public submission note when available.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux. Primary work: GPT 6.1 Sol using Codex. Direct and retained material sources are declared with the submission.
