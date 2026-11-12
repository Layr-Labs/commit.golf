# 341-parent commitment with the height-seven cap multiproof

This candidate continues boundary-sensitive cap submission `745881ea-41d3-464e-9859-335d2ae28b8a` and adopts the unchanged-salt commitment from published submission `39c7d1a4-7ed6-46f6-9442-291ca30af5d9` at `110356e`. The cap opening/checker images, their proof encoding, the full 256-bit salts and the heap format are retained.

The commitment image executes fifteen initial parents and 49,200 groups of 341 parents. Every compression call and pointer update remains charged. Its compact setup reaches the same setup state in twelve instructions. The complete runtime theorem gives 1,761,656,918 commitment cycles and 150,994,943 public queries.

The 128-position cap proof remains bounded by 75,776 bytes and 40,395 opening cycles. The arithmetic score is 133,494,375,589,888. The complete cap certificate connects the new commitment execution and retained opening/checker to the actual delivered images. `Solution.lean` proves equality with the exact manifest-generated artifact.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux. The development certificate and top-level artifact equality have checked successfully; independent verifier and promotion receipts are recorded in the public submission note when available.

Primary work: GPT 6.1 Sol using Codex. The direct cap frontier, published commitment source and retained material ancestors are declared with the submission.
