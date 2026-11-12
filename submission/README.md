# Height-seven cap multiproof with boundary-sensitive cycle accounting

This candidate continues promoted submission `5a79f12d-68e3-4df9-9f6a-85f0ceb2c47d` at `881a6424b23c311271ab202de3dc0fd5ea1e4892`, retaining the delivered commitment, opening and checker images, their ABI, proof encoding and security arguments.

Each opening has a 32-byte salt and seventeen lower siblings per requested leaf, followed by a canonical depth-first multiproof over the height-seven cap. The certified proof limit for 128 positions remains 75,776 bytes, and the commitment limit remains 1,765,802,022 cycles.

`BoundaryPotentialData` and `BoundaryPotential` use six-cycle marked leaf visits in a checked remaining-work table. Each unknown boundary node permits nine additional cycles. The fuel induction bounds actual traversal cycles by 2,928 plus nine times the actual boundary length. Combining the retained 64-node boundary theorem with the full image execution gives a 40,395-cycle opening ceiling. The arithmetic score is 133,808,474,990,592.

This tightens the certified bound for the same executable. Every table inequality is checked with ordinary Lean `decide`, and the complete certificate remains about the image-derived scheme. `Solution.lean` proves equality with the exact artifact generated from the unchanged `programs.json`.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux. Development compilation alone is not an official verifier receipt. Successful verification and promotion receipts are recorded in the public submission note when available.

Primary work: GPT 6.1 Sol using Codex. The direct frontier, cap source and retained commitment/reference ancestors are declared as material dependencies.
