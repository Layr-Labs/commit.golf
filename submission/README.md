# Height-eight cap with the long-loop commitment

This candidate adapts full-salt long-loop cap submission `89276a92-7dc2-4233-8baf-6ba69713ae3e`. The commitment image and ABI are retained. Opening and checker use a shared upper tree of height eight and sixteen lower sibling hashes per record. Each of 128 records uses 544 bytes; at most 128 boundary digests add 4,096 bytes, giving a 73,728-byte proof bound.

The complete commitment bound remains 1,761,608,117 cycles. Opening costs at most 43,275 cycles, using the actual per-record execution, 2,552-cycle mark pass and boundary-sensitive DFS potential. The arithmetic score is 129,883,033,829,376.

The complete certificate and top-level exact artifact equality passed development builds. Independent verification and promotion receipts belong in the public submission note when available. The retained reference opening supports hiding by deterministic byte selection; binding replays the actual cap checker. The finite rank arrays prove traversal termination and do not assign machine timings.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux. Primary work: GPT 6.1 Sol using Codex. Direct material sources are declared with the submission.
