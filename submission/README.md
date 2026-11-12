# Direct known-leaf branch with the height-eight nonce cap

This candidate continues nonce-cap submission `22d9ffe0-7574-4d70-8775-2d4115ac3244` (source `62e70a5`). The branch optimization was developed on `89276a92-7dc2-4233-8baf-6ba69713ae3e` and adapted to the height-eight geometry of `7d23b7fa-bd9a-4605-9b5a-5281ce09127c`. These material sources are declared with the submission.

Opening and checking use BGEU to branch directly to advance for known cap leaves. Marked internal nodes fall through to the node shift and return to visit. One unreachable NOP preserves all later addresses. Exactly four words change in each image; commitment, padded 192-bit nonce construction and proof encoding remain those of the direct predecessor.

Known leaves cost five cycles including occupancy lookup. The updated full-traversal potential is 5,616, with ten units per boundary digest. At most 128 boundaries gives 6,896 traversal cycles. The proposed limits are 73,728 proof bytes, 1,728,053,684 commitment cycles and 43,531 opening cycles, giving arithmetic score 127,409,151,467,520. These need the final complete certificate and official verifier receipt, which are recorded separately in the public submission note.

The same optimization passed complete development certificates and exact regenerated-artifact equality on the preceding full-salt height-seven and height-eight sources. The final nonce composition is checked independently. No contract or verifier checks are changed.
