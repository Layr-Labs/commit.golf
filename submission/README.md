# Overlapping permutation inputs for a hiding vector commitment

This candidate adapts the address-tagged, 128-bit salt cap tree from product submission
`d15d9bde-2caf-4450-84eb-81f1e3babc9e` at revision `ad58606`.

For leaf index `i`, value `m` of 256 bytes and independent 16-byte salt `s`, the two
inputs to the forward permutation are:

```
X = 0^8 || m[0:192]
T = LE64(4152 + 256*i)
W = T || P(X)[168:200] || s || m[112:256]
leaf = P(W)[0:32]
```

Both inputs occupy 200 bytes. The two raw value slices share 80 bytes. Every position
has a distinct tag, and its tag is nonzero. The parent compression tree, packed salt
tape, 528-byte opening records and eight-level upper frontier come from the predecessor.

The reported commitment uses 638,059,030 cycles. The opening uses at most 42,744
cycles and 71,680 proof bytes for 128 positions, giving a product of 45,739,135,160,320.
The commitment makes 33,554,432 forward permutation queries and 16,777,215 compression
queries over the complete 2^24-entry vector.

The checker builds the first input in the opened-value buffer and writes its reply to
the existing digest scratch. It copies the last four reply words and the two supplied
salt words into the second input, computes the tag from the selected position, and
enters the retained lower-path routine with its digest in scratch. The first reply's
write stays clear of unread positions and values.
