import CommitGolfCandidate.K3OpenChainRun
import CommitGolfCandidate.K3OpenChainExit
import CommitGolfCandidate.K3OpenChainReply
/-! (Re-export of the K3OpenChain* files.) Opener prefix, salt regeneration of one position on the linked (chain) schedule: rows
`chainStart .. chainStart+18`. With `n = i % 4096`, `r = n % 11` (rank), `h = n / 11` (head in the tile),
`j = h % 34` (links after the keyed restart):
```
remu x28,x6,x26 ; divu x30,x28,x29 ; remu x28,x28,x29 ; addi x31,x0,34 ; remu x30,x30,x31 ; mul x31,x30,x29 ;
sub x7,x6,x28 ; sub x7,x7,x31 ; addi x7,x7,1 ; slli x7,x7,8 ; add x7,x7,x26 ; sd x7,0(x10) ; ecall ;
beq x30,x0,+24 ; addi x10,x12,0 ; L: ecall ; addi x30,x30,-1 ; bne x30,x0,L ; addi x10,x0,1024
```
the keyed generator call of head `h - j` (counter = base of its C leaf, K1 input layout at word 128, reply at
`[1536, 1736)`), then `j` in-place links on `[1536, 1736)`. The counter arithmetic and the reply of the
restart-plus-links walk are S9-K6P's `K6Chain.restart_counter` / `K6Chain.opener_chain`. -/
namespace TwoPermutationPrototype.GroupedOpening
-- Frozen interface: `chainStart`, `chainLinks`, `chainSteps`, `chainCalls`, `chainCycles`, `chainReply`, `ChainEntry`,
-- `KeyWords`, `chainTrace`, `chainState` (K3OpenChainRows); `chain_run` (K3OpenChainRun);
-- `chain_fixed` (K3OpenChainPost); `chain_post` (K3OpenChainExit); `chain_reply` (K3OpenChainReply).
end TwoPermutationPrototype.GroupedOpening
