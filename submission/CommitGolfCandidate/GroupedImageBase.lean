import CommitGolfCandidate.GroupedManifest
import CommitGolfCandidate.TwoPermutationManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def image : Image := ⟨ArtifactEncoding.decode 32 GroupedArtifact.commitCode, ArtifactEncoding.decode 8 GroupedArtifact.commitData⟩
theorem exact_image : image = GroupedArtifact.submission.image .commit := rfl
def codeWord (index : Nat) : BitVec 32 :=
  if inside : index<201767 then GroupedArtifact.commitCode.get 32 ⟨index,inside⟩ else 0
def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4*index)

theorem fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 201767) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (codeWord index)=some instruction) :
    fetch image state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : image.code=ArtifactEncoding.decode 32 GroupedArtifact.commitCode := by
    simp only [image]
  have length : index< image.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : image.code[index]?=some (GroupedArtifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (GroupedArtifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [codeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (GroupedArtifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all



/-- Number of heads among the first n slots of a 4096-leaf period (373 groups: 372 of eleven leaves, one of 4). -/
def heads (n : Nat) := 373*(n/4096)+((n%4096+10)/11)
def rank (n : Nat) := (n%4096)%11
def pairPos (n : Nat) := (n%4096)%22
def pairHeads (n : Nat) := 187*(n/4096)+(n%4096+21)/22
/-- Byte offset of leaf slot n inside the quartet blocks of one body (368-byte blocks). -/
def slotOff (n : Nat) := 368*(n/4)+72+32*(n%4)
/-- Number of quartet-pointer rebases (4,096-byte windows) before leaf slot n of a body. -/
def rb (n : Nat) := slotOff n/4096
/-- Leaf slot n is followed by a rebase of the quartet pointer. -/
def rebase (n : Nat) : Prop := rb (n+1) ≠ rb n
instance (n : Nat) : Decidable (rebase n) := inferInstanceAs (Decidable (_ ≠ _))
def firstWord (n : Nat) := 21+11*n+pairHeads n+rb n
def heapImm (n : Nat) := BitVec.ofNat 12 (2048+slotOff n-4096*rb n)
def sourceImm (n : Nat) := BitVec.ofNat 12 (2560+2816*((n%4096/11)%2)+16*(rank n-1))

def packet (n : Nat) : List Instr :=
  [.ADDI .x12 .x10 (-32),.ECALL] ++
  (if rank n=0 then
    [.SD .x24 .x10 0,.ADDI .x12 .x10 (-120),.ADDI .x10 .x24 0,.ECALL] ++ (if pairPos n=0 then [.ADDI .x7 .x12 1536] else []) ++
     [.ADDI .x10 .x12 176,.SD .x10 .x10 0]
  else [.ADDI .x10 .x10 56,.SD .x10 .x10 0,.LD .x31 .x7 (sourceImm n),
    .SD .x10 .x31 8,.LD .x31 .x7 (sourceImm n+8),.SD .x10 .x31 16]) ++
  [.ADDI .x12 .x20 (heapImm n),.ECALL,.ADDI .x10 .x10 200] ++
  (if rebase n then [.ADD .x20 .x20 .x23] else [])

/-! ## Pair heads: the leaf body runs 2,048 pair packets (even leaf 2p, odd leaf 2p+1) per 4,096-leaf body. -/

/-- Pair `p` of a body is a head pair (one generator call fills both leaves' salts in place): pairs 11m, 11m+5. -/
abbrev pairHead (p : Nat) : Prop := p%11=0 ∨ p%11=5
/-- Head pairs among the first `p` pairs of a body. -/
def headsBefore (p : Nat) := 2*(p/11)+(if p%11=0 then 0 else if p%11≤5 then 1 else 2)
/-- Prefetching heads: pair 11m (m ≤ 185) loads its table salt 8 into a6,a7 and pair 11m+5 into a4,a5, for pair 11m+10. -/
def prefetchA (p : Nat) : Prop := p%11=0 ∧ p<2046
instance (p : Nat) : Decidable (prefetchA p) := inferInstanceAs (Decidable (p%11=0 ∧ p<2046))
/-- Pairs 11m+10 store both salts from the prefetched registers a4..a7. -/
def fromRegs (p : Nat) : Prop := p%11=10
instance (p : Nat) : Decidable (fromRegs p) := inferInstanceAs (Decidable (p%11=10))
/-- First word of pair packet `p` (`p < 2048`): non-head packets have 22 words, prefetching heads 20, pairs 11m+10
and the last head (2,046) 18, plus the quartet rebases before leaf `2p` (368-byte blocks: 92 per body). -/
def pairWord (p : Nat) := 21+22*p+rb (2*p)-2*headsBefore p-4*(p/11)-(if 2046<p then 2 else 0)
/-- Index of leaf `n`'s salt among its group's copied salts (non-head pairs): 0..8 own table, 9 = previous table. -/
def copyIndex (n : Nat) : Nat :=
  let r := (n/2)%11
  2*((if r<5 then r else r-5)-1)+n%2
/-- Position of local leaf `n`'s pair inside its salt group (0 = head). -/
def localK (n : Nat) : Nat :=
  let r := (n/2)%11
  if r<5 then r else r-5
/-- a2-relative immediate of leaf `n`'s copied salt (a2 = the odd entry − 32 bytes; table salt `c` of the head `k`
pairs back sits 512k + 72 − 16c bytes below). -/
def srcImm (n : Nat) : BitVec 12 := BitVec.ofNat 12 (4096-(512*localK n+72-16*copyIndex n))

def pairPacket (p : Nat) : List Instr :=
  [.ADDI .x10 .x10 256,.ADDI .x12 .x10 (-256),.ECALL,.ADDI .x10 .x10 200,.ADDI .x12 .x10 (-32),.ECALL] ++
  (if pairHead p then
    [.SD .x24 .x10 0,.ADDI .x12 .x10 (-120),.ADDI .x10 .x24 0,.ECALL] ++
    (if prefetchA p then [.LD .x16 .x12 144,.LD .x17 .x12 152]
     else if p%11=5 then [.LD .x14 .x12 144,.LD .x15 .x12 152] else []) ++
    [.ADDI .x10 .x12 (-184)]
  else if fromRegs p then
    [.SD .x10 .x14 (-120),.SD .x10 .x15 (-112),.SD .x10 .x16 64,.SD .x10 .x17 72,.ADDI .x10 .x10 (-304)]
  else
    [.LD .x31 .x12 (srcImm (2*p)),.SD .x10 .x31 (-120),.LD .x31 .x12 (srcImm (2*p)+8),.SD .x10 .x31 (-112),
     .LD .x31 .x12 (srcImm (2*p+1)),.SD .x10 .x31 64,.LD .x31 .x12 (srcImm (2*p+1)+8),.SD .x10 .x31 72,
     .ADDI .x10 .x10 (-304)]) ++
  [.SD .x10 .x10 0,.ADDI .x12 .x20 (heapImm (2*p)),.ECALL] ++
  (if rebase (2*p) then [.ADD .x20 .x20 .x23] else []) ++
  [.ADDI .x10 .x10 360,.SD .x10 .x10 0,.ADDI .x12 .x20 (heapImm (2*p+1)),.ECALL] ++
  (if rebase (2*p+1) then [.ADD .x20 .x20 .x23] else [])

end TwoPermutationPrototype.Grouped
