import CommitGolfCandidate.K1Manifest
import CommitGolfCandidate.TwoPermutationManifest

/-!
# The K1 commit image and its 4096-leaf body

The commit image is `K1Artifact.commitCode`.  Words 0..20 are the prologue (word 20 is
`addi x10,x18,56`), words 21..43,712 the body for the 4096 leaves of a tile, words 43,713..43,715
the latch, and words 45,591.. the unchanged quartet and parent stages of the record.

`packet n` is the code of leaf `n` of a tile, in program order.  A pair head (rank 0, the A leaf)
runs both first calls of its pair, the generator and its own second call; the C leaf (rank 1)
only runs its second call; a follower (rank ≥ 2) runs both of its calls with its salt copied from
the generator reply (ranks 9 and 10 through x14..x17, loaded by rank 8).
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def image : Image := ⟨ArtifactEncoding.decode 32 K1Artifact.commitCode, ArtifactEncoding.decode 8 K1Artifact.commitData⟩
theorem exact_image : image = K1Artifact.submission.image .commit := rfl
def codeWord (index : Nat) : BitVec 32 :=
  if inside : index<213314 then K1Artifact.commitCode.get 32 ⟨index,inside⟩ else 0
def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4*index)

theorem fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 213314) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (codeWord index)=some instruction) :
    fetch image state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : image.code=ArtifactEncoding.decode 32 K1Artifact.commitCode := by
    simp only [image]
  have length : index< image.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : image.code[index]?=some (K1Artifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (K1Artifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [codeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (K1Artifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all

/-- Number of heads among the first n slots of a 4096-leaf period (373 groups: 372 of eleven leaves, one of 4). -/
def heads (n : Nat) := 373*(n/4096)+((n%4096+10)/11)
def rank (n : Nat) := (n%4096)%11
/-- Register holding the constant offset from a salt-first or C leaf's second-call input (`L+56`) to its quartet
slot (1024-byte quartet blocks, one per 1024 message bytes), by slot in the quartet. -/
def sreg (n : Nat) : Reg := if n%4=0 then .x20 else if n%4=1 then .x23 else if n%4=2 then .x25 else .x26
/-- The same for an A leaf, whose second-call input is `B-56`. -/
def areg (n : Nat) : Reg := if n%4=0 then .x27 else if n%4=1 then .x28 else if n%4=2 then .x29 else .x30
/-- The next entry is `L+56`: this is an A head (its C leaf follows) or an A head follows. -/
def near (n : Nat) : Bool := rank n=0 || rank (n+1)=0
/-- Restore register after the quartet call of slot `n` (`n % 4 = 3`). -/
def rreg (n : Nat) : Reg := if near n then .x2 else .x1

/-- Head `(n%4096)/11` of a tile is keyed (generator on the key block) every 34 heads; the others are
chained (generator input = the previous head's reply, in place). -/
def keyed (n : Nat) : Bool := ((n%4096)/11)%34==0
/-- Chained heads among the first `n ≤ 4096` slots of a tile (one word shorter each). -/
def chainedBefore (n : Nat) := (n+10)/11-((n+10)/11+33)/34

/-- Code words of the ranks `0..r-1` of an 11-leaf group (keyed head), quartet calls excluded. -/
def rankPrefix (r : Nat) : Nat :=
  if r=0 then 0 else if r=1 then 14 else if r=2 then 18 else if r≤8 then 18+11*(r-2)
  else if r=9 then 99 else if r=10 then 108 else 117

/-- First code word of slot `n ≤ 4096` of the tile body (slot 4096 is the latch): even quartet calls
add two words, odd ones three. -/
def firstWord (n : Nat) := 21+117*(n/11)+rankPrefix (n%11)+2*((n+4)/8)+3*(n/8)-chainedBefore n

/-- Increment of x10 at the end of slot `n` (no quartet call): to the next entry. -/
def trail (n : Nat) : BitVec 12 := if rank n=0 then 368 else if rank (n+1)=0 then 256 else 200

/-- Load offset (from x10 = L+56) of the salt of a follower of rank `r ∈ 2..8`: `56-240 r`. -/
def saltImm (r : Nat) : BitVec 12 := BitVec.ofNat 12 (4152-240*r)

def saltCode (r : Nat) : List Instr :=
  if r≤8 then
    [.LD .x31 .x10 (saltImm r),.SD .x10 .x31 0,.LD .x31 .x10 (saltImm r+8),.SD .x10 .x31 8] ++
    (if r=8 then [.LD .x14 .x10 (-1848),.LD .x15 .x10 (-1840),.LD .x16 .x10 (-1832),.LD .x17 .x10 (-1824)] else [])
  else if r=9 then [.SD .x10 .x14 0,.SD .x10 .x15 8]
  else [.SD .x10 .x16 0,.SD .x10 .x17 8]

/-- After the second call: advance x10, or (fourth leaf of a quartet) the quartet call and the restore. -/
def tailCode (n : Nat) : List Instr :=
  if n%4=3 then
    (if (n/4)%2=0 then [.ADDI .x10 .x12 (-168),.ECALL] else [.ADDI .x10 .x12 (-168),.ADDI .x12 .x10 (-656),.ECALL]) ++
    [.ADD .x10 .x10 (rreg n)]
  else [.ADDI .x10 .x10 (trail n)]

def packet (n : Nat) : List Instr :=
  (if rank n=0 then
    [.ADDI .x12 .x10 (-256),.ECALL,.ADDI .x10 .x10 200,.ADDI .x12 .x10 (-32),.ECALL] ++
    (if keyed n then [.SD .x24 .x10 0,.ADDI .x12 .x12 (-96),.ADDI .x10 .x24 0,.ECALL]
     else [.ADD .x10 .x12 .x3,.ADDI .x12 .x12 (-96),.ECALL]) ++
    [.ADDI .x10 .x12 (-184),.SD .x10 .x10 16,.ADD .x12 .x10 (areg n),.ECALL]
  else if rank n=1 then
    [.SD .x10 .x10 16,.ADD .x12 .x10 (sreg n),.ECALL]
  else
    [.ADDI .x12 .x10 (-32),.ECALL,.ADDI .x10 .x10 56,.SD .x10 .x10 16] ++ saltCode (rank n) ++
    [.ADD .x12 .x10 (sreg n),.ECALL]) ++ tailCode n

end TwoPermutationPrototype.Grouped
