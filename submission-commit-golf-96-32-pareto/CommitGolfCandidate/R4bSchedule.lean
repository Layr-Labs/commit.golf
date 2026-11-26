import CommitGolfCandidate.R4bAddressVM
import CommitGolfCandidate.R4bWriter
import CommitGolfCandidate.S4SlotState
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Machine (W Safe indexBase proofBase byte)
open S4.Open (tdBase Sources targetAddr)

def group (h : Nat) := h/7
def part (h : Nat) := h%7
def blockIndex (i g : Nat) := i/3/(128^g)
def tableRow (i h : Nat) := 1024*group h+8*(blockIndex i (group h)%128)+part h
def virtualSlot (i key : Nat) := if key<3 then 2048+3*(key-1)+i%3 else tableRow i ((key-3)%14)
def reads (r i : Nat) : Reads where
  address k := if k=0 then indexBase+8*r else tableBase+8*virtualSlot i k
  value k := if k=0 then i else slotWord (virtualSlot i k)
theorem slotsFit (i k : Nat) : virtualSlot i k<2054 := by
  unfold virtualSlot tableRow group part
  split <;> omega
theorem memoryReads {s : MachineState} {td : Late.Trapdoor} {ps : Positions} (r : Nat) (br : r<ps.card)
    (batch : ps.card=128) (sources : Sources td ps s) (table : TableMem s) :
    let x:=reads r (recordIndex ps r).val
    ∀ k,Safe (x.address k) 8 ∧ s.getMem (W (x.address k))=W (x.value k) := by
  intro x k;by_cases z:k=0
  · subst k;refine ⟨?_,sources.index r br⟩
    change indexBase+8*r+8≤68719476736 ∧ (indexBase+8*r)%8=0;unfold indexBase;omega
  · simp only [x,reads,if_neg z];let key:=virtualSlot (recordIndex ps r).val k
    have h : key<2054:=slotsFit _ _
    exact ⟨⟨by change tableBase+8*key+8≤68719476736;unfold tableBase;omega,by unfold tableBase;omega⟩,table key h⟩

def fixed (tile : Nat) : NRegs
  | .x1=>some tableBase | .x2=>some (tableBase+8192)
  | .x3=>some (Late.rowBase+72) | .x4=>some tdBase | .x5=>some 184
  | .x10=>some 96 | .x11=>some 6144 | .x13=>some (indexBase+32*tile)
  | .x16=>some (tableBase+16384) | .x27=>some 3 | _=>none
def high (i h : Nat) := (blockIndex i (group h)/128)*6144/2^(part h)
def pointer (i h : Nat) := tableBase+8192*group h+64*(blockIndex i (group h)%128)
def locals (i q : Nat) : NRegs
  | .x8=>if q=1 then some i else none
  | .x28=>if 2≤q then some (if q≤10 then i/3 else i/3/128) else none
  | .x21=>if q=2 then some (tdBase+96*(i/3)) else
      if 3≤q ∧ q<17 ∧ part (q-3)≠0 then some (high i (q-3)) else none
  | .x22=>if q=2 then some (tableBase+16384+8*(i%3)) else none
  | .x14=>if 3≤q ∧ q<17 ∧ part (q-3)≠0 then some (pointer i (q-3)) else none
  | _=>none
def env (tile i q : Nat) : NRegs := fun r => (locals i q r).or (fixed tile r)

def addressOps (lane q : Nat) : List Op :=
  if q=0 then [.ld .x8 .x13 (8*lane) 0,.shr .x6 .x8 1,.mul .x6 .x6 .x5,.add .x12 .x3 .x6,
               .mask .x6 .x8 1,.shl .x6 .x6 4,.add .x12 .x12 .x6]
  else if q=1 then [.div3 .x28 .x8,.mod3 .x7 .x8,.mul .x21 .x28 .x10,.add .x21 .x21 .x4,
               .shl .x7 .x7 3,.add .x22 .x16 .x7,.ld .x14 .x22 0 1,.add .x12 .x21 .x14]
  else if q=2 then [.ld .x14 .x22 24 2,.add .x12 .x21 .x14]
  else
    let h:=q-3;let j:=part h;let g:=group h
    (if j=0 then (if g=0 then [] else [Op.shr .x28 .x28 7])++
      [.mask .x6 .x28 7,.shl .x6 .x6 6,.add .x14 (if g=0 then .x1 else .x2) .x6,
       .shr .x21 .x28 7,.mul .x21 .x21 .x11] else [])++
    [.ld .x12 .x14 (8*j) q,.add .x12 .x12 .x21]++(if j<6 then [.shr .x21 .x21 1] else [])

def logicalSource (i q : Nat) :=
  if q=0 then Late.rowBase+72+i/2*184+(i%2)*16
  else if q<3 then tdBase+96*(i/3)+slotWord (virtualSlot i q)
  else slotWord (virtualSlot i q)+high i (q-3)

def fieldFacts (tile l i q : Nat) : Prop :=
  let x:=reads (4*tile+l) i
  let pre:=env tile i q
  let ops:=addressOps l q
  let out:=finalRegs x pre ops
  okList x pre ops ∧ out .x12=some (logicalSource i q) ∧
    ∀ r n,locals i (q+1) r=some n → out r=some n

def fieldOffset (lane q : Nat) := 510*lane+Open.offsetAt true q
def chunkCount (q : Nat) := if q=0 then 3 else 4
def outputChunk (l q j : Nat) :=
  let o:=fieldOffset l q + 8*j
  chunkOps (o%8) (min 8 (Open.widthAt true q-8*j)) (8*j) (completed o)
def fieldCode (l q : Nat) := (addressOps l q).map Op.code ++ (List.range (chunkCount q)).flatMap (outputChunk l q)
def markCode : List Instr := [.SRLI .x8 .x28 7,.ADD .x6 .x24 .x8,.SB .x6 .x25 0]
def rowCode (l : Nat) := (List.range 17).flatMap (fieldCode l)++markCode
def tileCode := (List.range 4).flatMap rowCode
end CommitGolfCandidate.R4b
