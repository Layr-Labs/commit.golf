import CommitGolfCandidate.S4RawPair
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
structure PairFinished (o : Oracle) (x : CheckInput) (s t : MachineState) (j n q : Nat) : Prop where
  run : CheckRuns o s t n q
  pc : t.pc=pcAt 4504
  keep : ∀ r,whilePair r → t.getReg r=s.getReg r
  frame : HighExcept s t (upperAddr j) 32
  value : readBuffer t (upperAddr j) 32=batchCap .byte o.compression (readView x) j

attribute [local irreducible] lower recordAt walk List.range
theorem capDecomposition (H : Compression) (v : View) (j : Nat) :
    batchCap .byte H v j=mergePair .byte H (leftChild H v j) (rightChild H v j) (v.slot j):=by
  unfold batchCap pairAt pairChildren leftChild rightChild served firstBefore select;rfl

private theorem hashWhenPresent (H : Compression) (l r : Option Digest) (slot : Digest)
    (yes : (l.isSome || r.isSome)=true) : trim true (H (Late.parentBlock (l.getD slot) (r.getD slot)))=mergePair .byte H l r slot:=by
  have no : (l.isNone && r.isNone)=false:=by cases l <;> cases r <;> simp_all
  unfold mergePair
  rw [if_neg (by rw [no];decide)]
  exact trimIsRetained 16 _

private theorem pickValue (s : MachineState) (j : Nat) (side : Bool) (d : Option Digest) (slot : Digest)
    (raw : readBuffer s 352 32=slot) (old : ∀ w,d=some w → readBuffer s (capAddr (2*j)+selectOffset side) 32=w) :
    readBuffer s (chosenAddress j side d) 32=d.getD slot := by
  cases eqv:d with
  | none=>exact raw
  | some a=>exact old a eqv

attribute [local irreducible] readBuffer clearState tableReply batchCap mergePair

set_option maxRecDepth 5500 in
set_option maxHeartbeats 1200000 in
theorem touchedPair (o : Oracle) (x : CheckInput) (j : Nat) (bj : j<171) (s : MachineState)
    (present : touched o.compression (readView x) j=true) (pc : s.pc=pcAt 4461)
    (leftFlag : s.getReg .x3=flagBit (leftChild o.compression (readView x) j).isSome)
    (rightFlag : s.getReg .x4=flagBit (rightChild o.compression (readView x) j).isSome)
    (src : s.getReg .x29=W (capAddr (2*j))) (dst : s.getReg .x30=W (upperAddr j))
    (seen : Seen o.compression (readView x) 128 s) (slot : readBuffer s 352 32=(readView x).slot j) (env : Env x s) :
    ∃ t,PairFinished o x s t j 32 1 := by
  let v:=readView x;let l:=leftChild o.compression v j;let r:=rightChild o.compression v j
  have even : readBuffer s (chosenAddress j false l) 32=l.getD (v.slot j):=
    pickValue s j false l (v.slot j) slot (fun w h=>seen.leaves _ (by omega) w h)
  have odd : readBuffer s (chosenAddress j true r) 32=r.getD (v.slot j):=by
    apply pickValue s j true r _ slot
    intro w h
    have e:=seen.leaves (2*j+1) (by omega) w h
    rw [show capAddr (2*j)+selectOffset true=2048+32*(2*j+1) by unfold capAddr;change 2048+32*(2*j)+32=_;omega]
    exact e
  obtain ⟨t,raw⟩:=rawPair o j bj s l r (v.slot j) pc leftFlag rightFlag src dst even odd env.mode env.kind env.width
  refine ⟨t,⟨raw.run,raw.pc,raw.keep,raw.frame,raw.value.trans ?_⟩⟩
  rw [capDecomposition]
  exact hashWhenPresent o.compression l r (v.slot j) present
end CommitGolfCandidate.S4.Machine
