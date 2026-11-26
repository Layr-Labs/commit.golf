import CommitGolfCandidate.S4PairPick
import CommitGolfCandidate.S4SaltAssembly
import CommitGolfCandidate.S4RowValues
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
abbrev whilePair (r : Reg) := pairKeep r ∨ r=.x18
structure RawPair (o : Oracle) (s t : MachineState) (j : Nat) (value : Digest) : Prop where
  run : CheckRuns o s t 32 1
  pc : t.pc=pcAt 4504
  keep : ∀ r,whilePair r → t.getReg r=s.getReg r
  frame : HighExcept s t (upperAddr j) 32
  value : readBuffer t (upperAddr j) 32=value

private theorem sourceAway (j : Nat) (right left : Option Digest) (bj : j<171) :
    chosenAddress j true right+32≤2^64 ∧ (chosenAddress j true right+32≤512 ∨ 544≤chosenAddress j true right) := by
  cases right <;> simp only [chosenAddress,childPtr,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,ite_false,
    ite_true,selectOffset,capAddr] <;> omega

attribute [local irreducible] readBuffer clearState tableReply
set_option maxRecDepth 4000 in
theorem rawPair (o : Oracle) (j : Nat) (bj : j<171) (s : MachineState) (l r : Option Digest) (salt : Digest)
    (pc : s.pc=pcAt 4461) (leftFlag : s.getReg .x3=flagBit l.isSome) (rightFlag : s.getReg .x4=flagBit r.isSome)
    (src : s.getReg .x29=W (capAddr (2*j))) (dst : s.getReg .x30=W (upperAddr j))
    (even : readBuffer s (chosenAddress j false l) 32=l.getD salt)
    (odd : readBuffer s (chosenAddress j true r) 32=r.getD salt)
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96) :
    ∃ t,RawPair o s t j (trim true (o.compression (Late.parentBlock (l.getD salt) (r.getD salt)))) := by
  let u:=execInstrBr s (ptrCode .x14 512)
  have start:=stepAdd .check s 4461 .x14 .x0 512 (by decide) pc (stood pairSites.rowPtr)
  have keep1 (reg : Reg) (ne : reg≠.x14) : u.getReg reg=s.getReg reg:=keepAdd s .x14 .x0 reg _ (Ne.symm ne)
  obtain ⟨a,f⟩:=pickChild u false j l bj (addPC _ _ _ pc) rfl ((keep1 _ (by decide)).trans src) ((keep1 _ (by decide)).trans leftFlag)
  have aKeep (reg : Reg) (ne : reg∉[Reg.x6,.x14,.x15]) : a.getReg reg=s.getReg reg:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at ne
    exact (f.keep reg ne.1 ne.2.2).trans (keep1 reg ne.2.1)
  obtain ⟨b,g⟩:=pickChild a true j r bj f.pc ((f.keep _ (by decide) (by decide)).trans rfl)
    ((aKeep _ (by decide)).trans src) ((aKeep _ (by decide)).trans rightFlag)
  have bKeep (reg : Reg) (ne : reg∉[Reg.x6,.x14,.x15]) : b.getReg reg=s.getReg reg:=by
    have h:=ne;simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact (g.keep reg h.1 h.2.2).trans (aKeep reg ne)
  have addr14 : b.getReg .x14=W 512:=(g.keep _ (by decide) (by decide)).trans ((f.keep _ (by decide) (by decide)).trans rfl)
  obtain ⟨pad,padded⟩:=zeroRow b 4486 g.pc addr14 (by decide) pairSites.zero
  let c:=clearState b 4
  have keep (reg : Reg) (ne : reg∉[Reg.x6,.x14,.x15]):c.getReg reg=s.getReg reg:=(pad.regs reg).trans (bKeep reg ne)
  have readRight : readBuffer a (chosenAddress j true r) 32=r.getD salt:=by
    have bounds:=sourceAway j r l bj
    exact (f.copy.away bounds.1 bounds.2).trans ((read_buffer_memory_congr u s rfl _ _).trans odd)
  have row : readBuffer c 512 96=Late.parentBlock (l.getD salt) (r.getD salt):=by
    have lo : readBuffer c 512 32=l.getD salt:=(pad.outside.read (by decide) (Or.inl (by decide))).trans
      ((g.copy.away (by decide) (Or.inl (by decide))).trans ((f.copy.read (by decide)).trans ((read_buffer_memory_congr u s rfl _ _).trans even)))
    have hi : readBuffer c 544 32=r.getD salt:=(pad.outside.read (by decide) (Or.inl (by decide))).trans ((g.copy.read (by decide)).trans readRight)
    have sub:=Late.readTriple c 512
    change readBuffer c 512 96=readBuffer c 576 32 ++ readBuffer c 544 32 ++ readBuffer c 512 32 at sub
    have zero : readBuffer c 576 32=0:=padded
    rw [zero,lo,hi] at sub;exact sub
  have call:=tableHash o c 4490 (upperAddr j) true pad.pc (by decide) pairSites.hash
    ((keep _ (by decide)).trans mode) ((keep _ (by decide)).trans kind) ((keep _ (by decide)).trans len)
    ((pad.regs .x14).trans addr14) ((keep _ (by decide)).trans dst) ⟨by unfold upperAddr;omega,by unfold upperAddr MEMORY_BYTES;omega⟩
  let z:=tableReply o c 4490 (upperAddr j) true
  let t:=z.setPC (pcAt 4504)
  have skip:=jump .check 4494 4504 z call.pc pairSites.touchedEnd
  have data : readBuffer t (upperAddr j) 32=trim true (o.compression (Late.parentBlock (l.getD salt) (r.getD salt))):=
    (read_buffer_memory_congr t z rfl _ _).trans (call.value.trans (congrArg (fun w=>trim true (o.compression w)) row))
  have pre : HighExcept s c (upperAddr j) 32:=
    (highOnly (unchangedBytes (show u.mem=s.mem from rfl) 0 0) (by decide)).trans
      ((highOnly f.copy.frame (by decide)).trans ((highOnly g.copy.frame (by decide)).trans (highOnly pad.outside (by decide))))
  refine ⟨t,⟨?_,rfl,?_,?_,?_⟩⟩
  · exact (((ofRuns o ((start.trans f.run).trans g.run)).trans (ofRuns o pad.run)).trans call.run).trans (ofRuns o skip)
  · intro reg allowed
    have safe : ∀ reg : Reg,whilePair reg → reg≠.x10 ∧ reg≠.x12 ∧ reg∉[Reg.x6,.x14,.x15]:=by intro reg;cases reg <;> decide
    have h:=safe reg allowed;exact MachineState.getReg_setPC.trans ((call.keep reg h.1 h.2.1).trans (keep reg h.2.2))
  · exact pre.trans (highWrite call.outside)
  · exact data
end CommitGolfCandidate.S4.Machine
