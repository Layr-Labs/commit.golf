import CommitGolfCandidate.S4LeafPre
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Salt Digest)
theorem Moved.subread {s t : MachineState} {src dst n : Nat} (m : Moved s t src dst n) (bound : dst+n≤2^64)
    (off k : Nat) (inside : off+k≤n) : readBuffer t (dst+off) k=readBuffer s (src+off) k :=
  (read_buffer_slice t dst n off k inside).symm.trans ((congrArg (fun v : BitVec (8*n)=>v.extractLsb' (8*off) (8*k))
    (m.read bound)).trans (read_buffer_slice s src n off k inside))
theorem fixedEffect {o : Oracle} {s t : MachineState} {pc src dst n : Nat} (f : FixedMoved s t pc src dst n)
    (low : 256≤dst) (hi : dst+8*n≤608) : LeafEffect o s t (2+2*n) 0:=by
  refine ⟨ofRuns o f.run,protectedBytes f.moved.frame low hi,?_⟩
  intro r hr
  exact f.keep r (by rintro rfl;exact hr (by decide)) (by rintro rfl;exact hr (by decide)) (by rintro rfl;exact hr (by decide))
def gapPC (b odd : Bool) := rowStart b+(if odd then 117 else 98)
def gapSize (odd : Bool) := if odd then 24 else 64
def oddStart (b odd : Bool) := rowStart b+(if odd then 109 else 80)
def firstSource (odd : Bool) := if odd then 416 else 352
def firstSize (odd : Bool) := if odd then 3 else 8
def secondSource (odd : Bool) := if odd then 352 else 416
def secondDest (odd : Bool) := if odd then 544 else 584
def secondSize (odd : Bool) := if odd then 8 else 3

attribute [local irreducible] copyPair putGap
set_option maxRecDepth 5000 in
theorem saltArm (o : Oracle) (s : MachineState) (b odd : Bool) (salt : Salt) (a d : Digest)
    (pc : s.pc=pcAt (oddStart b odd)) (left : readBuffer s 352 32=a)
    (right : readBuffer s 384 32=d) (srcSalt : readBuffer s 416 24=salt) :
    ∃ t,LeafEffect o s t (if odd then 28 else 29) 0 ∧ t.pc=pcAt (rowStart b+137) ∧
      readBuffer t 512 96=Late.finalBlock odd salt a d := by
  let n:=rowStart b
  have bound : n+140≤Code.check.count:=by cases b <;> decide
  have sites:=leafSites b
  let f:=firstSource odd;let z:=firstSize odd;let off:=gapSize odd
  let f2:=secondSource odd;let dst:=secondDest odd;let z2:=secondSize odd
  let i0:=oddStart b odd
  have c1 : Matches .check i0 (fixedCopy f 512 z):=by cases odd <;> first | exact sites.evenAB | exact sites.oddSalt
  have c2 : Matches .check (gapPC b odd) [ptrCode .x14 512,.SD .x14 .x0 (BitVec.ofNat 12 off)]:=by
    cases odd <;> first | exact sites.evenGap | exact sites.oddGap
  have c3 : Matches .check (gapPC b odd+2) (fixedCopy f2 dst z2):=by cases odd <;> first | exact sites.evenSalt | exact sites.oddAB
  have gStep : i0+(2+2*z)=gapPC b odd:=by cases odd <;> rfl
  have after : gapPC b odd+2+(2+2*z2)=n+(if odd then 137 else 108):=by cases odd <;> rfl
  let u:=copyPair s f 512 z
  have one:=fixedMove s i0 f 512 z pc (by rw [gStep];cases b <;> cases odd <;> decide) c1
    (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide) (by decide) (Or.inl (by cases odd <;> decide))
  have e1 : LeafEffect o s u (2+2*z) 0:=fixedEffect one (by decide) (by cases odd <;> decide)
  let v:=putGap u off
  obtain ⟨g,gpc,gkeep,gwrite,gzero⟩:=gapRun u (gapPC b odd) off (by cases odd <;> decide) (gStep ▸ one.pc)
    (by cases b <;> cases odd <;> decide) c2
  have eg : LeafEffect o u v 2 0:=by
    refine ⟨ofRuns o g,protectedBytes gwrite.frame (by omega) (by cases odd <;> decide),?_⟩
    intro r hr;exact gkeep r (by rintro rfl;exact hr (by decide))
  let t:=copyPair v f2 dst z2
  have two:=fixedMove v (gapPC b odd+2) f2 dst z2 gpc (by rw [after];split <;> omega) c3
    (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)
    (by cases odd <;> decide) (Or.inl (by cases odd <;> decide))
  have e2 : LeafEffect o v t (2+2*z2) 0:=fixedEffect two (by cases odd <;> decide) (by cases odd <;> decide)
  have total : LeafEffect o s t 28 0:=by
    have q:=(e1.next eg).next e2
    have h:(2+2*z)+2+(2+2*z2)=28:=by cases odd <;> decide
    rw [h] at q;exact q
  have fields : readBuffer t 512 96=Late.finalBlock odd salt a d:=by
    cases odd with
    | false=>
      apply Late.even_row t 512 a d salt
      · exact (two.moved.away (by decide) (Or.inl (by decide))).trans
          ((gwrite.away (by decide) (Or.inl (by decide))).trans ((one.moved.subread (by decide) 0 32 (by decide)).trans left))
      · exact (two.moved.away (by decide) (Or.inl (by decide))).trans
          ((gwrite.away (by decide) (Or.inl (by decide))).trans ((one.moved.subread (by decide) 32 32 (by decide)).trans right))
      · exact (two.moved.away (by decide) (Or.inl (by decide))).trans gzero
      · exact (two.moved.read (by decide)).trans ((gwrite.away (by decide) (Or.inl (by decide))).trans
          ((one.moved.away (by decide) (Or.inl (by decide))).trans srcSalt))
    | true=>
      apply Late.odd_row t 512 a d salt
      · exact (two.moved.away (by decide) (Or.inl (by decide))).trans ((gwrite.away (by decide) (Or.inl (by decide))).trans
          ((one.moved.read (by decide)).trans srcSalt))
      · exact (two.moved.away (by decide) (Or.inl (by decide))).trans gzero
      · exact (two.moved.subread (by decide) 0 32 (by decide)).trans ((gwrite.away (by decide) (Or.inl (by decide))).trans
          ((one.moved.away (by decide) (Or.inl (by decide))).trans left))
      · exact (two.moved.subread (by decide) 32 32 (by decide)).trans ((gwrite.away (by decide) (Or.inl (by decide))).trans
          ((one.moved.away (by decide) (Or.inl (by decide))).trans right))
  have endPC : t.pc=pcAt (n+(if odd then 137 else 108)):=two.pc.trans (congrArg pcAt after)
  cases odd with
  | true=>exact ⟨t,total,endPC,fields⟩
  | false=>
    have skip:=jump .check (n+108) (n+137) t endPC sites.evenEnd
    let endState:=t.setPC (pcAt (n+137))
    have done : LeafEffect o t endState 1 0:=⟨ofRuns o skip,unchangedBytes (show endState.mem=t.mem from rfl) _ _,fun _ _=>MachineState.getReg_setPC⟩
    exact ⟨endState,total.next done,rfl,(read_buffer_memory_congr endState t rfl 512 96).trans fields⟩
end CommitGolfCandidate.S4.Machine
