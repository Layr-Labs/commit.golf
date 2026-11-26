import CommitGolfCandidate.TruncWireImage
import CommitGolfCandidate.S3LateCheckLeafFirst

namespace CommitGolfCandidate.Late.Check3.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W AddrOK)
set_option maxRecDepth 4000
attribute [local irreducible] Normal.Runs readBuffer

def stable : List Reg := [.x19,.x20,.x21,.x24,.x26,.x27,.x30]
structure LeafEnd (o : Oracle) (s t : MachineState) (i : Index) (salt : Salt) (v : CommitGolf.Entry) (link a p n : Nat) : Prop where
  budget : n≤50
  runs : Normal.Runs o s t n 4
  pc : t.pc=pcAt link
  valPtr : t.getReg .x8=W (a+256)
  proofPtr : t.getReg .x25=W (p+24)
  keep : ∀ reg∈stable, t.getReg reg=s.getReg reg
  high : High s t
  digest : readBuffer t 256 32=leaf o.compression (i.val.testBit 0) salt v

private theorem returnRun (s : MachineState) (link : Nat) (allowed : link=26 ∨ link=218)
    (pc : s.pc=pcAt 432) (reg : s.getReg .x1=pcAt link) : Runs s (s.setPC (pcAt link)) 1 1 := by
  apply one 432 (by decide) (.JALR .x0 .x1 0) (by rfl) _ _ pc
  change some (s.setPC ((s.getReg .x1+signExtend12 0) &&& ~~~1))=_
  rw [reg];rcases allowed with rfl|rfl <;> rfl

private theorem gapKeep {s t odd} (g : Gap s t odd) : Keeps s t :=
  fun r hr=>g.keep r (by intro e;subst r;exact (by decide : ¬Reg.x12∈anchors) hr)

private theorem rowFields (t : MachineState) (odd : Bool) (salt : Salt) (a b : Digest)
    (left : readBuffer t (da odd) 32=a) (right : readBuffer t (da odd+32) 32=b)
    (gap : readBuffer t (ga odd) 8=0) (salts : readBuffer t (sa odd) 24=salt) :
    readBuffer t 160 96=finalBlock odd salt a b := by
  cases odd with
  | false=>exact even_row t 160 a b salt left right gap salts
  | true=>exact odd_row t 160 a b salt salts gap left right

private theorem advancePtrs (z : MachineState) (h : BlockResult .advance z) (a p : Nat)
    (va : z.getReg .x8=W a) (sp : z.getReg .x25=W p) :
    (Part.advance.after z).getReg .x8=W (a+256) ∧ (Part.advance.after z).getReg .x25=W (p+24) := by
  constructor
  · rw [h.regs];change z.getReg .x8+W 256=_;rw [va];exact (BitVec.ofNat_add _ _).symm
  · rw [h.regs];change z.getReg .x25+W 24=_;rw [sp];exact (BitVec.ofNat_add _ _).symm

set_option maxHeartbeats 900000
attribute [local irreducible] result copies Part.after
theorem leafRun (o : Oracle) (s : MachineState) (i : Index) (salt : Salt) (v : CommitGolf.Entry) (a p link : Nat)
    (pc : s.pc=pcAt 384) (value : s.getReg .x8=W a) (index : s.getReg .x20=W i.val)
    (sp : s.getReg .x25=W p) (scratch : s.getReg .x21=256) (reg : s.getReg .x1=pcAt link)
    (ret : link=26 ∨ link=218) (ar : AddrOK a 256) (pr : AddrOK p 24) (ah : 448≤a) (ph : 448≤p)
    (vread : readBuffer s a 256=v) (sread : readBuffer s p 24=salt) :
    ∃ t n, LeafEnd o s t i salt v link a p n := by
  let odd:=i.val.testBit 0
  obtain ⟨r,mid⟩:=middle o s v a i pc value index ar ah vread
  obtain ⟨u,n,nb,gRun,g⟩:=clearGap o r odd mid.pc mid.bit
  have k:=mid.keep.then (gapKeep g)
  have ptr : Pointers .salt u p (sa odd) := by
    constructor
    · change u.getReg .x25+0=_;exact (BitVec.add_zero _).trans ((k _ (by decide : Reg.x25∈anchors)).trans sp)
    · change u.getReg .x12+0=_;exact (BitVec.add_zero _).trans g.dest
  have dr : AddrOK (sa odd) 24 := by cases odd <;> decide
  have cp:=copies_run .salt u 3 p (sa odd) g.pc (by decide) ptr pr dr
  have copied:=copies_effect .salt u p (sa odd) 3 (by decide) ptr pr dr ((by cases odd <;> decide : sa odd+8*3≤448).trans ph)
  let t:=copies .salt u 3
  have gh : High r u:=high_write g.outside (by cases odd <;> decide) (by decide) (by cases odd <;> decide)
  have ch : High u t:=high_write copied.outside dr.1 (by decide) (by cases odd <;> decide)
  have high:=mid.high.trans (gh.trans ch)
  have anchor:=k.then (copyKeeps .salt u 3)
  have saltRead : readBuffer t (sa odd) 24=salt :=
    (copied_read copied pr.1 dr.1).trans (((mid.high.trans gh) _ _ ph pr.2).trans sread)
  have gapRead : readBuffer t (ga odd) 8=0 :=
    (Open.outside_read copied.outside dr.1 (by decide) _ _ (by cases odd <;> decide) (by cases odd <;> decide)).trans g.zero
  have keepRead (x : Nat) (fit : x+32≤MEMORY_BYTES)
      (sep1 : x+32≤ga odd ∨ ga odd+8≤x) (sep2 : x+32≤sa odd ∨ sa odd+24≤x) :
      readBuffer t x 32=readBuffer r x 32 :=
    (Open.outside_read copied.outside dr.1 (by decide) _ _ fit sep2).trans
      (Open.outside_read g.outside (by cases odd <;> decide) (by decide) _ _ fit sep1)
  let A:=o.compression (middleBlock v (o.compression (firstBlock v)))
  let B:=o.compression (lastBlock v)
  have left : readBuffer t (da odd) 32=A :=
    (keepRead _ (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)).trans mid.a
  have right : readBuffer t (da odd+32) 32=B :=
    (keepRead _ (by cases odd <;> decide) (by cases odd <;> decide) (by cases odd <;> decide)).trans mid.b
  have row := rowFields t odd salt A B left right gapRead saltRead
  have modeU : Mode u:=⟨(g.keep _ (by decide)).trans mid.mode.select,(g.keep _ (by decide)).trans mid.mode.kind,
    (g.keep _ (by decide)).trans mid.mode.width⟩
  have sc : t.getReg .x21=256 := (anchor _ (by decide)).trans scratch
  have last:=doCall o .final t 160 256 cp.2 (copiesMode .salt u 3 modeU) (by rfl)
    (by change t.getReg .x21+0=256;exact (BitVec.add_zero _).trans sc) (by decide) (by decide)
  let z:=result .final t (o.compression (readBuffer t 160 96))
  change CallResult o .final t z 160 256 at last
  have next:=basic .advance z last.pc rfl
  let q:=Part.advance.after z
  have preserve := anchor.then (callKeeps last)
  have linkQ : q.getReg .x1=pcAt link := (next.keep _ rfl).trans ((preserve _ (by decide)).trans reg)
  let out:=q.setPC (pcAt link)
  have rt:=returnRun q link ret next.pc linkQ
  have moved:=advancePtrs z next a p ((preserve _ (by decide)).trans value) ((preserve _ (by decide)).trans sp)
  have outReg (reg : Reg) : out.getReg reg=q.getReg reg := MachineState.getReg_setPC
  refine ⟨out,31+n+6+3+2+1,⟨by omega,?_,rfl,?_,?_,?_,?_,?_⟩⟩
  · have before := ((mid.runs.trans gRun).trans (Normal.deterministic o cp.1)).trans last.runs
    exact (before.trans (Normal.deterministic o next.runs)).trans (Normal.deterministic o rt)
  · exact (outReg .x8).trans moved.1
  · exact (outReg .x25).trans moved.2
  · intro j hj;apply (outReg j).trans
    have mem : j∈anchors := (by intro r;cases r <;> decide : ∀ j : Reg, j∈stable → j∈anchors) j hj
    exact (next.keep j ((by intro r;cases r <;> decide : ∀ r : Reg,r∈stable → Part.advance.equation r=Open.original r) j hj)).trans (preserve j mem)
  · exact high.trans ((last.high (by decide)).trans (High.memory (show out.mem=z.mem from next.mem)))
  · have digest := (read_congr_mem out z 256 32 (show out.mem=z.mem from next.mem)).trans last.written
    rw [row] at digest;exact digest

end CommitGolfCandidate.Late.Check3.Micro
