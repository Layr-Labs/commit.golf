import CommitGolfCandidate.ReconstructedOpeningHeaderFront
import CommitGolfCandidate.ReconstructedOpeningHeaderHigh
import CommitGolfCandidate.ReconstructedOpeningHeaderLow
import CommitGolfCandidate.ReconstructedOpeningHeaderWrite

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype (writeWord)
open CommitBlocks (addr)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem normal (x : Context) (q : Model) (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) :
    s357 x q=q := by
  obtain ⟨r,m⟩ := q
  unfold s357;congr 1;funext n
  cases n <;> first | rfl | exact (st.frame _ (by decide) (by decide) (by decide) (by decide)).symm

def s389 (x : Context) (q : Model) :=
  (s388 x q).store (cell (x.cursor+120)) (q.reg .x12)
def to396 (x : Context) (q : Model) := after (s389 x q) OpeningHeaderWrite.prepare
def to416 (x : Context) (q : Model) := OpeningHeaderWrite.output (to396 x q) (x.cursor+184)

private theorem storeRun (o : Oracle) (x : Context) (q : Model) (room : (x.cursor+120)/64<capacity)
    (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) (s : MachineState) (pc : s.pc=addr 388)
    (fits : Fits s (s388 x q)) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 1 s t ∧ t.pc=addr 389 ∧ Fits t (s389 x q) := by
  let w := cell (x.cursor+120)
  have limit := OpeningSaltLow.room _ room
  have loc : (s388 x q).reg .x19+signExtend12 0=wordAddress w := by
    change q.reg .x19+0=_;rw [st.dst];exact BitVec.add_zero _
  have run := OpeningLinear.write o (s388 x q) .x19 .x12 0 w (q.reg .x12) (by dsimp [w];omega) loc rfl
  exact OpeningLinear.block run (i:=388) (by decide) ⟨rfl,True.intro⟩ s pc fits

theorem low_memory (x : Context) (q : Model) (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) :
    (s389 x q).mem=put (s345 x).mem (x.cursor+120) 64 (W (partialHeader x 10)) := by
  let c := x.cursor+120
  change writeWord q.mem (cell c) (q.reg .x12)=_
  rw [st.current,st.memory,OpeningHeaderLow.finish]
  exact congrArg (put (s345 x).mem c 64) (low19 x)

def headerSteps (c : Nat) := 108+(if (c+120)%64=0 then 6 else 12)+31+1+7+OpeningHeaderWrite.steps (c+184)

theorem run (o : Oracle) (x : Context) (room : (x.cursor+184)/64<capacity) (s : MachineState) (pc : s.pc=addr 237)
    (fits : Fits s (s237 x)) :
    ∃ t q, CommitExact.Segment o OpeningStraight.image (headerSteps x.cursor) s t ∧ t.pc=addr 416 ∧
      Fits t (to416 x q) ∧ OpeningHeaderLow.Staged (s345 x) q (x.cursor+120) := by
  have room' : (x.cursor+120)/64<capacity := by omega
  obtain ⟨a,ra,pa,ha⟩ := front o x s pc fits
  obtain ⟨b,q,rb,pb,hb,st⟩ := OpeningHeaderLow.stage o (s345 x) (x.cursor+120) room' rfl rfl rfl a pa ha
  have hb' : Fits b (s357 x q) := (normal x q st).symm ▸ hb
  obtain ⟨d,rd,pd,hd⟩ := OpeningLinear.block (carryRun o x q) (i:=357) (by decide) carryTable b pb hb'
  obtain ⟨e,re,pe,he⟩ := storeRun o x q room' st d pd hd
  obtain ⟨f,rf,pf,hf⟩ := OpeningHeaderWrite.prepareRun o (s389 x q) e pe he
  have limit : x.cursor+184<2^64 := by unfold capacity at room;omega
  obtain ⟨off,ptr,_⟩ := OpeningHeaderWrite.prepared (s389 x q) x.cursor limit rfl rfl
  obtain ⟨t,rt,pt,ht⟩ := OpeningHeaderWrite.run o (to396 x q) (x.cursor+184) (OpeningSaltLow.room _ room) f pf hf
    rfl rfl off ptr
  exact ⟨t,q,CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose
    (CommitExact.compose ra rb) rd) re) rf) rt,pt,ht,st⟩

theorem memory (x : Context) (q : Model) (room : (x.cursor+184)/64<capacity)
    (st : OpeningHeaderLow.Staged (s345 x) q (x.cursor+120)) :
    (to416 x q).mem=put (put (s345 x).mem (x.cursor+120) 64 (W (partialHeader x 10)))
      (x.cursor+184) 38 (OpeningHeaderWrite.clip (W (partialHeader x 10/2^64))) := by
  obtain ⟨off,_,val⟩ := OpeningHeaderWrite.prepared (s389 x q) x.cursor
    (by unfold capacity at room;omega) rfl rfl
  have h := OpeningHeaderWrite.memory (to396 x q) (x.cursor+184) rfl off
  rw [show (to396 x q).mem=(s389 x q).mem from rfl,low_memory x q st] at h
  have val' : (to396 x q).reg .x14=OpeningHeaderWrite.clip (v387 x) := val
  rw [val',high19] at h
  exact h

end CommitGolfCandidate.Reconstruction.OpeningHeader
