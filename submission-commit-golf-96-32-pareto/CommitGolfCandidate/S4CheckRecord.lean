import CommitGolfCandidate.S4LastLeaf
import CommitGolfCandidate.S4RecordPath
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest Salt)
def proofStart (b : Bool) (r : Nat) := proofBase+recordBytes b*r
structure LeafResult (o : Oracle) (x : CheckInput) (b : Bool) (r : Nat) (s t : MachineState) : Prop where
  run : CheckRuns o s t 111 4
  next : t.pc=pcAt (firstNode b)
  idx : t.getReg .x20=W ((readView x).idx r).val
  proof : t.getReg .x18=W (siblingPtr b r 0)
  keep : ∀ reg,pathKeep reg → t.getReg reg=s.getReg reg
  frame : SameOutside s t 256 352
  data : readBuffer t 256 32=Late.leaf o.compression (((readView x).idx r).val.testBit 0) ((readView x).salt r) ((readView x).entry r)

theorem checkLeaf (o : Oracle) (x : CheckInput) (b : Bool) (r : Nat) (s : MachineState) (br : r<x.positions.card)
    (choice : b=decide (x.positions.card=BATCH)) (pc : s.pc=pcAt (rowStart b)) (env : Env x s) (regs : Cursor x s r) :
    ∃ t,LeafResult o x b r s t := by
  let i:=recordIndex x.positions r;let a:=valueBase+256*r;let p:=proofStart b r
  have bound : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at bound
  have room : rowStart b+140≤Code.check.count:=by cases b <;> decide
  have enough : p+24≤MEMORY_BYTES:=by
    dsimp only [p,proofStart,proofBase];unfold MEMORY_BYTES;cases b <;> change _≤2^36 <;> unfold recordBytes <;> simp <;> omega
  have loadedAt : s.getMem (s.getReg .x8+0)=W i.val:=by
    rw [regs.index];change s.getMem (W (indexBase+8*r)+0)=_
    have al : (indexBase+8*r)%8=0:=by unfold indexBase;omega
    rw [show W (indexBase+8*r)+(0 : Word)=W (indexBase+8*r) from BitVec.add_zero _,readIndexed al,
      env.data.read _ _ (by unfold indexBase;omega) (by unfold indexBase;omega),←readIndexed al]
    exact loaded_index x r br
  let u:=Sym.evaluated entryOps s
  have safe : ∀ e∈Sym.requirements Sym.original entryOps,accessValid (e.1.eval s) e.2=true:=by
    intro e he;change e∈[(_ ,8)] at he;rcases List.mem_singleton.mp he with rfl
    change accessValid (s.getReg .x8+0) 8=true
    rw [regs.index,show W (indexBase+8*r)+(0 : Word)=W (indexBase+8*r) from BitVec.add_zero _]
    exact Safe.valid ⟨by unfold indexBase MEMORY_BYTES;omega,by unfold indexBase;omega⟩
  have code:=leafSites b
  obtain ⟨indRun,ir,imem,ipc⟩:=calcGiven (rowStart b) .check entryOps s pc (by change rowStart b+1≤_;omega) code.idx
    (fun c h=>by change c∈[_] at h;rcases List.mem_singleton.mp h with rfl;decide) safe
  have iu : u.getReg .x20=W i.val:=(ir .x20).trans loadedAt
  have ik (v : Reg) (ne : v≠.x20) : u.getReg v=s.getReg v:=outsideCalc entryOps s u ir [.x20] rfl v (by simpa)
  have pr : u.getReg .x18=W p:=by rw [ik _ (by decide),regs.proof];rw [←choice];rfl
  have low : 32768≤p:=by dsimp [p,proofStart,proofBase];omega
  have load:=loadField u (rowStart b+1) p 416 24 (Or.inl rfl) code.salt (by change rowStart b+1+50≤_;omega) ipc pr rfl
    (by exact ⟨by decide,by decide⟩) enough (by omega)
  let v:=loaded u 416 24
  have fr : SameOutside s v 256 352:=bothScratch (unchangedBytes imem _ _) (protectedBytes load.outside (by decide) (by decide))
  have vr (reg : Reg) (a6 : reg≠.x6) (a14 : reg≠.x14) (a18 : reg≠.x18) (a20 : reg≠.x20) :
      v.getReg reg=s.getReg reg:=(load.keep _ a6 a14 a18).trans (ik _ a20)
  have sv : readBuffer v 416 24=(readView x).salt r:=by
    apply load.low.trans
    have hi : 32768≤p:=low
    have e:=(env.data.regs imem).read p 24 hi (enough.trans (by decide))
    apply e.trans;unfold readView proofAt initial
    apply congrArg (fun addr=>readBuffer (Late.submission.initialState .check x) addr 24)
    change proofBase+recordBytes b*r=proofBase+r*recordBytes (decide (x.positions.card=BATCH))
    rw [choice,Nat.mul_comm]
  have val : readBuffer v a 256=(readView x).entry r:=by
    apply ((env.data.scratch fr).read a 256 (by dsimp [a,valueBase];omega) (by dsimp [a,valueBase];omega)).trans
    exact loaded_value x r br
  obtain ⟨t,final,atEnd,digest⟩:=hashLeaf o v b i ((readView x).entry r) ((readView x).salt r) a load.pc
    ((load.keep _ (by decide) (by decide) (by decide)).trans iu) ((vr _ (by decide) (by decide) (by decide) (by decide)).trans regs.value)
    (by dsimp [a,valueBase];omega) (by dsimp [a,valueBase];omega) (by dsimp [a,valueBase,MEMORY_BYTES];omega) val sv
    ((vr _ (by decide) (by decide) (by decide) (by decide)).trans env.mode)
    ((vr _ (by decide) (by decide) (by decide) (by decide)).trans env.kind)
    ((vr _ (by decide) (by decide) (by decide) (by decide)).trans env.width)
  refine ⟨t,⟨((ofRuns o indRun).trans (ofRuns o load.run)).trans final.run,atEnd,
    (final.keep _ (by decide)).trans ((load.keep _ (by decide) (by decide) (by decide)).trans iu),
    (final.keep _ (by decide)).trans load.cursor,?_,bothScratch fr final.frame,digest⟩⟩
  intro reg kept
  have good : SmallRegs reg ∧ reg≠.x6 ∧ reg≠.x14 ∧ reg≠.x18 ∧ reg≠.x20:=by
    simp only [SmallRegs,pathKeep,List.mem_cons,List.not_mem_nil,or_false,not_or] at kept ⊢;tauto
  exact (final.keep reg good.1).trans (vr reg good.2.1 good.2.2.1 good.2.2.2.1 good.2.2.2.2)
end CommitGolfCandidate.S4.Machine
