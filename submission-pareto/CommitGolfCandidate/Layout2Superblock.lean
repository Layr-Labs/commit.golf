import CommitGolfCandidate.Layout2Apply
import CommitGolfCandidate.Layout2Clear
import CommitGolfCandidate.Layout2Effects
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySimpa false

structure Move (I : Image) (b : Block) (s : MachineState) : Prop where
  run : Runs I s (after b s) b.ops.length (price b.ops)
  regs : ∀ r, (after b s).getReg r=regOut s r b
  mem : (after b s).mem=(memOut s b).mem
  pos : (after b s).pc=pcOut s b
  kept : Kept (clobbers b) s (after b s)

theorem move {I} (program : Program I) (b : Block) (s : MachineState) (start : s.pc=pc b.start)
    (valid : accessible s b) : Move I b s := by
  obtain ⟨reg,mem,pos,ok⟩:=effects b s start
  exact ⟨runBlock program b s start (ok.mpr valid),reg,mem,pos,kept_of_regs reg⟩

theorem move_temps (b : Block) : ∀ q, q∈clobbers b → q∈temps := by
  cases b <;> intro q h <;> cases q <;> first | decide | exact (False.elim (by simpa [clobbers] using h))
theorem call_temps : ∀ q, q∈callScratch → q∈temps := by intro q h;cases q <;> simp_all [callScratch,temps]

structure Input (s : MachineState) (k len : Nat) : Prop where
  scratch : s.getReg .x10=addr scratchBase
  output : s.getReg .x15=addr proofBase
  stack : s.getReg .x2=addr tableBase
  card : s.getReg .x16=addr k
  length : s.getReg .x17=addr len
  count : k≤16777216
  capacity : len≤8959041024

def source (s : MachineState) (j : Nat) := byte s (proofBase+j)
def resultByte (τ : Tables) (s : MachineState) (k : Nat) := convertAt τ k (source s)

structure FullCursor (τ : Tables) (k : Nat) (s m : MachineState) (g : Nat) : Prop where
  next : m.pc=pc 713
  dst : m.getReg .x8=addr (proofBase+2136*g)
  rem : m.getReg .x9=addr (k-4*g)
  four : m.getReg .x20=4
  eight : m.getReg .x21=8
  wrote : Records s m proofBase (2136*g) (resultByte τ s k)
  kept : Kept temps s m

theorem insert_block {I τ} (program : Program I) (wf : WellFormed τ) (s m : MachineState) (k len : Nat)
    (args : Input s k len) (tables : TablesAt τ s) (g r target : Nat)
    (limit : g≤k/4) (mult : r=blockSize k g) (pos : 1≤r) (small : r≤4)
    (record : Records s m proofBase (2136*g) (resultByte τ s k))
    (start : m.pc=pc 759) (ptr : m.getReg .x8=addr (proofBase+2136*g))
    (size : m.getReg .x18=addr (534*r)) (tab : m.getReg .x19=addr (tableBase+tableOffset r))
    (scratch : m.getReg .x10=addr scratchBase) (eight : m.getReg .x21=8)
    (link : (m.getReg .x31 &&& ~~~1#64)=pc target) :
    ∃ t, Runs I m t (5+106*(534*r)) (5+106*(534*r)) ∧ t.pc=pc target ∧
      Records s t proofBase (2136*g+534*r) (resultByte τ s k) ∧ Kept callScratch m t := by
  let P:=proofBase+2136*g
  have bound:=args.count
  have cfg:=tableConfig τ wf r P pos small (by unfold P proofBase tableBase;omega) (by unfold P proofBase scratchBase;omega)
  have tableM:=record.table (tables r pos small) (by have:=cfg.tableAfter;omega)
    (by have:=cfg.separated;have:=cfg.tableAfter;omega) cfg.even cfg.room
  obtain ⟨t,ran,pcT,writes,kept⟩:=apply_table program cfg m target start ptr size tab scratch eight link tableM
  refine ⟨t,ran,pcT,record.append writes ?_,kept⟩
  intro j hj
  unfold resultByte
  rw [at_block τ k g r j (source s) hj limit mult]
  apply gather_congr wf pos small hj
  intro q hq
  have ram:=cfg.room;have afterP:=cfg.tableAfter;have sep:=cfg.separated
  have old:=record.outside (P+q) (by omega) (Or.inr (by omega)) (Or.inr (by dsimp [P];omega))
  simpa only [source,P,Nat.add_assoc] using old

private theorem minus_four (v : Nat) (pos : 4≤v) : addr v+signExtend12 4092=addr (v-4) := by
  have cast : addr v=addr (v-4)+4#64 := by
    change addr v=addr (v-4)+addr 4
    rw [addr_add]; congr 1 <;> omega
  calc
    addr v+signExtend12 4092=(addr (v-4)+4#64)+signExtend12 4092 := congrArg (fun q=>q+signExtend12 4092) cast
    _=addr (v-4) := by rw [BitVec.add_assoc,show (4#64)+signExtend12 4092=0#64 from rfl,BitVec.add_zero]

theorem full_loop {I τ} (program : Program I) (wf : WellFormed τ) (s m0 : MachineState) (k len : Nat)
    (args : Input s k len) (tables : TablesAt τ s) (init : FullCursor τ k s m0 0) :
    ∃ t, Runs I m0 t (226429*(k/4)) (226429*(k/4)) ∧ FullCursor τ k s t (k/4) := by
  apply loop (I:=I) (k/4) 226429 226429 (fun g t=>FullCursor τ k s t g) m0 init
  intro g more m h
  have select:=move program .choose m h.next trivial
  let a:=after .choose m
  have remLe:=args.count
  have enough : BitVec.ult (addr (k-4*g)) (4#64)=false := by
    simp [BitVec.ult,addr,Nat.mod_eq_of_lt (show k-4*g<2^64 by omega),show ¬k-4*g<4 by omega] <;> omega
  have selPC : a.pc=pc 714 := by
    rw [select.pos];simp only [pcOut,h.rem,h.four]
    change (if BitVec.ult (addr (k-4*g)) (4#64)=true then pc 721 else pc 714)=pc 714
    rw [enough];rfl
  have enter:=move program .full a selPC trivial
  have noChange (q : Reg) : a.getReg q=m.getReg q := select.regs q
  let u:=after .full a
  have ptr : u.getReg .x8=addr (proofBase+2136*g) := by rw [enter.regs];simpa [regOut,noChange] using h.dst
  have stack : a.getReg .x2=addr tableBase := (noChange _).trans ((h.kept _ (by decide)).trans args.stack)
  have eight : u.getReg .x21=8 := (enter.kept _ (by decide)).trans ((noChange _).trans h.eight)
  have scr : u.getReg .x10=addr scratchBase := (enter.kept _ (by decide)).trans ((noChange _).trans ((h.kept _ (by decide)).trans args.scratch))
  have st : u.pc=pc 759 := enter.pos
  have size : u.getReg .x18=addr (534*4) := by rw [enter.regs];rfl
  obtain ⟨t,runT,pcT,writes,kept⟩:=insert_block program wf s u k len args tables g 4 718 (by omega)
    (by simp [blockSize,more]) (by decide) (by decide) (h.wrote.move rfl (enter.mem.trans select.mem))
    st ptr size (by rw [enter.regs];simpa [regOut,tableOffset] using stack) scr eight
    (by rw [enter.regs];change (pc 718 &&& ~~~1#64)=pc 718;decide)
  have back:=move program .next t pcT trivial
  have keptA := (select.kept.weaken (move_temps _)).trans (enter.kept.weaken (move_temps _))
  have allKept:=((h.kept.trans keptA).trans (kept.weaken call_temps)).trans (back.kept.weaken (move_temps _))
  have tick : Runs I m (after .next t) 226429 226429 := ((select.run.thenDo enter.run).thenDo runT).thenDo back.run
  refine ⟨after .next t,tick,back.pos,?_,?_,?_,?_,?_,allKept⟩
  · rw [back.regs];simp only [regOut,reduceCtorEq,ite_false,ite_true, kept _ (by decide : Reg.x8∉callScratch),
      kept _ (by decide : Reg.x18∉callScratch),ptr,size,addr_add]
    apply congrArg (BitVec.ofNat 64);omega
  · have remaining : t.getReg .x9=addr (k-4*g) :=
      (kept _ (by decide)).trans ((enter.kept _ (by decide)).trans ((noChange _).trans h.rem))
    rw [back.regs];simp only [regOut,ite_true,remaining,minus_four (k-4*g) (by omega)]
    apply congrArg (BitVec.ofNat 64);omega
  · exact (back.kept _ (by decide)).trans ((kept _ (by decide)).trans ((enter.kept _ (by decide)).trans ((noChange _).trans h.four)))
  · exact (back.kept _ (by decide)).trans ((kept _ (by decide)).trans eight)
  · simpa only [show 2136*(g+1)=2136*g+534*4 by omega] using writes.move rfl back.mem

end CommitGolfCandidate.Layout2
