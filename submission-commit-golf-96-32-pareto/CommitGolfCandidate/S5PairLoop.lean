import CommitGolfCandidate.S5Gates
import CommitGolfCandidate.S5StageLaw
import CommitGolfCandidate.S5LastRound
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000

def pairOps : List Instr := [.ADDI .x21 .x21 192,.ADDI .x22 .x22 96,.ADDI .x20 .x20 4095]
def pairUpdated (s : MachineState) :=pairOps.foldl execInstrBr s
def pairNext (d : Height) (b : Nat) (s : MachineState) :=
  (pairUpdated s).setPC (pcAt (if b+1<tiles d then mainPC d else mainExit d))

structure PairFrame (d : Height) (b : Nat) (s : MachineState) : Prop extends PairCtx d b s where
  pc : s.pc=pcAt (if b<tiles d then mainPC d else mainExit d)
  pad : ScratchPad s

theorem pair_end (o : Oracle) (d : Height) (b : Nat) (s : MachineState) (ctx : PairCtx d b s) (cut : chained d)
    (inside : b<tiles d) (pc : s.pc=pcAt (exitPairPC d)) (pad : ScratchPad s) :
    let t:=pairNext d b s
    PairFrame d (b+1) t ∧ t.mem=s.mem ∧ Runs .commit true o s t 4 4 0 := by
  obtain ⟨small,x21,x22,x20⟩:=pair_updates d cut
  let u:=pairUpdated s
  have first : Runs .commit true o s u 3 3 0 := by
    apply runs_pure;intro fuel
    apply execute_linear .commit true pairOps _ _ _ pc
    · intro op mem;exact header_straight op (List.all_eq_true.mp (by decide : pairOps.all setupOp) op mem)
    · intro i hi;change i<3 at hi;interval_cases i
      · rw [Nat.add_zero];exact decoded_site (by omega) x21
      · exact decoded_site (by omega) x22
      · exact decoded_site small x20
  have endEq:=(chain_shape d cut).2.2.2.2.2.2.2.1
  have ip : u.pc=pcAt (gatePos false (mainExit d)) := by
    change s.pc+4+4+4=_;rw [pc,BitVec.add_assoc,BitVec.add_assoc]
    change pcAt (exitPairPC d)+BitVec.ofNat 64 (4*3)=_
    rw [pc_delta];apply congrArg pcAt;unfold gatePos;simp only [Bool.false_eq_true,ite_false];omega
  have newc : u.getReg .x20=BitVec.ofNat 64 (tiles d-(b+1)) := by
    change s.getReg .x20+(-1)=_
    rw [ctx.ctr,←BitVec.sub_eq_add_neg]
    exact (BitVec.ofNat_sub_ofNat_of_le (w:=64) _ 1 (by decide) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have nz : (u.getReg .x20 != 0)=decide (b+1<tiles d) := by
    rw [newc];by_cases more:b+1<tiles d
    · rw [decide_eq_true more];apply bne_iff_ne.mpr;intro eq
      have bd : tiles d≤16777216 := (Nat.div_le_self ..).trans (level_count_le _)
      have v:=congrArg BitVec.toNat eq;rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v;change _=0 at v;omega
    · rw [show tiles d-(b+1)=0 by omega,decide_eq_false more];rfl
  have gate:=gate_run false _ _ _ u o ip (chain_gate d cut) nz
  have land : u.setPC (gatePC (mainPC d) (mainExit d) (decide (b+1<tiles d)))=pairNext d b s := by
    change u.setPC (pcAt (if decide (b+1<tiles d) then _ else _))=u.setPC (pcAt (if b+1<tiles d then _ else _));simp
  rw [land] at gate
  have keep (r : Reg) (a : Reg.x21≠r) (c : Reg.x22≠r) (e : Reg.x20≠r) :
      (pairNext d b s).getReg r=s.getReg r := by
    simp only [pairNext,pairUpdated,pairOps,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ a,MachineState.getReg_setReg_ne _ _ _ _ c,MachineState.getReg_setReg_ne _ _ _ _ e]
  have cm : Common (pairNext d b s) := by
    obtain ⟨q1,q2,q3,q4,q5,q6,q7,q8,q9⟩:=ctx.toCommon
    constructor <;> apply (keep _ (by decide) (by decide) (by decide)).trans <;> assumption
  refine ⟨⟨⟨cm,?_,?_,newc,(keep _ (by decide) (by decide) (by decide)).trans ctx.tag,
    (keep _ (by decide) (by decide) (by decide)).trans ctx.mask⟩,rfl,?_⟩,rfl,runs_comp first gate⟩
  · change s.getReg .x21+BitVec.ofNat 64 192=_;rw [ctx.src,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64)
    unfold srcAddr;rw [source_address,source_address];omega
  · change s.getReg .x22+BitVec.ofNat 64 96=_;rw [ctx.dst,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64)
    unfold dstAddr;rw [binaryAddress,binaryAddress];unfold Late.gapOffset;omega
  · exact ⟨(read_congr_mem _ s _ _ rfl).trans pad.second,(read_congr_mem _ s _ _ rfl).trans pad.last⟩

theorem pair_step (o : Oracle) {d b s base salt} (frame : PairFrame d b s) (cut : chained d) (valid : b<tiles d)
    (tree : TreeState o.compression base salt d.val s) (rows : doneRows o.compression base d.val (2*b) s) :
    ∃ t,PairFrame d (b+1) t ∧ TreeState o.compression base salt d.val t ∧ doneRows o.compression base d.val (2*(b+1)) t ∧
      Runs .commit true o s t (2*segmentWords d+4) (2*segmentWords d+4+7*(2*calls d)) (2*calls d) := by
  have nt:=(chain_shape d cut).2.2.2.2.2.2.1
  rw [nt] at valid
  have firstPC : s.pc=pcAt (segmentPC d 0):=frame.pc.trans (by rw [if_pos (by rwa [nt])];simp [segmentPC,show (0:Lane)=Lane.first by rfl,show (1:Lane)=Lane.second by rfl,Lane.val])
  obtain ⟨u,r₁,ctx₁,pc₁,pad₁,eff₁⟩:=chained_lane o d b 0 s cut frame.toPairCtx firstPC frame.pad tree.pads (by change 2*b+0<count d;omega)
  have tree₁:=node_frame tree eff₁ (by change 2*b+0<count d;omega)
  have rows₁:=grow_row tree rows eff₁ (by change 2*b+0<count d;omega)
  have secondPC : u.pc=pcAt (segmentPC d 1):=pc₁.trans (by simp [segmentPC,show (0:Lane)=Lane.first by rfl,show (1:Lane)=Lane.second by rfl,Lane.val])
  obtain ⟨v,r₂,ctx₂,pc₂,pad₂,eff₂⟩:=chained_lane o d b 1 u cut ctx₁ secondPC pad₁ tree₁.pads (by change 2*b+1<count d;omega)
  have tree₂:=node_frame tree₁ eff₂ (by change 2*b+1<count d;omega)
  have rows₂:=grow_row tree₁ rows₁ eff₂ (by change 2*b+1<count d;omega)
  have exitPC : v.pc=pcAt (exitPairPC d):=pc₂.trans (by simp [segmentPC,exitPairPC,show (1:Lane)=Lane.second by rfl,Lane.val];congr 1 <;> omega)
  obtain ⟨out,mem,r₃⟩:=pair_end o d b v ctx₂ cut (by rwa [nt]) exitPC pad₂
  refine ⟨_,out,transfer_tree tree₂ mem,?_,?_⟩
  · rw [show 2*(b+1)=2*b+1+1 by omega];exact transfer_rows rows₂ mem
  · have run:=runs_comp (runs_comp r₁ r₂) r₃;convert run using 1 <;> omega
end CommitGolfCandidate.S5Machine
