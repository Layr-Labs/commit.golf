import CommitGolfCandidate.S5MainFold
import CommitGolfCandidate.S5Gates
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 18000
set_option maxHeartbeats 800000
attribute [local irreducible] levelOffset

def tileEndOps (d : Height) : List Instr :=
  if tileSize d=252 then [.ADDI .x20 .x20 4095]
  else [.ADD .x21 .x21 .x25,.ADDI .x6 .x0 2016,.ADD .x22 .x22 .x6,.ADDI .x20 .x20 4095]
def tileGate (d : Height) :=gatePos (decide (tileSize d=252)) (mainExit d)
def tileUpdate (d : Height) (s : MachineState) := (tileEndOps d).foldl execInstrBr s
def tileLanded (d : Height) (more : Bool) (s : MachineState) := (tileUpdate d s).setPC (gatePC (mainPC d) (mainExit d) more)
def tileControl (d : Height) (more : Bool) := (tileEndOps d).length+gateWords (decide (tileSize d=252)) more

private theorem end_table : ∀ d : Height,¬chained d→0<tileSize d→
    (tileEndOps d).all setupOp=true ∧ bodyPC d (tileSize d)+(tileEndOps d).length=tileGate d ∧
    tileGate d<18492 ∧ ∀ (j : Fin (tileEndOps d).length),
      decoded (bodyPC d (tileSize d)+j.val)=some (.base ((tileEndOps d).get j)) := by decide +kernel

structure Boundary (d : Height) (b ctr : Nat) (s : MachineState) : Prop extends Common s where
  selectMask : wireWidth d=238 → s.getReg .x30=heldMask d
  pc : s.pc=pcAt (if 0<ctr then mainPC d else mainExit d)
  src : s.getReg .x21=BitVec.ofNat 64 (srcAddr d b)+2048
  dst : s.getReg .x22=BitVec.ofNat 64 (dstAddr d b)+2048
  counter : s.getReg .x20=BitVec.ofNat 64 ctr

theorem begin_tile {d b c s} (a : Boundary d b c s) (more : 0<c) : MainFrame d b 0 c s := by
  refine ⟨a.toCommon,a.selectMask,?_,?_,?_,a.counter⟩
  · simpa [more,bodyPC] using a.pc
  · simpa [groupSrc] using a.src
  · simpa [groupDst] using a.dst

private theorem update_keeps_ctrl (s : MachineState) (d : Height) (r : Reg)
    (r6 : Reg.x6≠r) (r21 : Reg.x21≠r) (r22 : Reg.x22≠r) (r20 : Reg.x20≠r) :
    (tileUpdate d s).getReg r=s.getReg r := by
  unfold tileUpdate tileEndOps;split <;>
    simp only [List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ r6,MachineState.getReg_setReg_ne _ _ _ _ r21,
      MachineState.getReg_setReg_ne _ _ _ _ r22,MachineState.getReg_setReg_ne _ _ _ _ r20]

private theorem counter_after (s : MachineState) (d : Height) : (tileUpdate d s).getReg .x20=s.getReg .x20-1 := by
  unfold tileUpdate tileEndOps;split <;> change s.getReg .x20+signExtend12 4095=_ <;> rw [BitVec.sub_eq_add_neg] <;> rfl

private theorem addresses_after {d b ctr s} (a : MainFrame d b (tileSize d) ctr s) (simple : ¬chained d) (used : 0<tileSize d) :
    (tileUpdate d s).getReg .x21=BitVec.ofNat 64 (srcAddr d (b+tileSize d))+2048 ∧
    (tileUpdate d s).getReg .x22=BitVec.ofNat 64 (dstAddr d (b+tileSize d))+2048 := by
  rcases main_shape d simple used with e|e
  · have x:=a.src;have y:=a.dst
    simp only [groupSrc,groupDst,e,ite_true] at x y
    unfold tileUpdate tileEndOps;rw [if_pos e,e]
    exact ⟨x,y⟩
  · have x:=a.src;have y:=a.dst
    simp [groupSrc,groupDst,e] at x y
    unfold tileUpdate tileEndOps;rw [if_neg (by omega),e]
    change s.getReg .x21+s.getReg .x25=_ ∧ s.getReg .x22+(0+signExtend12 2016)=_
    rw [x,y,a.stride₁]
    have bump (base n : Nat) : (BitVec.ofNat 64 base+2048)+BitVec.ofNat 64 n=BitVec.ofNat 64 (base+n)+2048 := by
      have reorder (u v w : Word) : (u+v)+w=(u+w)+v := by rw [BitVec.add_assoc,BitVec.add_comm v w,←BitVec.add_assoc]
      rw [reorder,←BitVec.ofNat_add]
    constructor
    · change (BitVec.ofNat 64 (srcAddr d b)+2048)+BitVec.ofNat 64 4032=_
      rw [bump];apply congrArg (fun k=>BitVec.ofNat 64 k+2048)
      unfold srcAddr rowAddress;omega
    · change (BitVec.ofNat 64 (dstAddr d b)+2048)+BitVec.ofNat 64 2016=_
      rw [bump];apply congrArg (fun k=>BitVec.ofNat 64 k+2048);unfold dstAddr;simp only [binaryAddress];unfold Late.gapOffset;omega

theorem tile_end (o : Oracle) {d b ctr s} (a : MainFrame d b (tileSize d) (ctr+1) s) (simple : ¬chained d) (used : 0<tileSize d) (bound : ctr+1<2^64) :
    let more:=decide (0<ctr)
    let u:=tileLanded d more s
    Boundary d (b+tileSize d) ctr u ∧ u.mem=s.mem ∧ Runs .commit true o s u (tileControl d more) (tileControl d more) 0 := by
  let u:=tileUpdate d s
  let more:=decide (0<ctr)
  obtain ⟨legal,sz,range,code⟩:=end_table d simple used
  have ok:=fun op mem=>List.all_eq_true.mp legal op mem
  obtain ⟨m,pc⟩:=header_properties (tileEndOps d) s ok
  have here : u.pc=pcAt (tileGate d) := by
    change ((tileEndOps d).foldl execInstrBr s).pc=_
    rw [pc,a.pc,←sz,pcAt,pcAt,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega
  have init : Runs .commit true o s u (tileEndOps d).length (tileEndOps d).length 0 := by
    apply runs_pure;intro fuel;apply execute_linear .commit true _ _ _ _ a.pc
    · exact fun op mem=>header_straight op (ok op mem)
    · intro i hi;exact decoded_site (by omega) (code ⟨i,hi⟩)
  have newc : u.getReg .x20=BitVec.ofNat 64 ctr := by
    rw [show u.getReg .x20=s.getReg .x20-1 from counter_after ..,a.counter,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have nz : (u.getReg .x20 != 0)=more := by
    rw [newc];by_cases e : ctr=0
    · subst ctr;rfl
    · have ne : BitVec.ofNat 64 ctr≠0 := by intro e';have v:=congrArg BitVec.toNat e';rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v;exact e v
      rw [show more=true from decide_eq_true (by omega : 0<ctr)];exact bne_iff_ne.mpr ne
  have term:=gate_run (decide (tileSize d=252)) more _ _ u o here (tiled_gate d simple used) nz
  have keep (r : Reg) (x : Reg.x6≠r) (y : Reg.x21≠r) (z : Reg.x22≠r) (w : Reg.x20≠r) :
      (tileLanded d more s).getReg r=s.getReg r := update_keeps_ctrl s d r x y z w
  have cm : Common (tileLanded d more s) := by
    obtain ⟨c1,c2,c3,c4,c5,c6,c7,c8,c9⟩:=a.toCommon
    constructor <;> apply (keep _ (by decide) (by decide) (by decide) (by decide)).trans <;> assumption
  have xy:=addresses_after a simple used
  exact ⟨⟨cm,fun w=>(keep .x30 (by decide) (by decide) (by decide) (by decide)).trans (a.selectMask w),by change gatePC _ _ more=_;simp [gatePC,more],xy.1,xy.2,newc⟩,m,runs_comp init term⟩
end CommitGolfCandidate.S5Machine
