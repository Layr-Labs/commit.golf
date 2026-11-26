import CommitGolfCandidate.S5MainGeometry
import CommitGolfCandidate.S5NodeFrame
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def moveState (d : Height) (j : Nat) (s : MachineState) := ((mainMoves d j).map Move.op).foldl execInstrBr s
def mainResult (o : Oracle) (d : Height) (b j : Nat) (s : MachineState) :=
  moveState d j (plainResult o.compression d (b+j) s (fromDisp j) (toDisp j))

private theorem moved_keeps (d : Height) (j : Nat) (s : MachineState) (r : Reg) (x : Reg.x21≠r) (y : Reg.x22≠r) :
    (moveState d j s).getReg r=s.getReg r := by
  rw [moveState,reg_effect];unfold mainMoves
  split_ifs <;> simp [Move.reg,applyDeltas,x,y]

private theorem moved_src (d : Height) (j : Nat) (s : MachineState) (stride : s.getReg .x25=4032) :
    (moveState d j s).getReg .x21 = s.getReg .x21+BitVec.ofNat 64 (if tileSize d=252 ∧ j%42=41 then 4032 else 0) := by
  rw [moveState,reg_effect];unfold mainMoves
  split_ifs <;> simp [Move.reg,applyDeltas,Move.delta,stride]

private theorem moved_dst (d : Height) (j : Nat) (s : MachineState) (stride : s.getReg .x26=4032) :
    (moveState d j s).getReg .x22 = s.getReg .x22+BitVec.ofNat 64 (if tileSize d=252 ∧ j%84=83 then 4032 else 0) := by
  rw [moveState,reg_effect];unfold mainMoves
  split_ifs <;> simp [Move.reg,applyDeltas,Move.delta,stride]

private theorem bumped (a n : Nat) :
    (BitVec.ofNat 64 a+2048)+BitVec.ofNat 64 n=BitVec.ofNat 64 (a+n)+2048 := by
  have reorder (u v w : Word) : (u+v)+w=(u+w)+v := by rw [BitVec.add_assoc,BitVec.add_comm v w,←BitVec.add_assoc]
  rw [reorder,←BitVec.ofNat_add]

theorem main_step (o : Oracle) {d b j k s} (frame : MainFrame d b j k s) (simple : ¬chained d)
    (inside : j<tileSize d) (even : b%2=0) (pfit : b+j<count d) (pads : gaps s) :
    let u:=mainResult o d b j s
    Runs .commit true o s u (bodyCost d j) (bodyCost d j+7) 1 ∧ MainFrame d b (j+1) k u ∧
    NodeEffect o.compression d (b+j) s u := by
  let t:=plainResult o.compression d (b+j) s (fromDisp j) (toDisp j)
  let u:=moveState d j t
  have tt : MainSites d j := main_table d simple ⟨j,by rcases main_shape d simple (by omega) with e|e <;>omega⟩ inside
  obtain ⟨range,src,dst,call,clear,maskN⟩:=tt
  have addr:=main_addresses frame simple inside even
  have pc:=frame.pc.trans (congrArg pcAt (body_site d j simple inside))
  have first : Runs .commit true o s t (laneWords d) (laneWords d+7) 1 :=
    plain_observed o addr frame.toCommon pfit simple (mainLane d j) pc
      (decoded_site (by omega) src) (decoded_site (by omega) dst) (decoded_site (by omega) call) (fun cut=>decoded_site range (clear cut)) (main_limit d j inside) maskN
  have pcT : t.pc=pcAt (movePC d j) := by
    rw [show t.pc=_ from plain_pc o.compression d (b+j) s (fromDisp j) (toDisp j) simple]
    rw [frame.pc];unfold pcAt movePC;rw [←BitVec.ofNat_add];congr 1 <;> omega
  have keep (r : Reg) (x : Reg.x10≠r) (y : Reg.x12≠r) (c : Reg.x31≠r) : t.getReg r=s.getReg r:=plain_keeps _ _ _ _ _ _ r x y c
  have same (r : Reg) (x : Reg.x10≠r) (y : Reg.x12≠r) (a : Reg.x21≠r) (b : Reg.x22≠r) (c : Reg.x31≠r) :
      u.getReg r=s.getReg r := (moved_keeps d j t r a b).trans (keep r x y c)
  have newCommon : Common u := by
    obtain ⟨m,l,kind,base,root,scratch,s1,s2,s3⟩:=frame.toCommon
    constructor <;> apply (same _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans <;> assumption
  let len := (mainMoves d j).length
  have next : Runs .commit true o t u len len 0 := by
    apply runs_pure;intro fuel
    let ix : Fin 252:=⟨j,by rcases main_shape d simple (by omega) with e|e <;>omega⟩
    have res:=run_moves d ix simple inside t pcT fuel
    change execute commitImage (fuel+((mainMoves d j).map Move.op).length) t true=
      (do let r←execute commitImage fuel u true;return r.charge ((mainMoves d j).map Move.op).length 0) at res
    rw [List.length_map] at res;exact res
  have inc:=geom_step d b j simple inside
  have up:=frame_effect (mainMoves d j) t
  have effect:=plain_effect o.compression addr pads pfit simple frame.selectMask
  refine ⟨?_,⟨newCommon,fun w=>(same .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (frame.selectMask w),?_,?_,?_,(same _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans frame.counter⟩,?_⟩
  · have joined:=runs_comp first next
    change Runs .commit true o s u (laneWords d+len) (laneWords d+len+7) 1
    rw [show laneWords d+len+7=(laneWords d+7)+len by omega];exact joined
  · change u.pc=_
    rw [show u.pc=t.pc+BitVec.ofNat 64 (4*len) from up.1,pcT,←body_advance d j simple inside]
    unfold pcAt movePC bodyCost;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);dsimp [len];omega
  · change u.getReg .x21=_
    rw [moved_src d j t ((keep _ (by decide) (by decide) (by decide)).trans frame.stride₁),keep _ (by decide) (by decide) (by decide),frame.src,bumped,inc.2.2.1]
    apply congrArg (fun n=>BitVec.ofNat 64 n+2048)
    unfold srcAddr;rw [source_address,source_address];split_ifs <;> omega
  · change u.getReg .x22=_
    rw [moved_dst d j t ((keep _ (by decide) (by decide) (by decide)).trans frame.stride₂),keep _ (by decide) (by decide) (by decide),frame.dst,bumped,inc.2.2.2]
    apply congrArg (fun n=>BitVec.ofNat 64 n+2048)
    unfold dstAddr;simp only [binaryAddress];unfold Late.gapOffset;split_ifs <;> omega
  · constructor
    · exact (read_congr_mem u t _ 32 up.2).trans effect.value
    · intro a n fit apart extra;exact (read_congr_mem u t a n up.2).trans (effect.outside a n fit apart extra)
end CommitGolfCandidate.S5Machine
