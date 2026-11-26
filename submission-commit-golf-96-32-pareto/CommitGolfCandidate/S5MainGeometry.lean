import CommitGolfCandidate.S5Changes
import CommitGolfCandidate.S5PlainEffect
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

def groupSrc (d : Height) (b j : Nat) := if tileSize d=252 then b+42*(j/42) else b
def groupDst (d : Height) (b j : Nat) := if tileSize d=252 then b+84*(j/84) else b
def bodyPC (d : Height) (j : Nat) :=
  mainPC d+laneWords d*j+(if tileSize d=252 then j/42+j/84 else 0)
def mainMoves (d : Height) (j : Nat) : List Move :=
  (if tileSize d=252 ∧ j%42=41 then [.message] else [])++
  (if tileSize d=252 ∧ j%84=83 then [.row] else [])
def bodyCost (d : Height) (j : Nat) := laneWords d+(mainMoves d j).length

theorem main_shape (d : Height) (simple : ¬chained d) (used : 0<tileSize d) :
    tileSize d=252 ∨ tileSize d=42 :=
  (by decide +kernel : ∀ h : Height, ¬chained h → 0<tileSize h → tileSize h=252 ∨ tileSize h=42) d simple used

theorem geom_step (d : Height) (b j : Nat) (simple : ¬chained d) (inside : j<tileSize d) :
    groupSrc d b j+j%42=b+j ∧ groupDst d b j+j%84=b+j ∧
    groupSrc d b (j+1)=groupSrc d b j+(if tileSize d=252 ∧ j%42=41 then 42 else 0) ∧
    groupDst d b (j+1)=groupDst d b j+(if tileSize d=252 ∧ j%84=83 then 84 else 0) := by
  rcases main_shape d simple (by omega) with eqn|eqn <;> rw [eqn] at inside <;>
    simp only [groupSrc,groupDst,eqn,Nat.reduceEqDiff,↓reduceIte,true_and,false_and] <;>
    (try split_ifs) <;> omega

theorem body_site (d : Height) (j : Nat) (simple : ¬chained d) (inside : j<tileSize d) : bodyPC d j=mainLane d j := by
  rcases main_shape d simple (by omega) with eqn|eqn <;> rw [eqn] at inside <;> simp [bodyPC,mainLane,eqn] <;> omega

theorem body_advance (d : Height) (j : Nat) (simple : ¬chained d) (inside : j<tileSize d) :
    bodyPC d j+bodyCost d j=bodyPC d (j+1) := by
  rcases main_shape d simple (by omega) with e|e <;> unfold bodyPC bodyCost mainMoves <;>
    simp only [e,Nat.mul_succ,Nat.reduceEqDiff,↓reduceIte,true_and,false_and] <;> (try split_ifs) <;>
    simp only [List.cons_append,List.nil_append,List.length_cons,List.length_nil] <;> omega

def movePC (d : Height) (j : Nat) :=bodyPC d j+laneWords d
private theorem moveSites : ∀ d : Height, ¬chained d → ∀ j : Fin 252, j.val<tileSize d →
    ∀ i : Fin 2, i.val<(mainMoves d j.val).length →
      decoded (movePC d j.val+i.val)=some (.base ((((mainMoves d j.val).map Move.op)[i.val]?).getD .EBREAK)) := by decide +kernel

theorem run_moves (d : Height) (j : Fin 252) (simple : ¬chained d) (valid : j.val<tileSize d)
    (s : MachineState) (pc : s.pc=pcAt (movePC d j.val)) (fuel : Nat) :
    let ops:=(mainMoves d j.val).map Move.op
    execute commitImage (fuel+ops.length) s true=(do let r←execute commitImage fuel (ops.foldl execInstrBr s) true
                                                     return r.charge ops.length 0) := by
  apply execute_linear .commit true _ _ _ _ pc
  · intro op mem
    obtain ⟨c,_,rfl⟩:=List.mem_map.mp mem
    cases c <;> intro s <;> exact ⟨rfl,rfl,rfl⟩
  · intro i hi;rw [List.length_map] at hi
    have bound : (mainMoves d j.val).length≤2 := by unfold mainMoves;split_ifs <;> decide
    have ix : i<2:=by omega
    have pcSmall := (by decide +kernel : ∀ h : Height, ¬chained h → ∀ t : Fin 252, t.val<tileSize h → movePC h t.val+2<18492) d simple j valid
    apply decoded_site (by omega)
    have f:=moveSites d simple j valid ⟨i,ix⟩ hi
    simpa only [List.getElem?_eq_getElem (by rwa [List.length_map] : i<((mainMoves d j.val).map Move.op).length),Option.getD_some] using f

theorem main_limit (d : Height) (j : Nat) (bound : j<tileSize d) : mainLane d j+5<18492 := by
  have sz : tileSize d≤252 := (by decide +kernel : ∀ h : Height,tileSize h≤252) d
  exact (by decide +kernel : ∀ h : Height,∀ k : Fin 252,k.val<tileSize h→mainLane h k.val+5<18492) d ⟨j,by omega⟩ bound
structure MainFrame (d : Height) (b j counter : Nat) (s : MachineState) extends Common s where
  selectMask : wireWidth d=238 → s.getReg .x30=heldMask d
  pc : s.pc=pcAt (bodyPC d j)
  src : s.getReg .x21=BitVec.ofNat 64 (srcAddr d (groupSrc d b j))+2048
  dst : s.getReg .x22=BitVec.ofNat 64 (dstAddr d (groupDst d b j))+2048
  counter : s.getReg .x20=BitVec.ofNat 64 counter

theorem main_addresses {d b j k s} (frame : MainFrame d b j k s) (simple : ¬chained d) (inside : j<tileSize d) (even : b%2=0) :
    Addr s d (b+j) (fromDisp j) (toDisp j) := by
  have range : j<252 := by rcases main_shape d simple (by omega) with e|e <;> omega
  have inc:=geom_step d b j simple inside
  have baseEven : groupDst d b j%2=0 := by unfold groupDst;split <;> omega
  constructor
  · erw [frame.src,BitVec.add_assoc,show 2048#64+signExtend12 (fromDisp j)=_ from source_disp ⟨j,range⟩,←BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64)
    change srcAddr d (groupSrc d b j)+96*(j%42)=srcAddr d (b+j)
    rw [←inc.1];unfold srcAddr;rw [source_address,source_address];omega
  · erw [frame.dst,BitVec.add_assoc,show 2048#64+signExtend12 (toDisp j)=_ from target_disp ⟨j,range⟩,←BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64)
    change dstAddr d (groupDst d b j)+Late.gapOffset (j%84)=dstAddr d (b+j)
    rw [←inc.2.1];unfold dstAddr; simp only [binaryAddress];unfold Late.gapOffset;omega
end CommitGolfCandidate.S5Machine
