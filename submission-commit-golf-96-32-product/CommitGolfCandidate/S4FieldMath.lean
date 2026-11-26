import CommitGolfCandidate.S4FieldExpr
import CommitGolfCandidate.S4Address
import CommitGolfCandidate.S4RawProof
namespace CommitGolfCandidate.S4.Open
open CommitGolf RiscvZkvm.Rv64
open Machine (W)
open Machine.Sym (Expr Bin mkOp eval_mkOp)

def atLevel (q : Nat) := if q=0 then 0 else if q=1 then 1 else q-1
def targetLane (i : Index) (q : Nat) := (childPos i.val (q-2)+(if q=2 then 2 else 1))%radix (q-2)
def targetAddr (i : Index) (q : Nat) := if q=0 then Late.sharedSaltAddr i else siblingAddress i (q-2) (if q=2 then 1 else 0)

structure FieldState (b : Bool) (l q : Nat) (i : Index) (s : MachineState) : Prop where
  divisor : s.getReg .x27=3
  index : q=0 → s.getMem (s.getReg (ixReg b)+W (8*l))=W i.val
  node : 0<q → s.getReg .x8=W (nodeIndex i.val (if q=2 then 1 else q-2))
  ternaryLane : q=2 → s.getReg .x7=W ((i.val%3+1)%3)
  ternaryRow : q=2 → s.getReg (rowReg b)=W (Late.rowAddress 0 (i.val/3))

set_option maxRecDepth 1800
private theorem inputSmall (i : Index) (h : Nat) : nodeIndex i.val h<2^64 :=
  lt_of_le_of_lt (Nat.div_le_self ..) (by have t:=i.isLt;change i.val<16777216 at t;omega)
private theorem indexBottom (i : Index) : nodeIndex i.val 0=i.val:=Nat.div_one _
private theorem indexTriple (i : Index) : nodeIndex i.val 1=i.val/3:=rfl

theorem indexValue (b : Bool) (l q : Nat) (i : Index) (s : MachineState) (f : FieldState b l q i s) :
    (fieldIndexExpr b l q).eval s=W (nodeIndex i.val (atLevel q)) := by
  by_cases zero : q=0
  · subst q;simpa only [fieldIndexExpr,atLevel,ite_true,plus,lit,Expr.eval,eval_mkOp,Bin.apply,indexBottom] using f.index rfl
  by_cases one : q=1
  · subst q
    change rv64_divu (s.getReg .x8) (s.getReg .x27)=W (nodeIndex i.val 1)
    rw [f.divisor,f.node (by decide)];change rv64_divu (W (nodeIndex i.val 0)) 3=W (nodeIndex i.val 1)
    rw [indexBottom,indexTriple];exact Machine.divThree _ (by have:=i.isLt;change i.val<16777216 at this;omega)
  by_cases two : q=2
  · subst q;exact f.node (by decide)
  · let h:=q-2
    have hh : 0<h:=by dsimp [h];omega
    have old : s.getReg .x8=W (nodeIndex i.val h):=by simpa only [if_neg two] using f.node (by omega)
    have level : atLevel q=h+1:=by simp only [atLevel,if_neg zero,if_neg one];dsimp only [h];omega
    have rad : radix h=2:=if_neg (by omega)
    simp only [fieldIndexExpr,if_neg zero,if_neg one,if_neg two,eval_mkOp,lit,Expr.eval,Bin.apply,old,
      level,nextIndex,rad]
    exact Machine.shr _ 1 (inputSmall i h)

theorem laneValue (b : Bool) (l q : Nat) (i : Index) (s : MachineState) (f : FieldState b l q i s) (pos : 0<q) :
    (laneExpr q).eval s=W (targetLane i q) := by
  by_cases one : q=1
  · subst q;change rv64_remu (rv64_remu (s.getReg .x8) (s.getReg .x27)+1) (s.getReg .x27)=_
    rw [f.divisor,f.node (by decide),show nodeIndex i.val (if 1=2 then 1 else 1-2)=i.val from indexBottom i,
      Machine.modThree _ (by have:=i.isLt;change i.val<16777216 at this;omega),Machine.oneMore,
      Machine.modThree _ (by omega)]
    change W _=W ((nodeIndex i.val 0%3+1)%3);rw [indexBottom]
  by_cases two : q=2
  · subst q;change rv64_remu (s.getReg .x7+1) (s.getReg .x27)=_
    rw [f.divisor,f.ternaryLane rfl,Machine.oneMore,Machine.modThree _ (by omega)]
    apply congrArg W;change ((i.val%3+1)%3+1)%3 = (nodeIndex i.val 0%3+2)%3
    rw [indexBottom];omega
  · let h:=q-2
    have hh : 0<h:=by dsimp [h];omega
    have rad : radix h=2:=if_neg (by omega)
    have old : s.getReg .x8=W (nodeIndex i.val h):=by simpa only [if_neg two] using f.node pos
    simp only [laneExpr,if_neg one,if_neg two,masked,lit,eval_mkOp,Expr.eval,Bin.apply,old]
    change ((W (nodeIndex i.val h) &&& (1 : Word)) ^^^ 1)=_;rw [Machine.flip]
    apply congrArg W
    change 1-nodeIndex i.val h%2=(nodeIndex i.val h%radix h+(if q=2 then 2 else 1))%radix h
    rw [rad,if_neg two];omega

theorem rowValue (b : Bool) (l q : Nat) (i : Index) (s : MachineState) (f : FieldState b l q i s) (pos : 0<q) :
    (rowExpr b l q).eval s=W (Late.rowAddress (q-2) (nodeIndex i.val ((q-2)+1))) := by
  by_cases two : q=2
  · subst q;exact f.ternaryRow rfl
  · have level : atLevel q=q-2+1:=by unfold atLevel;split_ifs <;> omega
    simp only [rowExpr,if_neg two,plus,scale96,lit,sh,eval_mkOp,Expr.eval,Bin.apply,indexValue b l q i s f,level]
    exact Machine.rowAddrCalc .. 

theorem addressValue (b : Bool) (l q : Nat) (i : Index) (s : MachineState) (f : FieldState b l q i s) :
    (fieldAddressExpr b l q).eval s=W (targetAddr i q) := by
  by_cases z : q=0
  · subst q
    have ind : (fieldIndexExpr b l 0).eval s=W i.val:=(indexValue b l 0 i s f).trans (congrArg W (indexBottom i))
    simp only [fieldAddressExpr,ite_true,plus,scale96,lit,sh,masked,eval_mkOp,Expr.eval,Bin.apply,ind,
      show (W 4).toNat=4 by decide,show (W 1).toNat=1 by decide]
    change W (Late.rowBase+72)+((W i.val >>> (1:Nat))*W 184)+((W i.val &&& 1) <<< (4:Nat)) = W (Late.sharedSaltAddr i)
    rw [Machine.shr _ _ (by have:=i.isLt;change i.val<16777216 at this;omega),Machine.parity,Machine.shifted,←BitVec.ofNat_mul,←BitVec.ofNat_add,←BitVec.ofNat_add]
    rfl
  · simp only [fieldAddressExpr,if_neg z,plus,sh,lit,eval_mkOp,Expr.eval,Bin.apply,rowValue b l q i s f (by omega),
      laneValue b l q i s f (by omega)]
    rw [show (W 5).toNat=5 by decide,Machine.shifted,←BitVec.ofNat_add]
    apply congrArg W
    simp only [targetAddr,if_neg z,siblingAddress,targetLane]
    by_cases t : q=2 <;> simp only [t,ite_true,ite_false,Nat.add_zero,show (2:Nat)^5=32 by decide,Nat.mul_comm _ 32] <;> rfl
end CommitGolfCandidate.S4.Open
