import CommitGolfCandidate.Stage3cBatchField
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def markHead : PathCode := [(328,.SLLI .x6 .x22 1),(329,.ADD .x6 .x21 .x6),(330,.LBU .x7 .x6 0),
  (331,.LBU .x28 .x6 1),(332,.OR .x29 .x7 .x28),(333,.BNE .x29 .x0 40)]
def flags (xs : List Index) (p : Nat) : Bool × Bool :=
  (xs.any fun i=>i.val/32768==2*p,xs.any fun i=>i.val/32768==2*p+1)
def flag (b : Bool) : Word:=if b then 1 else 0

set_option maxHeartbeats 650000
theorem mark_head (s : MachineState) (xs : List Index) (p : Nat) (bound : p<256) (m : Marked s xs)
    (pc : s.pc=pcAt 328) (base : s.getReg .x21=W 1024) (pos : s.getReg .x22=W p) :
    let t:=pathEnd s markHead
    Runs s t 6 6 ∧ t.pc=pcAt (if (flags xs p).1 || (flags xs p).2 then 343 else 334) ∧
      t.getReg .x7=flag (flags xs p).1 ∧ t.getReg .x28=flag (flags xs p).2 ∧ t.mem=s.mem ∧
      ∀ r,r∉([.x6,.x7,.x28,.x29] : List Reg)→t.getReg r=s.getReg r := by
  let z:=execInstrBr s (.SLLI .x6 .x22 1)
  let u:=execInstrBr z (.ADD .x6 .x21 .x6)
  let v:=execInstrBr u (.LBU .x7 .x6 0)
  let w:=execInstrBr v (.LBU .x28 .x6 1)
  let y:=execInstrBr w (.OR .x29 .x7 .x28)
  have zpc : z.pc=pcAt 329:=by change s.pc+4=_;rw [pc];rfl
  have upc : u.pc=pcAt 330:=by change z.pc+4=_;rw [zpc];rfl
  have vpc : v.pc=pcAt 331:=by change u.pc+4=_;rw [upc];rfl
  have wpc : w.pc=pcAt 332:=by change v.pc+4=_;rw [vpc];rfl
  have ypc : y.pc=pcAt 333:=by change w.pc+4=_;rw [wpc];rfl
  have addr : u.getReg .x6=W (1024+2*p) := by
    change s.getReg .x21+(s.getReg .x22 <<< 1)=_;rw [base,pos];unfold W
    rw [shifted,←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega
  have left : u.getReg .x6+signExtend12 0=W (1024+2*p) := by simpa only [show signExtend12 0=0#64 by rfl,BitVec.add_zero] using addr
  have right : v.getReg .x6+signExtend12 1=W (1024+(2*p+1)) :=
    (congrArg (·+signExtend12 1) addr).trans ((BitVec.ofNat_add (1024+2*p) 1).symm.trans (congrArg W (by omega)))
  have oka : memoryArgumentsValid u (.LBU .x7 .x6 0)=true := by
    change accessValid (_+_) 1=true;rw [left];apply access_ok <;> first | omega | (change _≤2^36;omega)
  have okb : memoryArgumentsValid v (.LBU .x28 .x6 1)=true := by
    change accessValid (_+_) 1=true;rw [right];apply access_ok <;> first | omega | (change _≤2^36;omega)
  have a : ordinaryStep u (.base (.LBU .x7 .x6 0))=some v := by simp only [ordinaryStep,oka,↓reduceIte];rfl
  have b : ordinaryStep v (.base (.LBU .x28 .x6 1))=some w := by simp only [ordinaryStep,okb,↓reduceIte];rfl
  have ready : pathReady s markHead:=⟨pc,rfl,rfl,zpc,rfl,rfl,upc,a,rfl,vpc,b,rfl,wpc,rfl,rfl,ypc,rfl,rfl,True.intro⟩
  have bits (j : Nat) (small : j<512) : (s.getByte (W (1024+j))).zeroExtend 64=flag (xs.any fun i=>i.val/32768==j) := by
    change (byteAt s (1024+j)).zeroExtend 64=_
    rw [m j small];unfold flag;split <;> rfl
  have l : y.getReg .x7=flag (flags xs p).1 := by change (s.getByte (u.getReg .x6+signExtend12 0)).zeroExtend 64=_;rw [left];exact bits _ (by omega)
  have r : y.getReg .x28=flag (flags xs p).2 := by change (s.getByte (v.getReg .x6+signExtend12 1)).zeroExtend 64=_;rw [right];exact bits _ (by omega)
  have both : (y.getReg .x29 != y.getReg .x0)=((flags xs p).1 || (flags xs p).2) := by
    change ((y.getReg .x7 ||| y.getReg .x28) != 0#64)=_;rw [l,r];cases (flags xs p).1 <;> cases (flags xs p).2 <;> decide
  have last : pathEnd s markHead=y.setPC (pcAt (if (flags xs p).1 || (flags xs p).2 then 343 else 334)) := by
    change (if y.getReg .x29 != y.getReg .x0 then y.setPC (y.pc+signExtend13 40) else y.setPC (y.pc+4))=_
    rw [both,ypc];split <;> rfl
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,?_,?_,?_⟩
  · rw [last];rfl
  · exact (congrArg (fun z : MachineState=>z.getReg .x7) last).trans (MachineState.getReg_setPC.trans l)
  · exact (congrArg (fun z : MachineState=>z.getReg .x28) last).trans (MachineState.getReg_setPC.trans r)
  · rw [last];rfl
  · intro q h
    apply (congrArg (fun z : MachineState=>z.getReg q) last).trans
    apply MachineState.getReg_setPC.trans
    cases q <;> first | rfl | (exfalso;apply h;decide)
end CommitGolfCandidate.Chained.BinaryMachine.Open
