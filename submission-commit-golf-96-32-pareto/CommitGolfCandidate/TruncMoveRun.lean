import CommitGolfCandidate.TruncWireState
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 200000

def Slice (im : Image) (i : Nat) (ops : List Instr) : Prop :=
  ∀ j (h : j<ops.length), (im.code[i+j]?).bind decodeInstruction=some (.base ops[j])

theorem leftSlice {im i xs ys} (s : Slice im i (xs++ys)) : Slice im i xs := by
  intro j h
  have hj : j<(xs++ys).length := by simp;omega
  exact (s j hj).trans (congrArg (fun op=>some (.base op : Instruction)) (List.getElem_append_left (as:=xs) (bs:=ys) h))
theorem rightSlice {im i xs ys} (s : Slice im i (xs++ys)) : Slice im (i+xs.length) ys := by
  intro j h
  have z:=s (xs.length+j) (by simp;omega)
  simpa only [Nat.add_assoc,List.getElem_append_right (by omega : xs.length≤xs.length+j),Nat.add_sub_cancel_left] using z

def legal (m : Move) := m.dest≤536 ∧ m.dest%2=0 ∧ ∀ a∈m.source,a≤536 ∧ a%2=0

theorem memoryAccess (start off : Nat) (b : start+538≤MEMORY_BYTES) (h : off≤536)
    (a : start%2=0) (e : off%2=0) : accessValid (BitVec.ofNat 64 start+signExtend12 (BitVec.ofNat 12 off)) 2=true := by
  rw [shortImm ⟨off,by omega⟩,← BitVec.ofNat_add]
  have bound : start+off<2^64 := by change start+538≤2^36 at b;omega
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨by omega,by omega⟩

theorem moveKeeps (m : Move) (s : MachineState) (r : Reg) (h : r≠.x6) :
    (after m s).getReg r=s.getReg r := by
  have keep (x : MachineState) (a : Word) (v : BitVec 16) : (x.setHalfword a v).getReg r=x.getReg r := by cases r <;> rfl
  rcases m with ⟨a,d⟩;cases a with
  | none =>
    change ((s.setHalfword _ _).setPC _).getReg r=_
    rw [MachineState.getReg_setPC,keep]
  | some i =>
    let x:=execInstrBr s (.LHU .x6 .x18 (BitVec.ofNat 12 i))
    change ((x.setHalfword _ _).setPC _).getReg r=_
    rw [MachineState.getReg_setPC,keep]
    change ((s.setReg .x6 _).setPC _).getReg r=_
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem movePC (m : Move) (s : MachineState) : (after m s).pc=s.pc+BitVec.ofNat 64 (4*(instructions m).length) := by
  rcases m with ⟨a,d⟩;cases a <;>
    simp [after,instructions,execInstrBr,MachineState.setPC,MachineState.setHalfword,MachineState.setMem,
      MachineState.setReg,BitVec.add_assoc]

theorem oneMove (im : Image) (i : Nat) (m : Move) (s : MachineState) (src dst : Nat)
    (bound : i+(instructions m).length≤2048) (pc : s.pc=loc i) (code : Slice im i (instructions m)) (ok : legal m)
    (sreg : s.getReg .x18=BitVec.ofNat 64 src) (dreg : s.getReg .x19=BitVec.ofNat 64 dst)
    (sb : src+538≤MEMORY_BYTES) (db : dst+538≤MEMORY_BYTES) (sa : src%2=0) (da : dst%2=0) :
    Runs im s (after m s) (instructions m).length (instructions m).length := by
  rcases m with ⟨a,d⟩
  have dstOk:=memoryAccess dst d db ok.1 da ok.2.1
  rw [←dreg] at dstOk
  cases a with
  | none =>
    let op:=Instr.SH .x19 .x0 (BitVec.ofNat 12 d)
    have step : ordinaryStep s (.base op)=some (execInstrBr s op) := by
      simp [ordinaryStep,op,memoryArgumentsValid,memAccess,dstOk]
    exact one i s _ op (by change i+1≤2048 at bound;omega) pc (code 0 (by change 0<1;decide)) step rfl
  | some a =>
    let load:=Instr.LHU .x6 .x18 (BitVec.ofNat 12 a)
    let save:=Instr.SH .x19 .x6 (BitVec.ofNat 12 d)
    let t:=execInstrBr s load
    have v:=ok.2.2 a (by simp)
    have srcOk:=memoryAccess src a sb v.1 sa v.2
    rw [←sreg] at srcOk
    have ls : ordinaryStep s (.base load)=some t := by simp [load,t,ordinaryStep,memoryArgumentsValid,memAccess,srcOk]
    have ds : ordinaryStep t (.base save)=some (execInstrBr t save) := by
      have ptr : t.getReg .x19=s.getReg .x19 := rfl
      simp [save,ordinaryStep,memoryArgumentsValid,memAccess,ptr,dstOk]
    have tp : t.pc=loc (i+1) := by change s.pc+4=_;rw [pc];unfold loc;exact ofNat64_add_eq _ 4 _ (by omega)
    change i+2≤2048 at bound
    exact chain (one i s t load (by omega) pc (code 0 (by change 0<2;decide)) ls rfl)
      (one (i+1) t _ save (by omega) tp (code 1 (by change 1<2;decide)) ds rfl)

def moveList (ms : List Move) (s : MachineState) := (ms.flatMap instructions).foldl execInstrBr s

theorem bodyRun (im : Image) (ms : List Move) (i : Nat) (s : MachineState) (src dst : Nat)
    (pc : s.pc=loc i) (space : i+(ms.flatMap instructions).length≤2048) (code : Slice im i (ms.flatMap instructions))
    (ok : ∀ m∈ms,legal m)
    (sreg : s.getReg .x18=BitVec.ofNat 64 src) (dreg : s.getReg .x19=BitVec.ofNat 64 dst)
    (sb : src+538≤MEMORY_BYTES) (db : dst+538≤MEMORY_BYTES) (sa : src%2=0) (da : dst%2=0) :
    Runs im s (moveList ms s) (ms.flatMap instructions).length (ms.flatMap instructions).length := by
  induction ms generalizing i s with
  | nil => exact runRefl im s
  | cons m rest ih =>
    let ops:=instructions m
    have sp : i+(ops.length+(rest.flatMap instructions).length)≤2048 := by simpa only [List.flatMap_cons,List.length_append] using space
    have c : Slice im i (ops++rest.flatMap instructions) := code
    let t:=after m s
    have first:=oneMove im i m s src dst (by dsimp [ops] at sp;omega) pc (leftSlice c)
      (ok m List.mem_cons_self) sreg dreg sb db sa da
    have ip : t.pc=loc (i+ops.length) := by
      rw [show t.pc=_ from movePC m s,pc];unfold loc;rw [←BitVec.ofNat_add];congr 1;dsimp [ops];omega
    have last:=ih (i+ops.length) t ip (by omega) (rightSlice c) (fun x hx=>ok x (List.mem_cons_of_mem _ hx))
      ((moveKeeps m s .x18 (by decide)).trans sreg) ((moveKeeps m s .x19 (by decide)).trans dreg)
    simpa only [List.flatMap_cons,List.length_append,moveList,List.foldl_append,t,after] using chain first last
end CommitGolfCandidate.Trunc.Wire
