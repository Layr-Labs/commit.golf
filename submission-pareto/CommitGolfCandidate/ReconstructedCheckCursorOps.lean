import CommitGolfCandidate.ReconstructedCheckCursorValues
import CommitGolfCandidate.ReconstructedCheckLink

namespace CommitGolfCandidate.Reconstruction.CheckCursorOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckCursorValues CheckRecorded
set_option maxRecDepth 12000
set_option maxHeartbeats 1300000

def assign (m : State) : Arith→Reg×Term
  | .rr op r a b=>(r,CheckCursorValues.apply op (m.get a) (m.get b))
  | .addi r a i=>(r,CheckCursorValues.apply .add (m.get a) (.lit (signExtend12 i)))
  | .addiw r a i=>(r,CheckCursorValues.apply .add32 (m.get a) (.lit (signExtend12 i)))
  | .slli r a i=>(r,CheckCursorValues.apply .shl (m.get a) (.lit (i.zeroExtend 64)))
  | .srli r a i=>(r,CheckCursorValues.apply .shr (m.get a) (.lit (i.zeroExtend 64)))
  | .lui r i=>assignment m (.lui r i)

private theorem reg (m : State) (a : Arith) : (assign m a).1=(assignment m a).1 := by cases a <;> rfl

private theorem value (env : Env) (ctx : Context env) (m : State) (a : Arith) :
    (assign m a).2.val env=(assignment m a).2.val env := by
  cases a <;> simp only [assign,assignment,CheckCursorValues.sound env ctx,op_sound]

def step (tab : Tables) (m : State) (op : CheckLink.Op) : Option State :=
  match op with
  | .plain (.basic (.arith a))=>let out:=assign m a;some {m.set out.1 out.2 with pc:=m.pc+4}
  | .plain (.andi rd rs off)=>some {m.set rd (CheckCursorValues.apply .bitAnd (m.get rs) (.lit (signExtend12 off))) with pc:=m.pc+4}
  | .plain (.subPtr rd a b)=>match m.get a,m.get b with
    | .lit x,.lit y=>some {m.set rd (.lit (x-y)) with pc:=m.pc+4}
    | _,_=>CheckLink.step tab m op
  | _=>CheckLink.step tab m op

theorem sound (o : Oracle) (env : Env) (ctx : Context env) (tab : Tables) (layout : Layout env tab)
    (m n : State) (s : MachineState) (h : Matches env m s) (safe : Safe tab m.writes)
    (op : CheckLink.Op) (found : fetch image s=some op.instr) (next : step tab m op=some n) :
    ∃ t, Segment o 1 s t [] ∧ Matches env n t ∧ Safe tab n.writes := by
  unfold step at next
  split at next
  · rename_i a
    simp only [Option.some.injEq] at next;subst n
    have exactStep:=CheckOrdinary.assigned env m s h a
    dsimp only at exactStep
    rw [←value env ctx m a,←reg m a] at exactStep
    exact ⟨_,plain o _ _ _ found exactStep,set_value env m s h _ _ _,safe⟩
  · rename_i rd rs off
    simp only [Option.some.injEq] at next;subst n
    have run : ordinaryStep s (CheckLink.Op.plain (.andi rd rs off)).instr=some ((s.setReg rd
      ((CheckCursorValues.apply .bitAnd (m.get rs) (.lit (signExtend12 off))).val env)).setPC (m.pc+4)) := by
      rw [CheckCursorValues.sound env ctx,←h.regs,←h.pc];rfl
    exact ⟨_,plain o _ _ _ found run,set_value env m s h _ _ _,safe⟩
  · rename_i rd a b
    split at next
    · rename_i x y ax byWord
      simp only [Option.some.injEq] at next;subst n
      have run : ordinaryStep s (CheckLink.Op.plain (.subPtr rd a b)).instr=some ((s.setReg rd (x-y)).setPC (m.pc+4)) := by
        change some ((s.setReg rd (s.getReg a-s.getReg b)).setPC (s.pc+4))=_
        rw [h.regs a,h.regs b,ax,byWord,h.pc];rfl
      exact ⟨_,plain o _ _ _ found run,set_value env m s h _ (.lit _) _,safe⟩
    · exact CheckLink.sound o env tab layout m n s h safe _ found next
  · exact CheckLink.sound o env tab layout m n s h safe _ found next

def run (tab : Tables) (lookup : Word→Option CheckLink.Op) (target : Word) : Nat→State→Option CheckProgram.Hit
  | 0,_=>none
  | k+1,m=>if m.pc=target then some ⟨0,m⟩ else do
    let op←lookup m.pc
    let v←step tab m op
    let hit←run tab lookup target k v
    return {hit with ticks:=hit.ticks+1}

theorem run_sound (o : Oracle) (env : Env) (ctx : Context env) (tab : Tables) (layout : Layout env tab)
    (lookup : Word→Option CheckLink.Op) (dec : ∀ s : MachineState,∀ op,lookup s.pc=some op→fetch image s=some op.instr)
    (target : Word) (k : Nat) (m : State) (s : MachineState) (h : Matches env m s) (safe : Safe tab m.writes)
    (hit : CheckProgram.Hit) (receipt : run tab lookup target k m=some hit) :
    ∃ t, Segment o hit.ticks s t [] ∧ Matches env hit.state t ∧ Safe tab hit.state.writes ∧ t.pc=target := by
  induction k generalizing m s hit with
  | zero=>cases receipt
  | succ n ih=>
    by_cases atPC : m.pc=target
    · simp [run,atPC] at receipt;subst hit;exact ⟨s,empty _ _,h,safe,h.pc.trans atPC⟩
    cases found : lookup m.pc with
    | none=>simp [run,atPC,found] at receipt
    | some op=>
      cases next : step tab m op with
      | none=>simp [run,atPC,found,next] at receipt
      | some v=>
        cases rest : run tab lookup target n v with
        | none=>simp [run,atPC,found,next,rest] at receipt
        | some r=>
          simp [run,atPC,found,next,rest] at receipt;subst hit
          obtain ⟨u,one,hu,su⟩:=sound o env ctx tab layout m v s h safe op (dec s op (h.pc ▸ found)) next
          obtain ⟨t,tail,last,st,pos⟩:=ih v u hu su r rest
          exact ⟨t,by simpa [Nat.add_comm] using compose one tail,last,st,pos⟩

end CommitGolfCandidate.Reconstruction.CheckCursorOps
