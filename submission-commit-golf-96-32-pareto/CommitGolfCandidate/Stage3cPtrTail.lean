import CommitGolfCandidate.Stage3cPtrLeafRun
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option Elab.async false
set_option maxHeartbeats 800000

private def mark (p : Prop) [Decidable p] := if p then 1 else 0
private theorem optional (o : Oracle) (p : Prop) [Decidable p] (s : MachineState) (word : Instr)
    (rd : Reg) (v : Word) (clk : instructionCycles (.base word)=1)
    (found : p → fetch commitImage s=some (.base word))
    (act : p → ordinaryStep s (.base word)=some ((s.setReg rd v).setPC (s.pc+4))) :
    Runs .commit true o s (advanceWhen p s rd v) (mark p) (mark p) 0 := by
  unfold mark advanceWhen;split
  next yes=>simpa only [clk] using runs_step (o:=o) (pg:=.commit) (coins:=true) (found yes) (act yes)
  next _=>exact runs_id .commit true o s 

private theorem tick (s : MachineState) (p : Prop) [Decidable p] (rd : Reg) (v : Word) (n : Nat) (ip:s.pc=pcAt n) :
    (advanceWhen p s rd v).pc=pcAt (n+mark p) := by
  unfold advanceWhen mark;split
  · exact (congrArg (·+4) ip).trans (pc_succ n)
  · exact ip

private theorem classified (k : Nat) :
    ((k+1)%16=0 → Site .commit (leafPC k+12) (.ADD .x21 .x21 .x25)) ∧
    ((k+1)%32=0 → Site .commit (leafPC k+13) (.ADD .x22 .x22 .x26) ∧
       Site .commit (leafPC k+14) (.ADDI .x23 .x23 1536)) ∧
    ((k+1)%128=0 → Site .commit (leafPC k+15) (.ADDI .x20 .x20 4095) ∧
       Site .commit (leafPC k+16) (.BEQ .x20 .x0 8) ∧ Site .commit (leafPC k+17) (.JAL .x0 2090936)) := by
  let j:Fin 128:=⟨k%128,Nat.mod_lt _ (by decide)⟩
  have ⟨one,two,three⟩:=tail_classified j
  have fetch (e : Nat) (small:e<6) : Site .commit (leafPC k+12+e) (tailAt j e):=by
    rw [leaf_pc_local];exact tail_site j e small
  constructor
  · intro hit;have step:=fetch 0 (by decide);rw [one (by dsimp [j];omega)] at step;exact step
  constructor
  · intro hit;obtain ⟨u,v⟩:=two (by dsimp [j];omega)
    exact ⟨u ▸ fetch 1 (by decide),v ▸ fetch 2 (by decide)⟩
  · intro hit;obtain ⟨u,v,w⟩:=three (by dsimp [j];omega)
    exact ⟨u ▸ fetch 3 (by decide),v ▸ fetch 4 (by decide),w ▸ fetch 5 (by decide)⟩

private def moves (k : Nat) := mark ((k+1)%16=0)+mark ((k+1)%32=0)+mark ((k+1)%32=0)+mark ((k+1)%128=0)
private theorem move_run (o : Oracle) (s : MachineState) (k : Nat) (ip:s.pc=pcAt (leafPC k+12)) :
    Runs .commit true o s (movedCount s k) (moves k) (moves k) 0 ∧
    (movedCount s k).pc=pcAt (leafPC k+12+moves k) := by
  obtain ⟨one,two,three⟩:=classified k
  let x:=mark ((k+1)%16=0);let y:=mark ((k+1)%32=0);let z:=mark ((k+1)%128=0)
  have bx (e:(k+1)%32=0) : x=1:=if_pos (by omega)
  have byz (e:(k+1)%128=0) : y=1:=if_pos (by omega)
  let a:=movedMsg s k;let b:=movedRow s k;let c:=movedNode s k
  have ar : Runs .commit true o s a x x 0:=optional o _ s (.ADD .x21 .x21 .x25) _ _ rfl (fun h=>one h s ip) (fun _=>rfl)
  have ap:a.pc=pcAt (leafPC k+12+x):=tick _ _ _ _ _ ip
  have keepA (r : Reg) (d:Reg.x21≠r) : a.getReg r=s.getReg r:=by
    rw [show a=movedMsg s k by rfl,movedMsg,advanceRead _ _ _ _ _ (by decide),if_neg (fun h=>d h.1)]
  have br : Runs .commit true o a b y y 0:=by
    apply optional o _ a (.ADD .x22 .x22 .x26) _ _ rfl
    · intro e;exact (two e).1 a (by simpa only [bx e] using ap)
    · intro e;change some ((a.setReg .x22 (_+_)).setPC _) = _
      rw [keepA .x22 (by decide),keepA .x26 (by decide)]
  have bp:b.pc=pcAt (leafPC k+12+x+y):=tick _ _ _ _ _ ap
  have keepB (r : Reg) (d:Reg.x22≠r) (d':Reg.x21≠r) : b.getReg r=s.getReg r:=by
    rw [show b=movedRow s k by rfl,movedRow,advanceRead _ _ _ _ _ (by decide),if_neg (fun h=>d h.1)];exact keepA _ d'
  have cr : Runs .commit true o b c y y 0:=by
    apply optional o _ b (.ADDI .x23 .x23 1536) _ _ rfl
    · intro e;exact (two e).2 b (by simpa only [bx e,show y=1 from if_pos e] using bp)
    · intro e;change some ((b.setReg .x23 (_+_)).setPC _) = _;rw [keepB .x23 (by decide) (by decide)]
  have cp:c.pc=pcAt (leafPC k+12+x+y+y):=tick _ _ _ _ _ bp
  have dr : Runs .commit true o c (movedCount s k) z z 0:=by
    apply optional o _ c (.ADDI .x20 .x20 4095) _ _ rfl
    · intro e;exact (three e).1 c (by simpa only [bx (by omega : (k+1)%32=0),byz e] using cp)
    · intro e
      have keep : c.getReg .x20=b.getReg .x20:=by
        rw [show c=movedNode s k by rfl,movedNode,advanceRead _ _ _ _ _ (by decide),if_neg (fun h=>(by decide : Reg.x23≠Reg.x20) h.1)] <;> rfl
      change some ((c.setReg .x20 (_+_)).setPC _) = _;rw [keep,keepB .x20 (by decide) (by decide)]
  exact ⟨runs_comp (runs_comp (runs_comp ar br) cr) dr, by
    have atD:=tick c ((k+1)%128=0) .x20 (s.getReg .x20+signExtend12 4095) _ cp
    exact atD.trans (congrArg pcAt (show leafPC k+12+x+y+y+z=leafPC k+12+moves k by unfold moves;dsimp only [x,y,z];omega))⟩

private theorem setSame (s : MachineState) : s.setPC s.pc=s:=by cases s;rfl

theorem tail_run (o : Oracle) (s : MachineState) (k : Nat) (hk:k<LENGTH) (ip:s.pc=pcAt (leafPC k+12)) (regs:LeafRegs s k) :
    Runs .commit true o s (leafTail s k) (tailCount k) (tailCount k) 0 := by
  obtain ⟨path,pc⟩:=move_run o s k ip
  let t:=movedCount s k
  have room:k<16777216:=hk
  by_cases wrap:(k+1)%128=0
  · have h16:(k+1)%16=0:=by omega
    have h32:(k+1)%32=0:=by omega
    have pm:moves k=4:=by simp [moves,mark,h16,h32,wrap]
    have lastPC:leafPC k=5660:=by unfold leafPC;rw [show k%128=127 by omega]
    have tp:t.pc=pcAt 5676:=by rw [lastPC,pm] at pc;exact pc
    have counter:t.getReg .x20=BitVec.ofNat 64 (tileCounter (k+1)):=by
      change (movedCount s k).getReg .x20=_
      rw [movedRead,if_pos ⟨rfl,wrap⟩,regs.counter];exact leafDecPublic _ hk wrap
    obtain ⟨_,be,jal⟩:=(classified k).2.2 wrap
    rw [lastPC] at be jal
    have taken:((t.getReg .x20)==t.getReg .x0)=decide (k+1=LENGTH):=by
      rw [counter];exact leafZeroTest k hk wrap
    let u:=execInstrBr t (.BEQ .x20 .x0 8)
    have control:Runs .commit true o t u 1 1 0:=runs_step (be t tp) rfl
    by_cases last:k+1=LENGTH
    · have target:u=t.setPC (pcAt 5678):=by
        dsimp only [u,execInstrBr];rw [taken,decide_eq_true last,if_pos rfl,tp];rfl
      have same:leafTail s k=u:=by rw [target,leafTail,if_neg (by omega : ¬k+1<LENGTH)]
      rw [pm] at path
      rw [same,tailCount,if_pos wrap,if_pos last];exact runs_comp path control
    · have target:u=t.setPC (pcAt 5677):=by
        dsimp only [u,execInstrBr];rw [taken,decide_eq_false last,if_neg (by decide : ¬false=true),tp];rfl
      have up:u.pc=pcAt 5677:=by rw [target];rfl
      have far:Runs .commit true o u (execInstrBr u (.JAL .x0 2090936)) 1 1 0:=runs_step (jal u up) rfl
      have endState:execInstrBr u (.JAL .x0 2090936)=leafTail s k:=by
        change u.setPC (u.pc+signExtend21 2090936)=_
        rw [up,show pcAt 5677+signExtend21 2090936=pcAt 4123 by decide,target,leafTail,if_pos (by omega : k+1<LENGTH),pc_wrap k wrap];rfl
      rw [endState] at far;rw [pm] at path
      rw [tailCount,if_pos wrap,if_neg last];exact runs_comp (runs_comp path control) far
  · have hnext:k+1<LENGTH:=by change k+1<16777216;omega
    have cost:moves k=tailCount k:=by
      unfold tailCount moves mark;by_cases a:(k+1)%32=0 <;> by_cases b:(k+1)%16=0 <;> simp [a,b,wrap] <;> omega
    rw [cost] at pc path
    have same:leafTail s k=t:=by
      unfold leafTail;rw [if_pos hnext,pc_linear _ hk wrap,←pc];exact setSame t
    rw [same];exact path

theorem fixed_iteration (o : Oracle) {s : MachineState} {k : Nat} (a : AtLeaf s k) (hk:k<LENGTH) :
    Runs .commit true o s (afterLeaf o.compression s k) (12+tailCount k) (40+tailCount k) 4 := by
  obtain ⟨regs,ip⟩:=hashed_leaf o.compression a hk
  exact runs_comp (fixed_leaf o a hk) (tail_run o _ k hk ip regs)
end CommitGolfCandidate.Chained.BinaryMachine
