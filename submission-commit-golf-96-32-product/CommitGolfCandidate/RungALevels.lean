import CommitGolfCandidate.RungACells
import CommitGolfCandidate.RungAHeadFacts
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (Agree)
open S4.Machine (W indexBase)
open Late (pcAt)
def levelSteps (g h : Nat) := headSteps h+sumN (cellSteps g h) (sizeAt h)
def levelCycles (g h : Nat) := headCycles h+sumN (cellCycles g h) (sizeAt h)
def levelCalls (g h : Nat) := sumN (cellCalls g h) (sizeAt h)

theorem phase (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (C : Cover) (k r i h : Nat)
    (bk:k≤16777216) (bi:i<16777216) (bh:h<4) (s : MachineState) (pc:s.pc=pcAt (headPC h))
    (ag : Agree (beforeHead k r i h) s) (mem : View o.compression td ps (frontier C (i/24) h 0) s) :
    let g:=i/24
    ∃ t,DetRun o image s (levelSteps g h) t (levelCycles g h) (levelCalls g h) ∧
      t.pc=pcAt (if h<3 then headPC (h+1) else 18161) ∧ Agree (stageRegs k r g h) t ∧ View o.compression td ps (frontier C g (h+1) 0) t := by
  intro g
  obtain ⟨ok,forms⟩:=headFacts k r i h bk bi bh
  obtain ⟨u,pre,entry,same,regs,_⟩:=arithRun o _ _ _ _ _ s pc ag ok (allHead ⟨h,bh⟩)
  obtain ⟨t,body,ip,ready,v⟩:=bankRun hash o td ps C k r g h (by dsimp [g];omega) bh u entry (Agree.weaken regs forms) (mem.ofMem same)
  exact ⟨t,by simpa only [Nat.zero_add,levelSteps,levelCycles,levelCalls] using pre.trans body,
    ip.trans (congrArg pcAt (lastCell ⟨h,bh⟩)),ready,v⟩

theorem sumEq (f g : Nat→Nat) (n : Nat) (eq : ∀ j<n,f j=g j) : sumN f n=sumN g n:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [sumN,sumN,ih (fun j hj=>eq j (by omega)),eq n (by omega)]

private theorem keptFull (g h n : Nat) (gg:g<699050) (bh:h<4) (bn:n<sizeAt h) :
    keepCell g h n=keepCell 0 h n := by
  interval_cases h <;> simp [keepCell,baseIndex,sizeAt,slots,depth,leaves,Late.levelCount,S4.width,S4.span,LENGTH,LOG_LENGTH] at * <;> omega

theorem groupPrices (g : Nat) (bg:g≤699050) :
    sumN (levelSteps g) 4=(if g=699050 then 229 else 252) ∧
    sumN (levelCycles g) 4=(if g=699050 then 448 else 548) ∧
    sumN (levelCalls g) 4=(if g=699050 then 27 else 38) := by
  by_cases last:g=699050
  · subst g;decide +kernel
  · have keep (h n : Nat) (bh:h<4) (bn:n<sizeAt h):=keptFull g h n (by omega) bh bn
    have s (h : Nat) (b:h<4) : levelSteps g h=levelSteps 0 h:=by
      unfold levelSteps;rw [sumEq _ (cellSteps 0 h) _ (fun n hn=>by simp only [cellSteps,keep h n b hn])]
    have c (h : Nat) (b:h<4) : levelCycles g h=levelCycles 0 h:=by
      unfold levelCycles;rw [sumEq _ (cellCycles 0 h) _ (fun n hn=>by simp only [cellCycles,keep h n b hn])]
    have q (h : Nat) (b:h<4) : levelCalls g h=levelCalls 0 h:=by
      apply sumEq;intro n hn;simp only [cellCalls,keep h n b hn]
    rw [sumEq _ _ _ s,sumEq _ _ _ c,sumEq _ _ _ q];simp only [if_neg last];decide +kernel

theorem groupBody (hash : HashLaw) (o : Oracle) (td : Late.Trapdoor) (ps : Positions) (xs : List Index)
    (r : Nat) (i : Index) (s : MachineState) (pc:s.pc=pcAt 17871)
    (ag : Agree (loaded ps.card r i.val) s) (v : View o.compression td ps (seen xs) s) :
    let g:=i.val/24
    ∃ t,DetRun o image s (if g=699050 then 229 else 252) t (if g=699050 then 448 else 548) (if g=699050 then 27 else 38) ∧
      t.pc=pcAt 18161 ∧ Agree (stageRegs ps.card r g 3) t ∧ View o.compression td ps (seen (xs++[i])) t := by
  intro g
  have bi:i.val<16777216:=i.isLt
  have bk:ps.card≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have ind (d : Nat) (le:d≤4) : ∃ t,DetRun o image s (sumN (levelSteps g) d) t (sumN (levelCycles g) d) (sumN (levelCalls g) d) ∧
      t.pc=pcAt (if d<4 then headPC d else 18161) ∧ Agree (beforeHead ps.card r i.val d) t ∧
      View o.compression td ps (frontier (seen xs) g d 0) t := by
    induction d with
    | zero=>exact ⟨s,DetRun.refl o image s,pc,ag,v.equiv (frontierZero _ _)⟩
    | succ d ih=>
      obtain ⟨u,pre,ip,regs,mem⟩:=ih (by omega)
      rw [if_pos (by omega : d<4)] at ip
      obtain ⟨t,last,next,ready,done⟩:=phase hash o td ps (seen xs) ps.card r i.val d bk bi (by omega) u ip regs mem
      refine ⟨t,pre.trans last,?_,?_,done⟩
      · simpa only [show (d<3)↔(d+1<4) by omega] using next
      · simpa [beforeHead] using ready
  obtain ⟨t,path,ip,regs,mem⟩:=ind 4 le_rfl
  obtain ⟨steps,cy,calls⟩:=groupPrices g (by dsimp [g];omega)
  rw [steps,cy,calls] at path
  exact ⟨t,path,ip,regs,mem.equiv (finishGroup xs i)⟩
end CommitGolfCandidate.RungA
