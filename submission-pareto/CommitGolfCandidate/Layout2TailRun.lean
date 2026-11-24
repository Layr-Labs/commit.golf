import CommitGolfCandidate.Layout2Tail
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1500000

def tailSteps (r : Nat) := if r=0 then 2 else 1+dispatchCost r+(5+106*(534*r))

theorem finish_tail {I τ} (program : Program I) (wf : WellFormed τ) (s m : MachineState) (k len : Nat)
    (args : Input s k len) (tables : TablesAt τ s) (cur : FullCursor τ k s m (k/4)) :
    ∃ t, Runs I m t (tailSteps (k%4)) (tailSteps (k%4)) ∧ t.pc=pc 739 ∧
      Records s t proofBase (534*k) (resultByte τ s k) ∧ Kept temps s t := by
  let r:=k%4
  have small : r≤3 := by dsimp [r];omega
  have rem : m.getReg .x9=addr r := by rw [cur.rem]; congr 1 <;> dsimp [r] <;> omega
  have choose:=move program .choose m cur.next trivial
  let a:=after .choose m
  have jumps : BitVec.ult (addr r) (4#64)=true := by
    simp [BitVec.ult,addr,Nat.mod_eq_of_lt (show r<2^64 by omega),show r<4 by omega] <;> omega
  have pcA : a.pc=pc 721 := by
    rw [choose.pos];simp only [pcOut,rem,cur.four]
    change (if BitVec.ult (addr r) (4#64)=true then pc 721 else pc 714)=pc 721
    rw [jumps];rfl
  have remA : a.getReg .x9=addr r := (choose.kept _ (by decide)).trans rem
  have fixedA:=cur.kept.trans (choose.kept.weaken (move_temps _))
  have ptrA : a.getReg .x8=addr (proofBase+2136*(k/4)) := (choose.kept _ (by decide)).trans cur.dst
  have eightA : a.getReg .x21=8 := (choose.kept _ (by decide)).trans cur.eight
  have wA:=cur.wrote.move (s':=s) rfl choose.mem
  by_cases e : r=0
  · have tail:=move program .tail a pcA trivial
    have eq : 2136*(k/4)=534*k := by dsimp [r] at e;omega
    have length : tailSteps (k%4)=2 := by change tailSteps r=2;simp [tailSteps,e]
    refine ⟨after .tail a,by rw [length];exact choose.run.thenDo tail.run,?_,?_,fixedA.trans (tail.kept.weaken (move_temps _))⟩
    · simpa [pcOut,remA,e,addr] using tail.pos
    · exact eq ▸ wA.move rfl tail.mem
  · obtain ⟨u,runU,entry⟩:=dispatch_tail program a r (by omega) small pcA remA ((fixedA _ (by decide)).trans args.stack)
    have good (q : Reg) (free : q∉tailScratch) := entry.kept q free
    have writeU := wA.move (s':=s) rfl entry.same
    have preserved:=fixedA.trans (entry.kept.weaken (b:=temps) (by intro q h;cases q <;> simp_all [tailScratch,temps]))
    obtain ⟨t,ran,land,out,keep⟩:=insert_block program wf s u k len args tables (k/4) r 739 (by omega)
      (by simp [blockSize,r]) (by omega) (by omega) writeU entry.pcAt
      ((good _ (by decide)).trans ptrA) entry.size entry.table ((preserved _ (by decide)).trans args.scratch)
      ((good _ (by decide)).trans eightA) (by rw [entry.link];decide)
    have eq : 2136*(k/4)+534*r=534*k := by dsimp [r];omega
    have prices : tailSteps (k%4)=1+dispatchCost r+(5+106*(534*r)) := by change tailSteps r=_;simp [tailSteps,e]
    refine ⟨t,by rw [prices];exact (choose.run.thenDo runU).thenDo ran,land,eq ▸ out,preserved.trans (keep.weaken call_temps)⟩

theorem merge_scratch {s t u p n f} (range : Records s t p n f) (clean : Writes t u scratchBase 2136 (fun _=>0))
    (below : scratchBase+2136≤p) (initial : ∀ j, j<2136 → byte s (scratchBase+j)=0) :
    Writes s u p n f := by
  intro q fit
  by_cases out : Outside q
  · rw [clean.outside q fit out];exact range q fit out
  · have inside : scratchBase≤q ∧ q<scratchBase+2136 := by unfold Outside at out;omega
    have old := initial (q-scratchBase) (by omega)
    rw [show scratchBase+(q-scratchBase)=q by omega] at old
    simp only [clean q fit,if_pos inside,if_neg (show ¬(p≤q ∧ q<p+n) by omega),old]

end CommitGolfCandidate.Layout2
