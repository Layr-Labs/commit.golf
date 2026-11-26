import CommitGolfCandidate.S4SlotState
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor pcAt)
open Machine (W Runs)
def slotSum : Nat→Nat | 0=>0 | n+1=>slotSum n+slotPrice n
structure SlotProgress (td : Trapdoor) (ps : Positions) (s : MachineState) (t l : Nat) extends SlotData td ps s (8*t+l) : Prop where
  pc : s.pc=pcAt (slotPC (decide (t=21)) l)
  count : s.getReg .x9=W (21-t)
  ptr : s.getReg .x24=W (512+16*t)
  kids : s.getReg .x22=W (Late.rowAddress 15 (8*t))
  cap : s.getReg .x23=W (Late.nodeAddress 16 (8*t))

theorem lanes (td : Trapdoor) (ps : Positions) (batch : ps.card=128) (t : Fin 22) (l : Nat)
    (allowed : l ≤ (if t.val=21 then 3 else 8)) (s : MachineState) (start : SlotTile td ps s t) :
    ∃ z,SlotProgress td ps z t l ∧ Runs .opening s z (slotSum l) (slotSum l) := by
  induction l with
  | zero=>exact ⟨s,⟨start.toSlotData,by simpa only [slotPC,decide_eq_true_eq] using start.pc,start.left,start.flagsPtr,start.children,start.parents⟩,
      Runs.refl .opening s⟩
  | succ l ih=>
    obtain ⟨u,cur,body⟩:=ih (by omega)
    have lim : l<8:=by split at allowed <;> omega
    have ok : (decide (t.val=21))=false ∨ l<3:=by by_cases v : t.val=21 <;> simp_all
    have inside : 8*t.val+l<171:=by have h:=t.isLt;split at allowed <;> omega
    let b:=decide (t.val=21)
    let j : Fin 8:=⟨l,lim⟩
    have w:=runSlot t j b ok ps batch u inside cur.pc cur.flags cur.ptr cur.kids cur.cap cur.dest
    refine ⟨slotEnd u l,⟨?_,w.pc,(w.keep .x9 (by decide)).trans cur.count,(w.keep .x24 (by decide)).trans cur.ptr,
      (w.keep .x22 (by decide)).trans cur.kids,(w.keep .x23 (by decide)).trans cur.cap⟩,body.trans w.run⟩
    exact afterSlot td ps batch u _ t j b inside cur.toSlotData w

def loopOps : List Machine.Sym.Calc := [.addi .x24 .x24 16,.addi .x22 .x22 768,.addi .x23 .x23 384,.addi .x9 .x9 4095]
private theorem loopCode : (Machine.Fragment.arithmetic loopOps).valid .opening 5171 5175:=by decide
def slotLatchSteps (t : Nat) := if t+1=21 then 5 else 6
private theorem nextAddrs : ∀ t : Fin 21,
    Late.rowAddress 15 (8*t.val)+768=Late.rowAddress 15 (8*(t.val+1)) ∧
    Late.nodeAddress 16 (8*t.val)+384=Late.nodeAddress 16 (8*(t.val+1)) := by decide

theorem slotLatch (td : Trapdoor) (ps : Positions) (t : Fin 21) (s : MachineState) (st : SlotProgress td ps s t 8) :
    ∃ v,SlotTile td ps v (t.val+1) ∧ Runs .opening s v (slotLatchSteps t) (slotLatchSteps t) := by
  have bt:=t.isLt
  have pc : s.pc=pcAt 5171:=by
    have eqv : decide (t.val=21)=false:=decide_eq_false (by omega)
    have h:=st.pc;rw [eqv] at h;exact h
  let u:=Machine.Sym.evaluated loopOps s
  obtain ⟨pre,regs,mem,atEnd⟩:=Machine.evalMath .opening loopOps 5171 5175 s pc loopCode
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : loopOps.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  have cnt : u.getReg .x9=W (21-(t.val+1)):=by
    apply (regs .x9).trans;change s.getReg .x9+18446744073709551615=_
    rw [st.count];exact (Machine.prev _ (by omega)).trans (congrArg W (by omega))
  have k := Machine.alternate .opening 5175 5177 4903 .x9 .x0 true (by decide) (by decide) rfl u atEnd
  have test : ((u.getReg .x9==u.getReg .x0)==true)=decide (t.val+1=21):=by
    rw [cnt];change ((W _==W 0)==true)=_;rw [Machine.eqNatural _ _ (by omega) (by decide)]
    by_cases e:t.val+1=21
    · rw [decide_eq_true e,decide_eq_true (by omega : 21-(t.val+1)=0)];rfl
    · rw [decide_eq_false e,decide_eq_false (by omega : ¬21-(t.val+1)=0)];rfl
  rw [test] at k
  let v:=u.setPC (pcAt (if t.val+1=21 then 5177 else 4903))
  have h : Runs .opening s v (slotLatchSteps t) (slotLatchSteps t):=by
    by_cases e:t.val+1=21
    · rw [decide_eq_true e] at k
      simp only [v,slotLatchSteps,if_pos e];exact pre.trans k
    · rw [decide_eq_false e] at k
      simp only [v,slotLatchSteps,if_neg e];exact pre.trans k
  have data : SlotData td ps v (8*(t.val+1)):=by
    rw [Nat.mul_succ];exact st.toSlotData.mem mem ((regs .x19).trans rfl)
  refine ⟨v,⟨data,rfl,cnt,?_,?_,?_⟩,h⟩
  · apply (regs .x24).trans;change s.getReg .x24+W 16=_;rw [st.ptr]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))
  · apply (regs .x22).trans;change s.getReg .x22+W 768=_;rw [st.kids]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (nextAddrs t).1)
  · apply (regs .x23).trans;change s.getReg .x23+W 384=_;rw [st.cap]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (nextAddrs t).2)

def fullTilePrice (t : Nat) := slotSum 8+slotLatchSteps t
theorem slotTiles (td : Trapdoor) (ps : Positions) (batch : ps.card=128) (s : MachineState) (start : SlotTile td ps s 0)
    (n : Nat) (limit : n≤21) :
    ∃ t,SlotTile td ps t n ∧ Runs .opening s t (rowTotal fullTilePrice n) (rowTotal fullTilePrice n) := by
  induction n with
  | zero=>exact ⟨s,start,Runs.refl .opening s⟩
  | succ n ih=>
    obtain ⟨z,frame,prev⟩:=ih (by omega)
    obtain ⟨u,done,body⟩:=lanes td ps batch ⟨n,by omega⟩ 8 (by rw [if_neg (show ¬(⟨n,by omega⟩ : Fin 22).val=21 by change n≠21;omega)]) z frame
    obtain ⟨v,fr,tail⟩:=slotLatch td ps ⟨n,by omega⟩ u done
    exact ⟨v,fr,prev.trans (body.trans tail)⟩
end CommitGolfCandidate.S4.Open
