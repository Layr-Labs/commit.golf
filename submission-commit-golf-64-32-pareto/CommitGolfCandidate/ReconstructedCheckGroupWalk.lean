import CommitGolfCandidate.ReconstructedCheckGroupDigit
import CommitGolfCandidate.ReconstructedCheckGroupControl

namespace CommitGolfCandidate.Reconstruction.CheckGroupWalk
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix CheckGroupControl
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000

def Access (m : Memory) (base j : Nat) (xs : List Nat) :=
  ∀ i (hi : i<xs.length),CheckCapSlots.read m base (j+i)=BitVec.ofNat 32 xs[i]
def patch (m : Memory) : List Nat → Nat → Memory
  | [],_=>m
  | a::xs,v=>patch (fix m a (v%211)) xs (v/211)

theorem unaffected (m : Memory) (id dig i : Nat) (apart : i≠top id) : fix m id dig i=m i := by simp [fix,writeWord,apart]

theorem congruence (m n : Memory) (xs : List Nat) (v : Nat) (agree : LeafMemory.Agrees m n) :
    LeafMemory.Agrees (patch m xs v) (patch n xs v) := by
  induction xs generalizing m n v with
  | nil=>exact agree
  | cons a xs ih=>
    apply ih
    intro i bound
    by_cases fresh : i=top a
    · subst i;simp [fix,writeWord,agree _ bound]
    · rw [unaffected _ _ _ _ fresh,unaffected _ _ _ _ fresh,agree _ bound]

theorem tail (m n : Memory) (base j a v : Nat) (xs : List Nat) (access : Access m base j (a::xs))
    (eff : LeafMemory.Agrees n (fix m a (v%211))) (small : a<1024)
    (stack : 528384≤base/8) (room : base+4*(j+1+xs.length)≤MEMORY_BYTES) : Access n base (j+1) xs := by
  intro i hi
  let w:=CheckCapSlots.cell base (j+1+i)
  have bound : w<2^33 := by dsimp [w,CheckCapSlots.cell];unfold MEMORY_BYTES at room;omega
  have fresh : w≠top a:=by dsimp [w,CheckCapSlots.cell,top,cap];omega
  have v:=access (i+1) (by simpa using hi)
  simp only [List.getElem_cons_succ] at v
  rw [show j+(i+1)=j+1+i by omega] at v
  change extractWord32 (n w) _=_
  rw [eff w bound,unaffected _ _ _ _ fresh];exact v

theorem walk (o : Oracle) (xs : List Nat) (nonempty : xs≠[]) (s : MachineState) (base j k v : Nat)
    (pos : s.pc=addr 577) (ptr : s.getReg .x16=CheckCapSlots.address base j) (access : Access (memoryView s) base j xs)
    (align : base%8=0) (room : base+4*(j+xs.length)≤MEMORY_BYTES) (stack : 528384≤base/8)
    (small : ∀ id∈xs,id<1024) (value : s.getReg .x17=W v) (bound : v<2^31)
    (count : s.getReg .x15=W k) (stop : s.getReg .x14=W (k+xs.length)) (few : k+xs.length≤4)
    (heap : s.getReg .x23=W cap) (radix : s.getReg .x21=W 211) (magicReg : s.getReg .x26=W magic) :
    ∃ t, Segment o (15*xs.length+1) s t [] ∧
      t.pc=addr (if (CapDigits.extract xs.length v).2=0 then 593 else 672) ∧
      LeafMemory.Agrees (memoryView t) (patch (memoryView s) xs v) ∧ Kept CheckGroupDigit.changed s t := by
  induction xs generalizing s j k v with
  | nil=>contradiction
  | cons a xs ih=>
    have sm:=small a List.mem_cons_self
    have slot : CheckCapSlots.read (memoryView s) base j=BitVec.ofNat 32 a := by
      have z:=access 0 (by simp)
      change CheckCapSlots.read _ _ (j+0)=BitVec.ofNat 32 a at z
      exact z
    simp only [List.length_cons] at room stop few
    obtain ⟨u,step,atEnd,old,quot,incr,next,ram,regs⟩:=CheckGroupDigit.positive o s base j a v k pos ptr slot align
      (by omega) sm value bound count heap radix magicReg
    have test:=less o u 591 577 .x15 .x14 (k+1) (k+(xs.length+1)) 8136 (by decide) atEnd rfl (by decide)
      incr ((regs .x14 (by decide)).trans stop) (by omega) (by omega)
    have both := compose step test
    have pass : ∀ r∉CheckGroupDigit.changed,u.getReg r=s.getReg r:=regs
    cases xs with
    | nil=>
      simp only [List.length_nil,Nat.zero_add,lt_self_iff_false,ite_false] at both
      let p:=u.setPC (addr 592)
      have close:=endDigit o p v rfl old ((regs .x21 (by decide)).trans radix) bound
      refine ⟨p.setPC (addr (if v/211=0 then 593 else 672)),?_,rfl,ram,?_⟩
      · exact compose both close
      · exact pass
    | cons b bs=>
      have more : k+1<k+((b::bs).length+1):=by simp
      rw [ite_eq_left more] at both
      let p:=u.setPC (addr 577)
      have here : Access (memoryView p) base (j+1) (b::bs) :=
        tail (memoryView s) (memoryView u) base j a v _ access ram sm stack (by omega)
      have sg : p.getReg .x14=W ((k+1)+(b::bs).length) := by
        change u.getReg .x14=_
        rw [regs .x14 (by decide),stop];congr 1;omega
      obtain ⟨t,moreSteps,done,finalMem,stays⟩:=ih (by simp) p (j+1) (k+1) (v/211) rfl next here (by omega)
        (fun i h=>small i (List.mem_cons_of_mem _ h)) quot (by omega) incr sg (by omega)
        ((regs .x23 (by decide)).trans heap) ((regs .x21 (by decide)).trans radix) ((regs .x26 (by decide)).trans magicReg)
      refine ⟨t,?_,done,?_,fun r h=>(stays r h).trans (pass r h)⟩
      · convert compose both moreSteps using 1 <;> simp <;> omega
      · intro w hw;exact (finalMem w hw).trans (congruence (memoryView u) _ _ (v/211) ram w hw)

end CommitGolfCandidate.Reconstruction.CheckGroupWalk

