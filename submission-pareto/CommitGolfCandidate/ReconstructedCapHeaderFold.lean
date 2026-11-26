import CommitGolfCandidate.ReconstructedCapHeaderDigit
import CommitGolfCandidate.ReconstructedCapSchedule

namespace CommitGolfCandidate.Reconstruction.CapHeaderFold
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
open HonestCapTables (scratch)
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

structure Data (m : Model) (d : Fin 10) (xs g : List Nat) (offset : Nat) (digit : Nat→Nat) : Prop where
  base : m.reg .x9=W scratch
  depth : m.reg .x10=W d.val
  heap : m.reg .x18=W (CapLoad.heap+24)
  radix : m.reg .x31=W 211
  slots : CapSlots.Contains m.mem xs
  contains : offset+g.length≤xs.length
  size : xs.length≤512
  group : ∀ i : Fin g.length, xs[offset+i.val]'(by have b := i.isLt;omega)=g[i.val]
  small : ∀ i∈g, i<1024
  encoded : ∀ i∈g, ((m.reg .x23 &&& m.mem (CapLoad.word d.val i 3)) >>> (32:Nat)).toNat=digit i

theorem transported (m t : Model) (d : Fin 10) (xs g : List Nat) (offset : Nat) (digit : Nat→Nat)
    (data : Data m d xs g offset digit) (same : t.mem=m.mem) (regs : ∀ r∈CapHeaderDigit.keep, t.reg r=m.reg r) :
    Data t d xs g offset digit := by
  refine ⟨(regs _ (by decide)).trans data.base,(regs _ (by decide)).trans data.depth,
    (regs _ (by decide)).trans data.heap,(regs _ (by decide)).trans data.radix,same ▸ data.slots,
    data.contains,data.size,data.group,data.small,?_⟩
  intro i found;rw [same,regs .x23 (by decide)];exact data.encoded i found

structure End (m t : Model) (digit : Nat→Nat) (g : List Nat) : Prop where
  value : t.reg .x16=W (Encoding.headerValue digit g)
  mem : t.mem=m.mem
  regs : ∀ r∈CapHeaderDigit.keep, t.reg r=m.reg r

theorem next (o : Oracle) (d : Fin 10) (xs g : List Nat) (start : Nat) (digit : Nat→Nat) (n : Nat)
    (small : g.length≤4) (inside : n+1≤g.length) (m : Model) (s : MachineState) (pc : s.pc=addr 1610) (fit : Fits s m)
    (data : Data m d xs g start digit) (atSlot : m.reg .x25=W (start+n))
    (rem : m.reg .x30=CapHeaderDigit.neg (n+1)) (acc : m.reg .x16=W (Encoding.headerValue digit (g.drop (n+1)))) :
    ∃ t out, CommitExact.Segment o OpeningStraight.image 16 s t ∧
      t.pc=(if n=0 then addr 1626 else addr 1610) ∧ Fits t out ∧
      out.reg .x16=W (Encoding.headerValue digit (g.drop n)) ∧ out.reg .x30=CapHeaderDigit.neg n ∧
      out.reg .x25=W (start+n)-1 ∧ out.mem=m.mem ∧ ∀ r∈CapHeaderDigit.keep, out.reg r=m.reg r := by
  have iOK : n < g.length := inside
  let i : Fin g.length := ⟨n,iOK⟩
  let id := g[i.val]
  have member : id∈g := List.getElem_mem (l:=g) i.isLt
  have xsBound := data.contains
  have maxSize := data.size
  have existsSlot : start+i.val < xs.length := by have bound := i.isLt;omega
  let ptr : Fin 512 := ⟨start+i.val,by omega⟩
  let counter : Fin 5 := ⟨i.val+1,by have bound := i.isLt;omega⟩
  obtain ⟨u,b,first,loc,fb,step⟩ := CapHeaderDigit.run o m s pc fit d id ptr xs existsSlot data.slots
    (data.group i) (data.small _ member) counter (by change 0 < i.val+1;omega) _ (digit id) atSlot data.base data.depth
    data.heap acc data.radix rem (data.encoded _ member)
  have test : CapHeaderDigit.neg i.val=0 ↔ i.val=0 :=
    (by decide : ∀ k : Fin 5, CapHeaderDigit.neg k.val=0 ↔ k.val=0) ⟨i.val,by have bound := i.isLt;omega⟩
  have count : b.reg .x30=CapHeaderDigit.neg i.val := by simpa only [counter,Nat.add_sub_cancel] using step.counter
  have branch := CapWordStep.bne o u 1625 1610 .x30 8132 loc (by decide) rfl rfl _ ((fb.registers _).trans count)
  simp only [test] at branch
  have val : b.reg .x16=W (Encoding.headerValue digit (g.drop i.val)) := by
    rw [CapSchedule.get digit g i.val i.isLt];exact step.value
  exact ⟨_,b,CommitExact.compose first branch,rfl,fb.pc _,val,count,step.previous,step.memory,step.frame⟩

theorem fold (o : Oracle) (d : Fin 10) (xs g : List Nat) (start : Nat) (digit : Nat→Nat) (n : Nat)
    (small : g.length≤4) (inside : n+1≤g.length) (m : Model) (s : MachineState) (pc : s.pc=addr 1610) (fit : Fits s m)
    (data : Data m d xs g start digit) (atSlot : m.reg .x25=W (start+n))
    (rem : m.reg .x30=CapHeaderDigit.neg (n+1)) (acc : m.reg .x16=W (Encoding.headerValue digit (g.drop (n+1)))) :
    ∃ t out, CommitExact.Segment o OpeningStraight.image (16*(n+1)) s t ∧ t.pc=addr 1626 ∧ Fits t out ∧ End m out digit g := by
  induction n generalizing m s with
  | zero =>
    obtain ⟨u,b,h,loc,fb,val,_,_,mem,regs⟩ := next o d xs g start digit 0 small inside m s pc fit data atSlot rem acc
    exact ⟨_,_,h,loc,fb,val,mem,regs⟩
  | succ n ih =>
    obtain ⟨u,b,first,loc,fb,val,count,previous,mem,regs⟩ := next o d xs g start digit (n+1) small inside m s pc fit data atSlot rem acc
    have smaller := transported _ _ _ _ _ _ _ data mem regs
    have earlier : b.reg .x25=W (start+n) := by
      rw [previous,show start+(n+1)=start+n+1 by omega,show W (start+n+1)=W (start+n)+W 1 from BitVec.ofNat_add ..]
      exact BitVec.add_sub_cancel _ _
    have pcU : u.pc=addr 1610 := by simpa only [Nat.succ_ne_zero,ite_false] using loc
    obtain ⟨v,t,tail,locV,ft,ok⟩ := ih (by omega) b u pcU fb smaller earlier count val
    refine ⟨v,t,?_,locV,ft,ok.value,ok.mem.trans mem,fun r h => (ok.regs r h).trans (regs r h)⟩
    have all := CommitExact.compose first tail
    simpa only [show 16+16*(n+1)=16*(n+1+1) by omega] using all

end CommitGolfCandidate.Reconstruction.CapHeaderFold
