import CommitGolfCandidate.ReconstructedCheckGroupWalk
import CommitGolfCandidate.ReconstructedCheckGroupRead

namespace CommitGolfCandidate.Reconstruction.CheckGroupPiece
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckGroupRadix CheckGroupControl CheckGroupWalk CheckStream
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 14000
set_option maxHeartbeats 1700000

def scratch := [Reg.x5,.x6,.x7,.x14,.x15,.x16,.x17,.x24,.x28]
def reader (proof c : Nat) : Reader := ⟨proof,c/64,0,0⟩
def value (stream c : Nat) := HonestStream.get stream c 31

theorem view_eq {s t : MachineState} (h : t.mem=s.mem) : memoryView t=memoryView s := by
  funext i;exact congrFun h _

theorem get_bound (stream c : Nat) : value stream c<2^31 := Nat.mod_lt _ (by decide)

theorem run (o : Oracle) (s : MachineState) (xs : List Nat) (stream c proof base n j : Nat)
    (nonempty : xs≠[]) (length : xs.length=min (n-j) 4) (pc : s.pc=addr 554)
    (total : s.getReg .x12=W n) (ordinal : s.getReg .x13=W j) (jle : j≤n) (small : n≤512)
    (cursor : s.getReg .x24=W c) (proofReg : s.getReg .x27=W proof) (stackReg : s.getReg .x29=W base)
    (placed : Placed (reader proof c)) (source : Source s (reader proof c) stream)
    (access : Access (memoryView s) base j xs) (align : base%8=0) (room : base+4*(j+xs.length)≤MEMORY_BYTES)
    (stack : 528384≤base/8) (ids : ∀ a∈xs,a<1024) (heap : s.getReg .x23=W cap)
    (radix : s.getReg .x21=W 211) (magicReg : s.getReg .x26=W magic) :
    ∃ ticks t,ticks≤24+15*xs.length ∧ Segment o ticks s t [] ∧
      t.pc=addr (if (CapDigits.extract xs.length (value stream c)).2=0 then 593 else 672) ∧
      t.getReg .x24=W (c+31) ∧ LeafMemory.Agrees (memoryView t) (patch (memoryView s) xs (value stream c)) ∧
      Kept scratch s t := by
  obtain ⟨a,u,ac,one,p1,limit,mu,ku⟩:=count o s n j pc total ordinal jle small
  let g:=reader proof c
  let r : Fin 64:=⟨c%64,by omega⟩
  have eq : 64*g.block+r.val=c:=Nat.div_add_mod c 64
  have src : Source u g stream:=fun i hi=>(congrFun mu _).trans (source i hi)
  obtain ⟨b,v,bc,two,p2,unmasked,mv,kv⟩:=CheckGroupRead.positive o u g r stream placed src p1
    (eq ▸ (ku .x24 (by decide)).trans cursor) ((ku .x27 (by decide)).trans proofReg)
  rw [eq] at unmasked
  have fixV (q : Reg) (hu : q∉[Reg.x14,.x15]) (hv : q∈CheckGroupRead.preserve) :
      v.getReg q=s.getReg q := (kv q hv).trans (ku q hu)
  obtain ⟨w,three,p3,z,ptr,newCursor,head,mw,kw⟩:=setup o v c j base (value stream c) p2
    ((fixV .x24 (by decide) (by decide)).trans cursor) ((fixV .x13 (by decide) (by decide)).trans ordinal)
    (by omega) ((fixV .x29 (by decide) (by decide)).trans stackReg) unmasked
  have ram : memoryView w=memoryView s :=
    (view_eq mw).trans ((view_eq (s:=u) (t:=v) (funext mv)).trans (view_eq mu))
  have fixW (q : Reg) (hu : q∉[Reg.x14,.x15]) (hv : q∈CheckGroupRead.preserve) (hw : q∉[Reg.x15,.x16,.x17,.x24]) :
      w.getReg q=s.getReg q := (kw q hw).trans (fixV q hu hv)
  have stop : w.getReg .x14=W (0+xs.length):=by rw [kw .x14 (by decide),kv .x14 (by decide),limit,length,Nat.zero_add]
  obtain ⟨t,four,endAt,final,kt⟩:=walk o xs nonempty w base j 0 (value stream c) p3 ptr (ram ▸ access) align room stack ids
    head (get_bound stream c) z stop (by omega) ((fixW .x23 (by decide) (by decide) (by decide)).trans heap)
    ((fixW .x21 (by decide) (by decide) (by decide)).trans radix) ((fixW .x26 (by decide) (by decide) (by decide)).trans magicReg)
  refine ⟨_,t,?_,compose (compose (compose one two) three) four,endAt,(kt .x24 (by decide)).trans newCursor,ram ▸ final,?_⟩
  · omega
  · intro q h
    have facts : q∉CheckGroupDigit.changed ∧ q∉[Reg.x14,.x15] ∧ q∈CheckGroupRead.preserve ∧ q∉[Reg.x15,.x16,.x17,.x24] := by
      cases q <;> first | decide | exact False.elim (h (by decide))
    exact (kt q facts.1).trans (fixW q facts.2.1 facts.2.2.1 facts.2.2.2)

end CommitGolfCandidate.Reconstruction.CheckGroupPiece

