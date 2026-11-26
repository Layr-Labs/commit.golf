import CommitGolfCandidate.ReconstructedCapHeaderStore

namespace CommitGolfCandidate.Reconstruction.CapHeaderFlush
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 16000

def cursorOp : Op := .reg .x7 (.addi .x7 31)
def lastOp : Op := .reg .x22 (.addi .x22 4)
def afterCursor (m : Model) := cursorOp.apply m
def afterGroup (m : Model) := (afterCursor m).set .x21 (CapWordStep.imm (m.reg .x21) 4)
def afterRest (m : Model) := (afterGroup m).set .x24 (CapWordStep.imm (m.reg .x24) 4092)
def finish (m : Model) := lastOp.apply (afterRest m)

def stored (m : Model) (c : Nat) := CapHeaderStore.ends (after m CapHeaderStore.beginOps) c

abbrev retained : List Reg := [.x2,.x5,.x8,.x9,.x10,.x11,.x13,.x17,.x18,.x19,.x20,.x23,.x26,.x28,.x29,.x31]

structure Result (m t : Model) (c : Nat) : Prop where
  memory : t.mem=put m.mem c 31 (m.reg .x16 &&& m.reg .x29)
  cursor : t.reg .x7=W (c+31)
  group : t.reg .x21=CapWordStep.imm (m.reg .x21) 4
  pending : t.reg .x24=CapWordStep.imm (m.reg .x24) 4092
  back : t.reg .x22=m.reg .x22+4
  regs : ∀ r∈retained, t.reg r=m.reg r

theorem endRun (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1598) (fit : Fits s m) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 4 s t ∧ t.pc=addr 1602 ∧ Fits t (finish m) := by
  obtain ⟨a,p,pa,fa⟩ := OpeningStraight.block o m [cursorOp] 1598 (by decide) ⟨rfl,True.intro⟩ (by trivial) s pc fit
  obtain ⟨b,q,pb,fb⟩ := CapWordStep.addiw o (afterCursor m) a fa 1599 pa (by decide) .x21 .x21 4 rfl
  obtain ⟨v,r,pv,fv⟩ := CapWordStep.addiw o (afterGroup m) b fb 1600 pb (by decide) .x24 .x24 4092 rfl
  obtain ⟨t,z,pt,ft⟩ := OpeningStraight.block o (afterRest m) [lastOp] 1601 (by decide) ⟨rfl,True.intro⟩ (by trivial) v pv fv
  exact ⟨t,CommitExact.compose (CommitExact.compose (CommitExact.compose p q) r) z,pt,ft⟩

theorem run (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1626) (fit : Fits s m)
    (c : Nat) (room : c/64<capacity) (cursor : m.reg .x7=W c) (baseReg : m.reg .x17=wordAddress base)
    (test : m.reg .x19=34) :
    ∃ n t out, n≤19 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1602 ∧ Fits t out ∧ Result m out c := by
  let a := after m CapHeaderStore.beginOps
  have limit : c<2^64 := by unfold capacity at room;omega
  obtain ⟨off,addrTop,val⟩ := CapHeaderStore.entry m c limit cursor baseReg
  obtain ⟨u,p,pu,fu⟩ := OpeningStraight.block o m CapHeaderStore.beginOps 1626 (by decide) ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
    (by simp [CapHeaderStore.beginOps,Checked,Op.Valid]) s pc fit
  obtain ⟨n,v,nBound,q,pv,fv⟩ := CapHeaderStore.actual o a u pu fu c (by unfold cell base;unfold capacity at room;omega) addrTop off test
  obtain ⟨t,z,pt,ft⟩ := endRun o (stored m c) v pv fv
  let e := stored m c
  have preserved (r : Reg) (a : r≠.x6) (b : r≠.x12) (d : r≠.x15) (f : r≠.x14) (g : r≠.x16) : e.reg r=m.reg r := by
    unfold e stored
    rw [CapHeaderStore.keep _ _ _ a b]
    apply CapLowCore.sameReg
    simp [CapHeaderStore.beginOps,CapLowCore.changes,beq_eq_false_iff_ne.mpr b.symm,beq_eq_false_iff_ne.mpr d.symm,
      beq_eq_false_iff_ne.mpr f.symm,beq_eq_false_iff_ne.mpr g.symm]
  refine ⟨5+n+4,_,_,by omega,CommitExact.compose (CommitExact.compose p q) z,pt,ft,?_,?_,?_,?_,?_,?_⟩
  · change (CapHeaderStore.ends a c).mem=_
    rw [CapHeaderStore.memory _ _ (show a.reg .x0=0 from (fit.registers _).symm.trans rfl) off,val];rfl
  · change e.reg .x7+signExtend12 31=_
    rw [preserved _ (by decide) (by decide) (by decide) (by decide) (by decide),cursor];exact (BitVec.ofNat_add ..).symm
  · exact congrArg (fun x => CapWordStep.imm x 4) (preserved _ (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact congrArg (fun x => CapWordStep.imm x 4092) (preserved _ (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact congrArg (·+4) (preserved _ (by decide) (by decide) (by decide) (by decide) (by decide))
  · intro r mem
    simp only [retained,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> apply preserved <;> decide

theorem serialized (m out : Model) (fs : List Wire.Field) (value : Nat) (reg : m.reg .x16=W value)
    (mask : m.reg .x29=CapPayload.mask 31) (post : Result m out (Wire.bits fs))
    (memory : Serialized m.mem (Wire.pack fs)) (room : Wire.bits fs/64<capacity) :
    Serialized out.mem (Wire.pack (fs++[⟨value,31⟩])) := by
  rw [post.memory]
  apply CapWriter.snoc _ fs ⟨value,31⟩ _ memory _ (by decide : 31≤64) room
  rw [reg,mask,CapPayload.masked _ _ (by decide),BitVec.toNat_ofNat,Nat.mod_mod_of_dvd _ (by decide : 2^31∣2^64)];rfl

end CommitGolfCandidate.Reconstruction.CapHeaderFlush
