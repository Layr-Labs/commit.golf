import CommitGolfCandidate.ReconstructedCheckCapWords

namespace CommitGolfCandidate.Reconstruction.CheckCapLowRead
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckStream
set_option maxRecDepth 24000
set_option maxHeartbeats 6000000

def saved : List Reg := [.x0,.x1,.x2,.x3,.x4,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]
def preserves (r w : Nat) :=
  let endState:=CheckCapRead.done r w
  decide (endState.ticks≤54) && saved.all (fun v=>decide (endState.state.get v=(CheckCapRead.start r w).get v))

private theorem kept224_0 : ∀ j : Fin 8,preserves (0+j.val) 224=true := by decide +kernel
private theorem kept224_1 : ∀ j : Fin 8,preserves (8+j.val) 224=true := by decide +kernel
private theorem kept224_2 : ∀ j : Fin 8,preserves (16+j.val) 224=true := by decide +kernel
private theorem kept224_3 : ∀ j : Fin 8,preserves (24+j.val) 224=true := by decide +kernel
private theorem kept224_4 : ∀ j : Fin 8,preserves (32+j.val) 224=true := by decide +kernel
private theorem kept224_5 : ∀ j : Fin 8,preserves (40+j.val) 224=true := by decide +kernel
private theorem kept224_6 : ∀ j : Fin 8,preserves (48+j.val) 224=true := by decide +kernel
private theorem kept224_7 : ∀ j : Fin 8,preserves (56+j.val) 224=true := by decide +kernel
private theorem kept224 (r : Fin 64) : preserves r.val 224=true := by
  let j : Fin 8:=⟨r.val%8,by omega⟩
  let k : Fin 8:=⟨r.val/8,by have hk:=r.isLt;omega⟩
  have split : r.val=8*k.val+j.val:=by change r.val=8*(r.val/8)+r.val%8;omega
  rw [split];generalize k=z;fin_cases z
  · exact kept224_0 j
  · exact kept224_1 j
  · exact kept224_2 j
  · exact kept224_3 j
  · exact kept224_4 j
  · exact kept224_5 j
  · exact kept224_6 j
  · exact kept224_7 j
private theorem kept240_0 : ∀ j : Fin 8,preserves (0+j.val) 240=true := by decide +kernel
private theorem kept240_1 : ∀ j : Fin 8,preserves (8+j.val) 240=true := by decide +kernel
private theorem kept240_2 : ∀ j : Fin 8,preserves (16+j.val) 240=true := by decide +kernel
private theorem kept240_3 : ∀ j : Fin 8,preserves (24+j.val) 240=true := by decide +kernel
private theorem kept240_4 : ∀ j : Fin 8,preserves (32+j.val) 240=true := by decide +kernel
private theorem kept240_5 : ∀ j : Fin 8,preserves (40+j.val) 240=true := by decide +kernel
private theorem kept240_6 : ∀ j : Fin 8,preserves (48+j.val) 240=true := by decide +kernel
private theorem kept240_7 : ∀ j : Fin 8,preserves (56+j.val) 240=true := by decide +kernel
private theorem kept240 (r : Fin 64) : preserves r.val 240=true := by
  let j : Fin 8:=⟨r.val%8,by omega⟩
  let k : Fin 8:=⟨r.val/8,by have hk:=r.isLt;omega⟩
  have split : r.val=8*k.val+j.val:=by change r.val=8*(r.val/8)+r.val%8;omega
  rw [split];generalize k=z;fin_cases z
  · exact kept240_0 j
  · exact kept240_1 j
  · exact kept240_2 j
  · exact kept240_3 j
  · exact kept240_4 j
  · exact kept240_5 j
  · exact kept240_6 j
  · exact kept240_7 j

theorem positive (o : Oracle) (s : MachineState) (g : Reader) (r : Fin 64) (stream w : Nat)
    (good : Placed g) (source : Source s g stream) (range : w=224 ∨ w=240)
    (pc : s.pc=CommitBlocks.addr 495) (cursor : s.getReg .x24=BitVec.ofNat 64 (64*g.block+r.val))
    (proof : s.getReg .x27=BitVec.ofNat 64 g.proofBase)
    (head : s.getReg .x13=BitVec.ofNat 64 (w-192)) (mask : s.getReg .x14=BitVec.ofNat 64 (2^(w-192)-1))
    (lim : s.getReg .x1=65) :
    let c:=64*g.block+r.val
    ∃ n≤54,∃ t,CheckRecorded.Segment o n s t [] ∧ t.pc=CommitBlocks.addr 484 ∧
      (t.getReg .x5).toNat=HonestStream.get stream c 64 ∧ (t.getReg .x7).toNat=HonestStream.get stream (c+64) 64 ∧
      (t.getReg .x28).toNat=HonestStream.get stream (c+128) 64 ∧
      (t.getReg .x29 &&& t.getReg .x14).toNat=HonestStream.get stream (c+192) (w-192) ∧
      (∀ p,t.getMem p=s.getMem p) ∧ (∀ v∈saved,t.getReg v=s.getReg v) := by
  have ok : preserves r.val w=true := by rcases range with h|h <;> subst w;exact kept224 r;exact kept240 r
  simp only [preserves,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  obtain ⟨t,sg,pos,a,b,c,lo,m,h⟩:=CheckCapWords.positive o s g r stream w good source range pc cursor proof head mask lim
  refine ⟨_,ok.1,t,sg,pos,a,b,c,lo,m,?_⟩
  intro q member
  rw [h.regs,ok.2 q member]
  cases q <;> try first | rfl | exact lim.symm | exact head.symm | exact mask.symm
  · change physical (env s g) (CheckParentRun.loc 1 r.val)=s.getReg .x24
    rw [point];exact cursor.symm
  · change physical (env s g) (CheckParentRun.loc 4 0)=s.getReg .x27
    rw [point];exact proof.symm

end CommitGolfCandidate.Reconstruction.CheckCapLowRead
