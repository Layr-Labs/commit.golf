import CommitGolfCandidate.ReconstructedCheckCapLowMemory
import CommitGolfCandidate.ReconstructedCheckCapLowSetup

namespace CommitGolfCandidate.Reconstruction.CheckCapLowLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapLowMemory
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W scratch)
open CheckCapLowItem (Context data keep)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def Access (m : Memory) (j : Nat) (xs : List Nat) :=
  ∀ i : Fin xs.length, CheckCapSlots.read m scratch (j+i.val)=BitVec.ofNat 32 xs[i.val]

private theorem tail_access {m n : Memory} (frame : Frame m n) (j id : Nat) (xs : List Nat)
    (valid : j+(id::xs).length≤512) (old : Access m j (id::xs)) : Access n (j+1) xs := by
  intro i
  have small:=i.isLt
  have tail:=old ⟨i.val+1,by simpa using i.isLt⟩
  change CheckCapSlots.read m scratch (j+(i.val+1))=BitVec.ofNat 32 xs[i.val] at tail
  rw [show j+1+i.val=j+(i.val+1) by omega]
  unfold CheckCapSlots.read
  rw [frame _ (by change 8589934171+(j+(i.val+1))/2<2^33;simp only [List.length_cons] at valid;omega)
    (Or.inr (by change 528384≤8589934171+(j+(i.val+1))/2;omega))]
  exact tail

theorem loop (o : Oracle) (xs : List Nat) (s : MachineState) (stream c w j total : Nat)
    (non : xs≠[]) (joint : j+xs.length=total) (small : total≤512) (room : c+w*xs.length≤70000000000)
    (range : w=224 ∨ w=240) (start : Context s proofBase c w j total)
    (ids : Access (memoryView s) j xs) (valid : ∀ id∈xs,id<1024) (tape : Proof (memoryView s) stream) :
    ∃ n≤65*xs.length,∃ t,Segment o n s t [] ∧ t.pc=addr 549 ∧ t.getReg .x24=W (c+w*xs.length) ∧
      LeafMemory.Agrees (memoryView t) (fill stream w xs c (memoryView s)) ∧
      (∀ q∈keep,t.getReg q=s.getReg q) := by
  induction xs generalizing s c j with
  | nil=>contradiction
  | cons id xs ih=>
    have cell:=valid id List.mem_cons_self
    have order:=ids ⟨0,by simp⟩
    have first : CheckCapSlots.read (memoryView s) scratch j=BitVec.ofNat 32 id := by simpa using order
    have count : j+(xs.length+1)=total:=joint
    have size : c+w+w*xs.length=c+w*(id::xs).length := by simp only [List.length_cons,Nat.mul_succ];omega
    obtain ⟨placed,reads⟩:=source s stream c (by omega) tape
    obtain ⟨n,steps,u,one,pc,cursor,ptr,memory,stable⟩:=CheckCapLowItem.run o s proofBase c w j total stream
      ⟨id,cell⟩ placed reads range start (by omega) small first
    let after:=data (memoryView s) id stream c w
    have model : LeafMemory.Agrees (memoryView u) after:=memory
    have frame : Frame (memoryView s) (memoryView u):=trans (CheckCapLowMemory.frame _ id stream c w cell) (frame_of_agrees memory)
    cases xs with
    | nil=>
      have endAt : j+1=total:=by simpa using count
      simp only [CheckCapLowItem.dest,ite_eq_left endAt] at pc
      exact ⟨n,by simpa using steps,u,one,pc,by simpa using cursor,model,stable⟩
    | cons id' rest=>
      let remain:=id'::rest
      have more : j+1≠total:=by simp only [List.length_cons] at count;omega
      have enter : u.pc=addr 495:=by simpa only [CheckCapLowItem.dest,ite_eq_right more] using pc
      have ctx : Context u proofBase (c+w) w (j+1) total :=
        ⟨enter,cursor,ptr,(stable _ (by decide)).trans start.endPtr,(stable _ (by decide)).trans start.proofReg,
          (stable _ (by decide)).trans start.head,(stable _ (by decide)).trans start.mask,(stable _ (by decide)).trans start.width,
          (stable _ (by decide)).trans start.limit,(stable _ (by decide)).trans start.table⟩
      obtain ⟨k,tk,t,body,final,out,agree,keepR⟩:=ih u (c+w) (j+1) (by simp)
        (by simp only [List.length_cons] at count ⊢;omega) (by omega) ctx
        (tail_access frame j id remain (joint ▸ small) ids) (fun a h=>valid _ (List.mem_cons_of_mem _ h)) (proof_frame frame tape)
      refine ⟨n+k,by simp only [List.length_cons] at tk ⊢;omega,t,compose one body,final,?_,?_,fun q h=>(keepR q h).trans (stable q h)⟩
      · rw [size] at out;exact out
      · have eq:=fill_agrees model stream w (c+w) remain
        exact fun q hq=>(agree q hq).trans (eq q hq)

end CommitGolfCandidate.Reconstruction.CheckCapLowLoop
