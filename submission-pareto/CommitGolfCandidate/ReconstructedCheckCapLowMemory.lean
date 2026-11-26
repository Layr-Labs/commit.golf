import CommitGolfCandidate.ReconstructedCheckCapLowItem

namespace CommitGolfCandidate.Reconstruction.CheckCapLowMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W cap scratch)
open CheckCapLowItem (data reader)
set_option maxRecDepth 15000
set_option maxHeartbeats 1000000

abbrev proofBase : Nat := 10334769248
def Proof (m : Memory) (stream : Nat) := ∀ i<1100000000,m (proofBase/8+i)=W (HonestStream.word stream i)
def Outside (q : Nat) := q<cap/8 ∨ cap/8+4096≤q
def Frame (m n : Memory) := ∀ q,q<2^33→Outside q→n q=m q

theorem source (s : MachineState) (stream c : Nat) (bound : c≤70000000000) (proof : Proof (memoryView s) stream) :
    CheckStream.Placed (reader proofBase c) ∧ CheckStream.Source s (reader proofBase c) stream := by
  refine ⟨⟨by change 10334769248%8=0;decide,by change 10334769248+8*(c/64)+40≤68719476736;omega⟩,?_⟩
  intro k hk
  have h:=proof (c/64+k) (by omega)
  change s.getMem (W ((proofBase+8*(c/64))+8*k))=_
  change s.getMem (W (8*(proofBase/8+(c/64+k))))=_ at h
  rw [show proofBase+8*(c/64)+8*k=8*(proofBase/8+(c/64+k)) by unfold proofBase;omega];exact h

theorem frame (m : Memory) (id stream c w : Nat) (bound : id<1024) : Frame m (data m id stream c w) := by
  intro q hq out
  change q<524288 ∨ 528384≤q at out
  have lo : 524288≤CheckCapLowStore.cell id := by unfold CheckCapLowStore.cell cap;omega
  have hi : CheckCapLowStore.cell id+4≤528384 := by unfold CheckCapLowStore.cell cap;omega
  simp only [data,CheckCapLowStore.copy,writeWord,ite_eq_right (by omega : q≠CheckCapLowStore.cell id),
    ite_eq_right (by omega : q≠CheckCapLowStore.cell id+1),ite_eq_right (by omega : q≠CheckCapLowStore.cell id+2),
    ite_eq_right (by omega : q≠CheckCapLowStore.cell id+3)]

theorem congr_data {m n : Memory} (same : LeafMemory.Agrees m n) (id stream c w : Nat) :
    LeafMemory.Agrees (data m id stream c w) (data n id stream c w) := by
  intro q hq;unfold data CheckCapLowStore.copy writeWord;simp only [same q hq]

theorem frame_of_agrees {m n : Memory} (same : LeafMemory.Agrees n m) : Frame m n := fun q hq _=>same q hq

theorem trans {m n u : Memory} (a : Frame m n) (b : Frame n u) : Frame m u :=
  fun q hq out=>(b q hq out).trans (a q hq out)

theorem proof_frame {m n : Memory} {stream : Nat} (f : Frame m n) (old : Proof m stream) : Proof n stream := by
  intro i hi;rw [f _ (by unfold proofBase;omega) (Or.inr (by unfold proofBase cap;omega))];exact old _ hi

theorem slots_frame {m n : Memory} (xs : List Nat) (bounded : xs.length≤512) (f : Frame m n)
    (old : CheckCapSlots.Contains m scratch xs) : CheckCapSlots.Contains n scratch xs := by
  intro j;have b:=j.isLt
  unfold CheckCapSlots.read
  rw [f _ (by change 8589934171+j.val/2<2^33;omega) (Or.inr (by change 528384≤8589934171+j.val/2;omega))]
  exact old j

def fill (stream w : Nat) : List Nat → Nat → Memory → Memory
  | [],_,m=>m
  | id::xs,c,m=>fill stream w xs (c+w) (data m id stream c w)

theorem fill_agrees {m n : Memory} (same : LeafMemory.Agrees m n) (stream w c : Nat) (ids : List Nat) :
    LeafMemory.Agrees (fill stream w ids c m) (fill stream w ids c n) := by
  induction ids generalizing c m n with
  | nil=>exact same
  | cons i is ih=>exact ih (congr_data same i stream c w) (c+w)

theorem fill_frame (m : Memory) (ids : List Nat) (stream c w : Nat) (bound : ∀ id∈ids,id<1024) :
    Frame m (fill stream w ids c m) := by
  induction ids generalizing c m with
  | nil=>exact fun _ _ _=>rfl
  | cons id ids ih=>
    exact trans (frame m id stream c w (bound id List.mem_cons_self)) (ih _ _ (fun a h=>bound _ (List.mem_cons_of_mem _ h)))

end CommitGolfCandidate.Reconstruction.CheckCapLowMemory
