import CommitGolfCandidate.ReconstructedCheckCapPrepare
import CommitGolfCandidate.ReconstructedCheckCapParents
import CommitGolfCandidate.ReconstructedCheckCapMembership

namespace CommitGolfCandidate.Reconstruction.CheckCapLevel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks Binding
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CheckCapScanData (W fp)
set_option maxRecDepth 16000

def clear (q : Nat) := CheckCapLowMemory.Outside q ∧ (q<532480 ∨ 532608≤q) ∧
  (q<8589934171 ∨ 8589934300≤q) ∧ (q<8589934144 ∨ 8589934162≤q) ∧ (q<8589934427 ∨ 8589934431≤q)
def Frame (s t : MachineState) := ∀ q,q<2^33→clear q→memoryView t q=memoryView s q
def Live (f : Nat→Bool) (d id : Nat) := HonestSizeSchedule.row f (9-d) (id-2^d)
def node (s : MachineState) (id : Nat) := CommitParents.cell s (CheckParentHeap.base id)
def view (m : Memory) (id : Nat) : Binding.Digest :=
  CheckEdge.digest (m (CheckCapLowStore.cell id)) (m (CheckCapLowStore.cell id+1))
    (m (CheckCapLowStore.cell id+2)) (m (CheckCapLowStore.cell id+3))
def parsed (f : Nat→Bool) (d stream c : Nat) (m : Memory) :=
  CheckCapRepair.result d (Encoding.lows d) m (CapSchedule.pending f d) stream c

structure Data (s : MachineState) (stream : Nat) : Prop where
  widths : ∀ d,0<d→d≤9→memoryView s (CheckCapLowSetup.widthCell d)=W (Encoding.lows d)
  mask : memoryView s CheckCapLowSetup.maskCell=0xffffffff
  constants : CheckParentGeometry.constants s
  proof : CheckCapLowMemory.Proof (memoryView s) stream

structure Boundary (f : Nat→Bool) (stream d c : Nat) (s : MachineState) : Prop where
  ready : CheckParentExit.Ready s d (W c)
  radix : s.getReg .x21=211
  magic : s.getReg .x26=W CheckGroupRadix.magic
  proof : s.getReg .x27=W CheckCapLowMemory.proofBase
  data : Data s stream
  rows : 0<d→HonestSizeRows.Rows f d 0 s
  canonical : ∀ id : Nat, 2^d ≤ id → id < 2^(d+1) → Live f d id=true→Canonical d (node s id)

structure Bases (m : Memory) (s : MachineState) : Prop where
  same : ∀ id,id<1024→view m id=node s id

structure Rejected (t : MachineState) : Prop where
  pc : t.pc=addr 672
  stack : t.getReg .x2=W CheckLayout.sp
  frame : t.getReg .x8=W fp

structure Passed (o : Oracle) (f : Nat→Bool) (stream d c : Nat) (s t : MachineState)
    (log : List PublicRow) (m : Memory) : Prop where
  valid : (parsed f d stream c m).valid=true
  boundary : Boundary f stream (d-1) (parsed f d stream c m).cursor t
  cursor : (parsed f d stream c m).cursor≤c+70000
  stored : ∀ p : Nat, 2^(d-1) ≤ p → p < 2^d → CheckCapMembership.used f d p=true→
    node t p=parent (oracleCompression o) (d-1) (view (parsed f d stream c m).data (2*p))
      (view (parsed f d stream c m).data (2*p+1))
  edges : ∀ p : Nat, 2^(d-1) ≤ p → p < 2^d → ∀ side : Bool,Live f d (2*p+side.toNat)=true→
    Nonempty (CheckPath.Edge o log (d-1) side (node s (2*p+side.toNat)) (node t p))

def Contract (o : Oracle) (f : Nat→Bool) (stream : Nat) := ∀ d c s,0<d→d≤9→c+70000*d≤70000000000→
  Boundary f stream d c s → ∃ n t log m,n≤56+322*2^(d-1) ∧ log.length≤HonestSizeSchedule.population f (d-1)*work (d-1) ∧
    Segment o n s t log ∧ Frame s t ∧ Bases m s ∧
    (((parsed f d stream c m).valid=false ∧ Rejected t) ∨ Passed o f stream d c s t log m)

end CommitGolfCandidate.Reconstruction.CheckCapLevel
