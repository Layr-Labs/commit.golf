import CommitGolfCandidate.S5PassEntry
import CommitGolfCandidate.S5NodeFrame
import CommitGolfCandidate.S5Runs
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64

def StageLaw (d : Height) : Prop := ∀ (o : Oracle) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape),
    s.pc=pcAt (passHeader d) → Common s → TreeState o.compression base salt d.val s →
    ∃ t,t.pc=pcAt (passEnd d) ∧ Common t ∧ TreeState o.compression base salt (d.val+1) t ∧
      Runs .commit true o s t (passSteps d) (passCycles d) (count d*calls d)

theorem transfer_tree {H base salt d s t} (tree : TreeState H base salt d s) (mem : t.mem=s.mem) :
    TreeState H base salt d t := by
  refine ⟨fun h lh j hj=>(read_congr_mem t s _ _ mem).trans (tree.nodes h lh j hj),
    fun i=>(read_congr_mem t s _ _ mem).trans (tree.salts i),?_⟩
  intro h j k pad
  exact ⟨(read_congr_mem t s _ _ mem).trans (tree.pads h j k pad).1,
    fun safe=>(read_congr_mem t s _ _ mem).trans ((tree.pads h j k pad).2 safe)⟩
theorem transfer_rows {H base d n s t} (rows : doneRows H base d n s) (mem : t.mem=s.mem) : doneRows H base d n t :=
  fun j hj=>(read_congr_mem t s _ _ mem).trans (rows j hj)
end CommitGolfCandidate.S5Machine
