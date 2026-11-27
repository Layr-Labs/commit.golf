import CommitGolfCandidate.Stage3cTreeFrame
import CommitGolfCandidate.Stage3cInputBlock
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem gap_limit (h : Height) (p : Nat) (inside : p<count h) : tagAddr h p+32≤rowBase := by
  have e:=gap_ceiling h p inside
  unfold tdBase levelOffset rowBase LENGTH LOG_LENGTH at *;omega

theorem salt_limits (ix : Index) : rowBase≤saltAddress ix.val ∧ saltAddress ix.val+24≤scratchBase := by
  have hi:=ix.isLt;change ix.val<16777216 at hi
  unfold saltAddress rowBase scratchBase;omega

theorem node_frame {H : Compression} {h : Height} {p : Nat} {s t : MachineState} {base : Nat→Output} {salt : Late.SaltTape}
    (before : TreeState H base salt h.val s) (effect : NodeEffect H h p s t) (inside : p<count h) :
    TreeState H base salt h.val t := by
  have dest:=parent_below_salts _ _ inside
  have gap:=gap_limit h p inside
  constructor
  · intro k lo i hi
    have near:=parent_below_salts _ _ hi
    have nd:=node_before (k:=h.val+1) (i:=p) (by omega) (by have :=h.isLt;change k<24;omega) hi
    refine (effect.outside _ 32 (by change _≤2^36;unfold rowBase at near;omega) (Or.inl nd) ?_).trans (before.nodes k lo i hi)
    intro _;refine ⟨?_,Or.inl (by unfold scratchBase rowBase at *;omega)⟩
    rcases node_gap_apart k i h p with a|b
    · exact Or.inl a
    · exact Or.inr (by omega)
  · intro ix
    have limits:=salt_limits ix
    refine (effect.outside _ 24 (by change _≤2^36;unfold scratchBase at limits;omega) (Or.inr (by omega)) ?_).trans (before.salts ix)
    exact fun _=>⟨Or.inr (by omega),Or.inl limits.2⟩
  · intro g j valid
    have cap:=gap_limit g j valid
    have old:=before.pads g j valid
    have apart:=node_gap_apart (h.val+1) p g j
    constructor
    · refine (effect.outside _ 24 (by change _≤2^36;unfold rowBase at cap;omega) (by rcases apart with x|x;exact Or.inr (by omega);exact Or.inl (by omega)) ?_).trans old.1
      intro _;refine ⟨?_,Or.inl (by unfold scratchBase rowBase at *;omega)⟩
      unfold Apart tagAddr;rw [source_address,source_address];omega
    · intro plain
      refine (effect.outside _ 8 (by change _≤2^36;unfold rowBase at cap;omega) (by rcases apart with x|x;exact Or.inr (by omega);exact Or.inl (by omega)) ?_).trans (old.2 plain)
      intro cut
      exact ⟨distinct_tag g h j p valid inside (fun eq=>plain (eq ▸ cut)),Or.inl (by unfold scratchBase rowBase at *;omega)⟩

theorem close_level {H : Compression} {h : Height} {s : MachineState} {base : Nat→Output} {salt : Late.SaltTape}
    (before : TreeState H base salt h.val s) (built : doneRows H base h.val (count h) s) :
    TreeState H base salt (h.val+1) s := by
  refine ⟨?_,before.salts,before.pads⟩
  intro k lo i hi;by_cases eqn : k=h.val+1
  · subst k;exact built i hi
  · exact before.nodes k (by omega) i hi
end CommitGolfCandidate.Chained.BinaryMachine
