import CommitGolfCandidate.ReconstructedCapControlExact
import CommitGolfCandidate.ReconstructedCapPayload

namespace CommitGolfCandidate.Reconstruction.CapControlValues
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestRanges HonestProtected HonestCapStages
open CommitBlocks (addr)
open CapControlForward (shape)
open OpeningCursor (W)
set_option maxRecDepth 26000
set_option maxHeartbeats 25000000
attribute [local irreducible] ArtifactEncoding.decode

abbrev Cells := List (Word×Word)
def value (rows : Cells) (q : Word) : Range := match rows with
  | [] => any
  | (a,v)::tail => if q=a then point v else value tail q
def ctx (rows : Cells) : Context := ⟨rows.map (fun x => point x.1),value rows,[]⟩
def reads (s : MachineState) (rows : Cells) := ∀ a v, (a,v)∈rows → s.getMem a=v

theorem definite (s : MachineState) (rows : Cells) (h : reads s rows) (q : Word) :
    Contains (value rows q) (s.getMem q) := by
  induction rows with
  | nil => exact arbitrary _
  | cons pair tail ih =>
    rcases pair with ⟨a,v⟩
    unfold value
    by_cases atWord : q=a
    · rw [ite_eq_left atWord,atWord,h a v List.mem_cons_self];exact precise _
    · rw [ite_eq_right atWord];exact ih (fun a v found => h a v (List.mem_cons_of_mem _ found))

def checked (i fuel j : Nat) (rows : Cells) (initial final : Facts) :=
  CapControlExact.check (fun pc => if pc=addr j then shape final else shape []) fuel (addr i) ((shape initial).model (ctx rows))

theorem compute (s t : MachineState) (coin : Bool) (i n j : Nat) (rows : Cells) (initial final : Facts)
    (cert : checked i n j rows initial final=true) (pc : s.pc=addr i) (next : t.pc=addr j)
    (reg : holds s initial) (mem : reads s rows) (path : HonestCapState.Path coin s t) : holds t final := by
  have input : Holds (ctx rows) (shape initial) s := by
    refine ⟨?_,(by intro _ _ h;cases h),fun q _ => definite s rows mem q⟩
    intro r v found
    obtain ⟨⟨a,b⟩,old,same⟩ := List.mem_map.mp found
    cases same;rw [reg a b old];exact precise _
  have post := CapControlExact.sound (fun pc => if pc=addr j then shape final else shape []) n _ _ cert s t coin pc (models_shape input) path
  simp only [next,ite_true] at post
  intro r v member
  have h := post r (point v) (List.mem_map.mpr ⟨(r,v),member,rfl⟩)
  exact BitVec.eq_of_toNat_eq (Nat.le_antisymm h.2 h.1)

def lowCells (d : Nat) : Cells := [(W (2097152+8*d),W (Encoding.lows d)),(68719474112,4294967295)]
def lowOut (d : Nat) : Facts := [(.x21,W (8*d)),(.x22,CapPayload.mask (Encoding.lows d-192)),(.x23,W (Encoding.lows d-192))]
def paidCells (d : Nat) : Cells := [(W (2097352+8*d),W (Binding.width d)),(68719474104,2147483647)]
def paidOut (d : Nat) : Facts := [(.x21,0),(.x22,0xffffffffffffffff),(.x23,CapPayload.mask (Binding.width d-192)),(.x29,2147483647)]

theorem lowTable (d : Fin 9) : checked 1483 26 1512 (lowCells (d.val+1)) (CapControlForward.beforeWidth (d.val+1)) (lowOut (d.val+1))=true := by
  exact (by decide +kernel : ∀ k : Fin 9, checked 1483 26 1512 (lowCells (k.val+1)) (CapControlForward.beforeWidth (k.val+1)) (lowOut (k.val+1))=true) d

theorem paidTable (d : Fin 2) : checked 1581 16 1603 (paidCells (d.val+8)) (CapControlForward.beforeGroup (d.val+8)) (paidOut (d.val+8))=true := by
  exact (by decide +kernel : ∀ k : Fin 2, checked 1581 16 1603 (paidCells (k.val+8)) (CapControlForward.beforeGroup (k.val+8)) (paidOut (k.val+8))=true) d

end CommitGolfCandidate.Reconstruction.CapControlValues
