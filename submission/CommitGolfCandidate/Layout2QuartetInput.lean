import CommitGolfCandidate.Layout2QuartetFormat
import CommitGolfCandidate.Layout2QuartetPrefix
import CommitGolfCandidate.Layout2Delivered
import CommitGolfCandidate.Layout2Loaded

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000
def prepared (i : CheckInput) : CheckInput := { i with proof:=normalize i.positions i.proof }

@[simp] theorem prepared_len (i : CheckInput) : (prepared i).proof.length=i.proof.length :=
  length_transform .. 

theorem init_entry (i : CheckInput) :
    (candidate.initialState .check i).getReg .x13=addr indicesBase ∧ (candidate.initialState .check i).pc=pc 0 := ⟨rfl,rfl⟩

private def abiReg (c : Submission) (k n : Nat) : Reg → Word
  | .x2 => addr (dataBase (c.image .check))
  | .x10 => addr c.layout.message
  | .x11 => addr c.layout.commitment
  | .x12 => addr c.layout.trapdoor
  | .x13 => addr c.layout.indices
  | .x14 => addr c.layout.values
  | .x15 => addr c.layout.proof
  | .x16 => addr k
  | .x17 => addr n
  | _ => 0

private theorem initial_reg (c : Submission) (i : CheckInput) (r : Reg) :
    (c.initialState .check i).getReg r=abiReg c i.positions.card i.proof.length r := by
  cases r <;> rfl

theorem same_args_for (c : Submission) (i v : CheckInput) (r : Reg)
    (pos : i.positions=v.positions) (len : i.proof.length=v.proof.length) :
    (c.initialState .check i).getReg r=(c.initialState .check v).getReg r := by
  rw [initial_reg,initial_reg,pos,len]

theorem same_args (c : Submission) (i : CheckInput) (r : Reg) :
    (c.initialState .check i).getReg r=(c.initialState .check (prepared i)).getReg r := by
  rw [initial_reg,initial_reg,prepared_len];rfl

attribute [local irreducible] Submission.initialState ArtifactEncoding.decode
theorem load_indices (i : CheckInput) : Indices (candidate.initialState .check i) i.positions.card (selectors i.positions) := by
  intro j present
  have bound:=Checker.checker_positions_bound i
  let w:=1174405636+j
  have eq : 8*w=indicesBase+8*j := by dsimp [w,indicesBase];omega
  have word:=bword (s:=candidate.initialState .check i) (t:=QAssembly.submission.initialState .check i)
    w (by dsimp [w,MEMORY_BYTES];omega)
    (fun b small=>below_table i _ (by dsimp [w,tableBase];omega))
  change (candidate.initialState .check i).getMem (addr (8*w))=(QAssembly.submission.initialState .check i).getMem (addr (8*w)) at word
  rw [eq] at word
  have old:=Checker.check_input_position i j present
  change (QAssembly.submission.initialState .check i).getMem (addr (indicesBase+8*j))=addr _ at old
  rw [word,old,low2]
  simp [selectors,List.getElem?_eq_getElem (by simpa using present : j<(i.positions.sort (· ≤ ·)).length)]

private theorem beyond (i : CheckInput) (q : Nat) (fit : q<MEMORY_BYTES)
    (outside : q<proofBase ∨ proofBase+i.proof.length≤q) :
    byte (candidate.initialState .check (prepared i)) q=byte (candidate.initialState .check i) q := by
  have small : q<2^64 := by unfold MEMORY_BYTES at fit;omega
  refine (initial_input_byte candidate .check (prepared i) q small).trans
    (Eq.trans ?_ (initial_input_byte candidate .check i q small).symm)
  have none : ¬(candidate.layout.proof≤q ∧ q<candidate.layout.proof+i.proof.length) := by
    change ¬(proofBase≤q ∧ q<proofBase+i.proof.length);omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,prepared_len,none,decide_false,cond_false,List.find?_nil]
  rfl

theorem prepared_memory (i : CheckInput) (fits : i.proof.length≤8959041024) (long : 534*i.positions.card ≤ i.proof.length)
    {m} (wrote : Writes (candidate.initialState .check i) m proofBase (534*i.positions.card)
      (payload (candidate.initialState .check i) i.positions.card (selectors i.positions))) (q : Nat) (fit : q<MEMORY_BYTES) :
    byte m q=byte (candidate.initialState .check (prepared i)) q := by
  by_cases hit : proofBase≤q ∧ q<proofBase+i.proof.length
  · let j:=q-proofBase
    have eq : q=proofBase+j := by dsimp [j];omega
    have jfit : j < i.proof.length := by dsimp [j];omega
    have read (u : CheckInput) (n : Nat) (valid : u.proof.length≤8959041024) (pres : n<u.proof.length) :
        byte (candidate.initialState .check u) (proofBase+n)=u.proof[n]?.getD 0 := by
      rw [below_table u _ (by unfold proofBase tableBase;omega)]
      exact (Checker.check_input_proof_byte u valid n pres).trans (by simp [pres])
    rw [wrote q fit,eq,read (prepared i) j (by simpa using fits) (by simpa using jfit)]
    change _=(transform false i.positions.card (selectors i.positions) i.proof)[j]?.getD 0
    rw [read_transform _ _ _ _ _ long jfit]
    by_cases rec : j<534*i.positions.card
    · rw [if_pos (by omega)]
      simp only [payload,Nat.add_sub_cancel_left]
      exact read i _ fits (((index_facts false _ _ j).1 rec).trans_le long)
    · rw [if_neg (by omega),index,if_neg rec]
      exact read i j fits jfit
  · have outside : q<proofBase ∨ proofBase+i.proof.length≤q := by omega
    exact (wrote.outside q fit (by omega)).trans (beyond i q fit outside).symm

end CommitGolfCandidate.Layout2.Quartet
