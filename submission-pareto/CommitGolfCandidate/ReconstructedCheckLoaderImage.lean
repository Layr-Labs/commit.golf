import CommitGolfCandidate.ReconstructedCheckLoader

namespace CommitGolfCandidate.Reconstruction.CheckLoader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecordABI
open TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 1700000
attribute [local irreducible] ArtifactEncoding.decode

private theorem outside (input : CheckInput) (valid : input.proof.length≤8355061248) (a : Nat)
    (away : a<4294971392 ∨ 19000000000≤a) :
    (Artifact.submission.inputBuffers .check input).find?
      (fun b => decide (b.address≤a ∧ a<b.address+b.length))=none := by
  have ps := positions_card_bound input.positions
  simp only [Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,valuesBuffer,Finset.length_sort,Finset.card_attach,
    show Artifact.submission.layout.commitment=4294971392 from rfl,show Artifact.submission.layout.indices=5905584160 from rfl,
    show Artifact.submission.layout.values=6039801952 from rfl,show Artifact.submission.layout.proof=10334769248 from rfl,
    show (DIGEST_BITS+7)/8=32 by decide,show LEAF_SIZE/8=256 by decide,
    show ¬(4294971392≤a ∧ a<4294971392+32) by omega,
    show ¬(5905584160≤a ∧ a<5905584160+8*input.positions.card) by omega,
    show ¬(6039801952≤a ∧ a<6039801952+256*input.positions.card) by omega,
    show ¬(10334769248≤a ∧ a<10334769248+input.proof.length) by omega,decide_false,List.find?_nil]

theorem image_word (input : CheckInput) (valid : input.proof.length≤8355061248) (j : Nat) (hj : j<126) :
    (initial input).getMem (W (68719475728+8*j))=tableWord j := by
  rw [initial,initial_input_word Artifact.submission .check input _ (by omega)]
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro b hb
  unfold inputByte
  rw [outside input valid _ (Or.inr (by omega)),image_base,ite_eq_left (by omega)]
  rw [show 68719475728+8*j+b-68719475728=8*j+b by omega]

theorem zero_flag (input : CheckInput) (valid : input.proof.length≤8355061248) (j : Nat) (hj : j<128) :
    (initial input).getMem (W (4259840+8*j))=0 := by
  rw [initial,initial_input_word Artifact.submission .check input _ (by omega)]
  have atByte (b : Nat) (hb : b∈Finset.range 8) :
      inputByte Artifact.submission .check input (4259840+8*j+b)=0 := by
    have sm := Finset.mem_range.mp hb
    unfold inputByte
    rw [outside input valid _ (Or.inl (by omega)),image_base,ite_eq_right (by omega)]
  have z : (∑ b ∈ Finset.range 8,(inputByte Artifact.submission .check input (4259840+8*j+b)).toNat*2^(8*b))=0 := by
    apply Finset.sum_eq_zero
    intro b hb;rw [atByte b hb];simp
  rw [z];rfl

private def packedWord (j : Nat) := W (∑ b ∈ Finset.range 8,
  (Artifact.checkData.get 8 ⟨(8*j+b)%1008,by omega⟩).toNat*2^(8*b))

private theorem packed (j : Nat) (bound : j<126) : tableWord j=packedWord j := by
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro b hb
  have below := Finset.mem_range.mp hb
  have h : 8*j+b<1008 := by omega
  have digit := ArtifactEncoding.getD_decode 8 Artifact.checkData (8*j+b) h
  rw [List.getD_eq_getElem?_getD] at digit
  change ((ArtifactEncoding.decode 8 Artifact.checkData)[8*j+b]?.getD 0).toNat*_=_
  rw [digit]
  have idx : (⟨8*j+b,h⟩ : Fin 1008)=⟨(8*j+b)%1008,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt h).symm
  exact congrArg (fun z => (Artifact.checkData.get 8 z).toNat*2^(8*b)) idx

theorem low_table (i : Fin 15) : tableWord (1+(10+i.val))=W (CheckMixed.width i) := by
  rw [packed _ (by have := i.isLt;omega)];exact (by decide +kernel : ∀ z : Fin 15,packedWord (1+(10+z.val))=W (CheckMixed.width z)) i
theorem divisor_table (i : Fin 15) : tableWord (26+(10+i.val))=W (CheckMixed.base i) := by
  rw [packed _ (by have := i.isLt;omega)];exact (by decide +kernel : ∀ z : Fin 15,packedWord (26+(10+z.val))=W (CheckMixed.base z)) i
private def validRo (n : Nat) := (CheckParentRun.ro (2097152+8*n)).all (fun v => decide (packedWord n=v))
private theorem bank0 : ∀ k : Fin 16,validRo (0+k.val)=true := by decide +kernel
private theorem bank1 : ∀ k : Fin 16,validRo (16+k.val)=true := by decide +kernel
private theorem bank2 : ∀ k : Fin 16,validRo (32+k.val)=true := by decide +kernel
private theorem bank3 : ∀ k : Fin 16,validRo (48+k.val)=true := by decide +kernel
private theorem bank4 : ∀ k : Fin 16,validRo (64+k.val)=true := by decide +kernel
private theorem bank5 : ∀ k : Fin 16,validRo (80+k.val)=true := by decide +kernel
private theorem bank6 : ∀ k : Fin 16,validRo (96+k.val)=true := by decide +kernel
private theorem bank7 : ∀ k : Fin 16,validRo (112+k.val)=true := by decide +kernel

private theorem joinBanks (f : Nat → Bool)
    (b0 : ∀ c : Fin 16, f (0+c.val)=true)
    (b1 : ∀ c : Fin 16, f (16+c.val)=true)
    (b2 : ∀ c : Fin 16, f (32+c.val)=true)
    (b3 : ∀ c : Fin 16, f (48+c.val)=true)
    (b4 : ∀ c : Fin 16, f (64+c.val)=true)
    (b5 : ∀ c : Fin 16, f (80+c.val)=true)
    (b6 : ∀ c : Fin 16, f (96+c.val)=true)
    (b7 : ∀ c : Fin 16, f (112+c.val)=true)
    (i : Fin 126) : f i.val=true := by
  let row : Fin 8 := ⟨i.val/16,by have := i.isLt;omega⟩
  let col : Fin 16 := ⟨i.val%16,by omega⟩
  have rs (r : Fin 8) : f (16*r.val+col.val)=true := by
    fin_cases r
    · exact b0 col
    · exact b1 col
    · exact b2 col
    · exact b3 col
    · exact b4 col
    · exact b5 col
    · exact b6 col
    · exact b7 col
  have verified :=  rs row
  have decom : 16*row.val+col.val=i.val := by dsimp [row,col];omega
  rw [decom] at verified
  exact verified

private theorem optionValue (o : Option Word) (a w : Word) (h : o.all (fun v => decide (a=v))=true)
    (eq : o=some w) : a=w := by subst o;simpa using h

private theorem ro_table (i : Fin 126) (w : Word) (hw : CheckParentRun.ro (2097152+8*i.val)=some w) : tableWord i.val=w :=
  (packed i.val i.isLt).trans (optionValue _ _ _ (joinBanks validRo bank0 bank1 bank2 bank3 bank4 bank5 bank6 bank7 i) hw)

theorem tables (s : MachineState) (image : ∀ j<126,s.getMem (W (2097152+8*j))=tableWord j)
    (mask : s.getMem (W CheckLayout.maskCell)=0xffffffff) : CheckLayout.Tables s := by
  refine ⟨?_,?_,mask,?_⟩
  · intro i
    have h := i.isLt
    have physical : CheckLayout.lowCell i=2097152+8*(1+(10+i.val)) := by unfold CheckLayout.lowCell;omega
    change s.getMem (W (CheckLayout.lowCell i))=_
    rw [physical,image _ (by omega),low_table]
  · intro i
    have h := i.isLt
    have physical : wordAddress (CheckLayout.divCell i)=W (2097152+8*(26+(10+i.val))) := by
      unfold wordAddress CheckLayout.divCell;congr 1;omega
    rw [physical,image _ (by omega),divisor_table]
  · intro a w al known
    have range : 2097560≤a ∧ a<2098152 := by unfold CheckParentRun.ro at known;split_ifs at known <;> first | contradiction | omega
    let j : Fin 126 := ⟨(a-2097152)/8,by omega⟩
    have eq : a=2097152+8*j.val := by dsimp [j];omega
    change s.getMem (W a)=_
    rw [eq,image j.val j.isLt];exact ro_table j w (eq ▸ known)

end CommitGolfCandidate.Reconstruction.CheckLoader
