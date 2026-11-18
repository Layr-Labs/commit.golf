import CommitGolfCandidate.PhaseSite

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 12000
set_option maxHeartbeats 1900000

def stitchedWord (prefixImage : Image) (n : Nat) : BitVec 32 :=
  if n<761 then (prefixImage.code[n]?).getD 0 else (wordAt n).getD 0

def stitched (prefixImage : Image) : Image :=
  ⟨(List.range 2680).map (stitchedWord prefixImage),[]⟩

theorem fetched_base (im : Image) (state : MachineState) (n : Nat) (op : Instr)
    (within : n<2680) (pc : state.pc=addr (4096+4*n))
    (dec : (im.code[n]?).bind Opening.decodeBase=some op) :
    fetch im state=some (.base op) := by
  have current : state.pc.toNat=4096+4*n := by
    rw [pc,addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];omega
  rw [fetch,current,ite_eq_left (by omega),show (4096+4*n-4096)/4=n by omega]
  cases row : im.code[n]? with
  | none => simp [row] at dec
  | some w =>
    simp [row,Opening.decodeBase] at dec
    cases d : decodeInstruction w with
    | none => simp [d] at dec
    | some result =>
      cases result with
      | base inst => simp [d] at dec;simpa [dec] using d
      | word op rd rs₁ rs₂ => simp [d] at dec
      | sraiw rd rs sh => simp [d] at dec

theorem stitched_get (im : Image) (n : Nat) (within : n<2680) :
    (stitched im).code[n]?=some (stitchedWord im n) := by
  simp [stitched,List.getElem?_map,List.getElem?_range,within]

theorem stitched_fetch (prefixImage : Image) (n : Nat) (op : Instr) (v : MachineState)
    (high : 761≤n) (within : n<2680) (d : decodeAt n=some op)
    (entry : v.pc=addr (4096+4*n)) : fetch (stitched prefixImage) v=some (.base op) := by
  apply fetched_base _ _ _ _ within entry
  rw [stitched_get _ _ within,stitchedWord,if_neg (by omega)]
  unfold decodeAt at d
  cases reply : wordAt n with
  | none => simp [reply] at d
  | some w => simpa [reply] using d

theorem all_sites_inside (p : Fin 4) (f : Fin 18) :
    762≤fieldPC p f ∧ fieldPC p f+2*(widths p f).length≤2680 := by
  exact (show ∀ p : Fin 4, ∀ f : Fin 18,
    762≤fieldPC p f ∧ fieldPC p f+2*(widths p f).length≤2680 by decide) p f

theorem every_site_fetches (prefixImage : Image) (p : Fin 4) (f : Fin 18)
    (n : Nat) (op : Instr) (low : fieldPC p f≤n) (high : n<fieldPC p f+2*(widths p f).length)
    (dec : decodeAt n=some op) (v : MachineState) (pc : v.pc=addr (4096+4*n)) :
    fetch (stitched prefixImage) v=some (.base op) := by
  have :=all_sites_inside p f
  exact stitched_fetch _ _ _ _ (by omega) (by omega) dec pc

#print axioms every_site_fetches
end TwoPermutationPrototype.PhaseOpening
