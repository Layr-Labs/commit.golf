import CommitGolfCandidate.ReconstructedOpeningHeader336

namespace CommitGolfCandidate.Reconstruction.OpeningHeader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningLinear
open OpeningHeaderAddress OpeningCursor TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 20000

theorem front (o : Oracle) (x : Context) (s : MachineState) (pc : s.pc=addr 237) (fits : Fits s (s237 x)) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 108 s t ∧ t.pc=addr 345 ∧ Fits t (s345 x) := by
  obtain ⟨u248,r237,p248,h248⟩ := OpeningLinear.block (span237 o x) (by decide) entries237 s pc fits
  obtain ⟨u261,r248,p261,h261⟩ := OpeningLinear.block (span248 o x) (by decide) entries248 u248 p248 h248
  obtain ⟨u273,r261,p273,h273⟩ := OpeningLinear.block (span261 o x) (by decide) entries261 u261 p261 h261
  obtain ⟨u286,r273,p286,h286⟩ := OpeningLinear.block (span273 o x) (by decide) entries273 u273 p273 h273
  obtain ⟨u298,r286,p298,h298⟩ := OpeningLinear.block (span286 o x) (by decide) entries286 u286 p286 h286
  obtain ⟨u308,r298,p308,h308⟩ := OpeningLinear.block (span298 o x) (by decide) entries298 u298 p298 h298
  obtain ⟨u318,r308,p318,h318⟩ := OpeningLinear.block (span308 o x) (by decide) entries308 u308 p308 h308
  obtain ⟨u327,r318,p327,h327⟩ := OpeningLinear.block (span318 o x) (by decide) entries318 u318 p318 h318
  obtain ⟨u336,r327,p336,h336⟩ := OpeningLinear.block (span327 o x) (by decide) entries327 u327 p327 h327
  obtain ⟨u345,r336,p345,h345⟩ := OpeningLinear.block (span336 o x) (by decide) entries336 u336 p336 h336
  exact ⟨u345,(CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose r237 r248) r261) r273) r286) r298) r308) r318) r327) r336),p345,h345⟩

/-- Only the five saved sibling pointers alter RAM while computing the header. -/
theorem front_memory (x : Context) (w : Nat) (away : w<8589934265 ∨ 8589934269<w) :
    (s345 x).mem w=x.initial.mem w := by
  have a : w≠8589934269 := by omega
  have b : w≠8589934268 := by omega
  have c : w≠8589934267 := by omega
  have d : w≠8589934266 := by omega
  have e : w≠8589934265 := by omega
  change (if w=8589934265 then _ else if w=8589934266 then _ else if w=8589934267 then _ else
    if w=8589934268 then _ else if w=8589934269 then _ else x.initial.mem w)=_
  simp only [a,b,c,d,e,ite_false]

end CommitGolfCandidate.Reconstruction.OpeningHeader
