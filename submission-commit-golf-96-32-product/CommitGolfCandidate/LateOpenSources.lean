import CommitGolfCandidate.LateOpenMemory
import CommitGolfCandidate.LateTrapdoor

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def indices (p : Positions) := p.sort (· ≤ ·)
def ix (xs : List Index) (r : Nat) : Index := xs[r]?.getD ⟨0,by decide⟩
def initial (td : Trapdoor) (p : Positions) := submission.initialState .opening (td,p)

structure Sources (s : MachineState) (xs : List Index) (tree : Levels) (salt : SaltTape) : Prop where
  index : ∀ r < xs.length, wordAt s (indexBase+8*r)=BitVec.ofNat 64 (ix xs r).val
  node : ∀ d ≤ LOG_LENGTH, ∀ j < levelCount d, readBuffer s (nodeAddress d j) 32 = Late.node tree d j
  salts : ∀ i : Index, readBuffer s (saltAddress i) 24 = salt i

theorem node_ok (d j : Nat) (hj : j<levelCount d) :
    tdBase≤nodeAddress d j ∧ nodeAddress d j+32 ≤ indexBase ∧ nodeAddress d j%8=0 := by
  have upper := parent_below_salts d j hj; unfold rowBase at upper
  constructor
  · unfold nodeAddress tdBase;omega
  · exact ⟨by unfold indexBase;omega,by unfold nodeAddress levelOffset gapOffset;omega⟩

theorem salt_ok (i : Index) :
    tdBase≤saltAddress i ∧ saltAddress i+24 ≤ indexBase ∧ saltAddress i%8=0 := by
  have h := i.isLt;change i.val<16777216 at h
  unfold tdBase saltAddress rowBase indexBase
  split <;> omega

theorem Sources.after {s t : MachineState} {xs : List Index} {tree : Levels} {salt : SaltTape}
    (src : Sources s xs tree salt) (size : xs.length≤LENGTH) (a n : Nat)
    (changeMem : Outside s t a n) (high : proofBase≤a) (al : a%8=0) (nl : n%8=0) : Sources t xs tree salt := by
  have cap : xs.length≤16777216 := size
  constructor
  · intro r hr
    apply (changeMem _ (by unfold indexBase MEMORY_BYTES;omega) (by unfold indexBase;omega)
      (Or.inl (by unfold proofBase at high; unfold indexBase;omega))).trans (src.index r hr)
  · intro d hd j hj
    have e := (node_ok d j hj).2.1; unfold indexBase at e
    exact (outside_read changeMem al nl _ _ (by unfold MEMORY_BYTES;omega)
      (Or.inl (by unfold proofBase at high;omega))).trans (src.node d hd j hj)
  · intro i
    have e := (salt_ok i).2.1; unfold indexBase at e
    exact (outside_read changeMem al nl _ _ (by unfold MEMORY_BYTES;omega)
      (Or.inl (by unfold proofBase at high;omega))).trans (src.salts i)

theorem Sources.same_mem {s t : MachineState} {xs tree salt} (src : Sources s xs tree salt) (eq : t.mem=s.mem) :
    Sources t xs tree salt := by
  constructor
  · intro r hr;simpa only [wordAt,MachineState.getMem,eq] using src.index r hr
  · exact fun d hd j hj => (read_congr_mem _ _ _ _ eq).trans (src.node d hd j hj)
  · exact fun i => (read_congr_mem _ _ _ _ eq).trans (src.salts i)

private theorem selected_byte (td : Trapdoor) (p : Positions) (b : InputBuffer) (a : Nat)
    (below : a < 2^64)
    (pick : (submission.inputBuffers .opening (td,p)).find?
      (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some b) :
    (initial td p).getByte (BitVec.ofNat 64 a) = b.byteAt (a-b.address) := by
  apply (initial_input_byte submission .opening (td,p) a below).trans
  unfold inputByte;rw [pick]

private theorem firstBuffer (b c : InputBuffer) (a : Nat)
    (h : b.address≤a ∧ a<b.address+b.length) :
    [b,c].find? (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some b := by
  simp [List.find?_cons,h.1,h.2]

private theorem secondBuffer (b c : InputBuffer) (a : Nat)
    (h : ¬(b.address≤a ∧ a<b.address+b.length)) (k : c.address≤a ∧ a<c.address+c.length) :
    [b,c].find? (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some c := by
  simp [List.find?_cons,h,k.1,k.2]

private theorem fixed_end (td : Trapdoor) : (fixedBuffer tdBase td).address+(fixedBuffer tdBase td).length = indexBase := by
  change 4294971424+(8*3355443200+7)/8=7650414624
  decide

private theorem selected_fixed (td : Trapdoor) (p : Positions) (a : Nat) (lo : tdBase≤a) (hi : a < indexBase) :
    (submission.inputBuffers .opening (td,p)).find? (fun b => decide (b.address≤a ∧ a<b.address+b.length)) =
        some (fixedBuffer tdBase td) := by
  apply firstBuffer
  exact ⟨lo,(fixed_end td).symm ▸ hi⟩

private theorem fixed_in (td : Trapdoor) (p : Positions) (a n : Nat) (lo : tdBase≤a) (hi : a+n ≤ indexBase) :
    readBuffer (initial td p) a n = slice td a n := by
  unfold slice
  apply read_serialized_slice
  intro j hj
  have q : tdBase≤a+j ∧ a+j < indexBase := by omega
  have bound : a+j<2^64 := by unfold indexBase at hi;omega
  have found := selected_fixed td p (a+j) q.1 q.2
  apply (selected_byte td p (fixedBuffer tdBase td) _ bound found).trans
  change td.extractLsb' (8*(a+j-tdBase)) 8 = td.extractLsb' (8*(a-tdBase+j)) 8
  exact congrArg (fun x => td.extractLsb' (8*x) 8) (show a+j-tdBase=a-tdBase+j by omega)

private theorem index_loaded (td : Trapdoor) (p : Positions) (r : Nat) (hr : r < (indices p).length) :
    wordAt (initial td p) (indexBase+8*r) = BitVec.ofNat 64 (ix (indices p) r).val := by
  let a := indexBase+8*r
  let v := ix (indices p) r
  have total : (indices p).length≤LENGTH := by simpa [indices] using Finset.card_le_univ p
  have cap : (indices p).length≤16777216 := total
  have read : readBuffer (initial td p) a 8 = BitVec.ofNat 64 v.val := by
    have law := read_serialized_slice (initial td p) (BitVec.ofNat 64 v.val) a 0 8 (by
      intro j hj
      have hi : a+j<2^64 := by unfold a indexBase;omega
      have start : indexBase≤a+j := by dsimp [a];omega
      have skip : ¬((fixedBuffer tdBase td).address≤a+j ∧ a+j<(fixedBuffer tdBase td).address+(fixedBuffer tdBase td).length) := by
        rw [fixed_end];omega
      have hits : (positionsBuffer indexBase p).address≤a+j ∧ a+j<(positionsBuffer indexBase p).address+(positionsBuffer indexBase p).length := by
        change indexBase≤a+j ∧ a+j < indexBase+8*(indices p).length;dsimp [a];omega
      have found := secondBuffer (fixedBuffer tdBase td) (positionsBuffer indexBase p) (a+j) skip hits
      apply (selected_byte td p (positionsBuffer indexBase p) _ hi found).trans
      dsimp only [positionsBuffer]
      rw [show (a+j-indexBase)/8=r by dsimp [a];omega,show (a+j-indexBase)%8=j by dsimp [a];omega]
      rw [List.getElem?_eq_getElem (show r < (p.sort (· ≤ ·)).length from hr)]
      have vv : v = (indices p)[r] := by simp only [v,ix,List.getElem?_eq_getElem hr,Option.getD_some]
      rw [vv]
      simp only [Nat.zero_add,BitVec.extractLsb',BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (show ((indices p)[r]).val<2^64 by have h := ((indices p)[r]).isLt;change _<16777216 at h;omega)]
      rfl)
    exact law.trans BitVec.extractLsb'_eq_self
  have take := read_buffer_slice (initial td p) a 32 0 8 (by decide)
  have word := read_digest_word (initial td p) a 0 (by dsimp [a,indexBase];omega) (by decide)
  exact word.symm.trans (take.trans read)

theorem initial_sources (td : Trapdoor) (p : Positions) (tree : Levels) (salt : SaltTape)
    (agree : TrapdoorAgrees td tree salt) : Sources (initial td p) (indices p) tree salt where
  index := index_loaded td p
  node d hd j hj := (fixed_in td p _ _ (node_ok _ _ hj).1 (node_ok _ _ hj).2.1).trans (agree.nodes d hd j hj)
  salts i := (fixed_in td p _ _ (salt_ok i).1 (salt_ok i).2.1).trans (agree.salt i)

end CommitGolfCandidate.Late.Open
