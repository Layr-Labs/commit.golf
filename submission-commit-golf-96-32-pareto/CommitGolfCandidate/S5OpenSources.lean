import CommitGolfCandidate.S5OpenMemory
import CommitGolfCandidate.S5TreeFrame

namespace CommitGolfCandidate.S5Machine.Open
open CommitGolfCandidate.Late (Levels SaltTape gapOffset)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def indices (p : Positions) := p.sort (· ≤ ·)
def ix (xs : List Index) (r : Nat) : Index := xs[r]?.getD ⟨0,by decide⟩
def initial (td : Trapdoor) (p : Positions) := Artifact.submission.initialState .opening (td,p)

def sourceCount (d : Nat) := if d<24 then S4.radix d*S4.rowCount d else levelCount d

structure Sources (s : MachineState) (xs : List Index) (tree : Levels) (salt : SaltTape) : Prop where
  index : ∀ r < xs.length, wordAt s (indexBase+8*r)=BitVec.ofNat 64 (ix xs r).val
  node : ∀ d ≤ LOG_LENGTH, ∀ j < sourceCount d, readBuffer s (nodeAddress d j) 32 = Late.node tree d j
  salts : ∀ i : Index, readBuffer s (saltAddress i) 24 = salt i

theorem node_ok (d j : Nat) (hj : j<sourceCount d) :
    tdBase≤nodeAddress d j ∧ nodeAddress d j+32 ≤ tdEnd ∧ nodeAddress d j%8=0 := by
  have aligned:=nodeAligned d j
  have top : nodeAddress d j+32≤rowBase := by
    by_cases small : d<24
    · have wide : j<S4.radix d*S4.rowCount d := by simpa [sourceCount,small] using hj
      have rad : 0<S4.radix d := by unfold S4.radix;split <;> decide
      have parent : j/S4.radix d<S4.rowCount d := (Nat.div_lt_iff_lt_mul rad).mpr (Nat.mul_comm .. ▸ wide)
      have rwid := S4.row_width ⟨d,small⟩
      have valid : j/S4.radix d<levelCount (d+1) := by
        unfold levelCount;rw [Nat.min_eq_left (by omega)];exact rwid ▸ parent
      have digit:=Nat.mod_lt j rad
      have eq:=row_slot d (j/S4.radix d) (j%S4.radix d) digit
      rw [Nat.div_add_mod] at eq
      rw [eq];have en:=row_after d _ small valid
      have padded:=padded_region (d+1)
      have lim : S4.radix d≤3:=by unfold S4.radix;split <;> decide
      omega
    · exact parent_below_salts _ _ (by simpa [sourceCount,small] using hj)
  exact ⟨by unfold tdBase nodeAddress;omega,top.trans (by decide),aligned⟩

theorem salt_ok (i : Index) :
    tdBase≤saltAddress i ∧ saltAddress i+24 ≤ tdEnd ∧ saltAddress i%8=0 := by
  have h := i.isLt;change i.val<16777216 at h
  unfold tdBase saltAddress rowBase tdEnd
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
    have e := (node_ok d j hj).2.1; unfold tdEnd at e
    exact (outside_read changeMem al nl _ _ (by unfold MEMORY_BYTES;omega)
      (Or.inl (by unfold proofBase at high;omega))).trans (src.node d hd j hj)
  · intro i
    have e := (salt_ok i).2.1; unfold tdEnd at e
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
    (pick : (Artifact.submission.inputBuffers .opening (td,p)).find?
      (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some b) :
    (initial td p).getByte (BitVec.ofNat 64 a) = b.byteAt (a-b.address) := by
  apply (initial_input_byte Artifact.submission .opening (td,p) a below).trans
  unfold inputByte;rw [pick]

private theorem firstBuffer (b c : InputBuffer) (a : Nat)
    (h : b.address≤a ∧ a<b.address+b.length) :
    [b,c].find? (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some b := by
  simp [List.find?_cons,h.1,h.2]

private theorem secondBuffer (b c : InputBuffer) (a : Nat)
    (h : ¬(b.address≤a ∧ a<b.address+b.length)) (k : c.address≤a ∧ a<c.address+c.length) :
    [b,c].find? (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some c := by
  simp [List.find?_cons,h,k.1,k.2]

private theorem fixed_end (td : Trapdoor) : (fixedBuffer tdBase td).address+(fixedBuffer tdBase td).length = tdEnd := by
  change 4294975488+(8*2818576384+7)/8=7113551872
  decide

private theorem selected_fixed (td : Trapdoor) (p : Positions) (a : Nat) (lo : tdBase≤a) (hi : a < tdEnd) :
    (Artifact.submission.inputBuffers .opening (td,p)).find? (fun b => decide (b.address≤a ∧ a<b.address+b.length)) =
        some (fixedBuffer tdBase td) := by
  apply firstBuffer
  exact ⟨lo,(fixed_end td).symm ▸ hi⟩

private theorem fixed_in (td : Trapdoor) (p : Positions) (a n : Nat) (lo : tdBase≤a) (hi : a+n ≤ tdEnd) :
    readBuffer (initial td p) a n = slice td a n := by
  unfold slice
  apply read_serialized_slice
  intro j hj
  have q : tdBase≤a+j ∧ a+j < tdEnd := by omega
  have bound : a+j<2^64 := by unfold tdEnd at hi;omega
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
        rw [fixed_end];unfold tdEnd indexBase at *; omega
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
  node d hd j hj := by
    apply (fixed_in td p _ _ (node_ok _ _ hj).1 (node_ok _ _ hj).2.1).trans
    by_cases valid : j<levelCount d
    · exact agree.nodes _ hd _ valid
    · have low : d<24 := by
        by_contra! high
        unfold sourceCount at hj
        rw [if_neg (Nat.not_lt.mpr high)] at hj
        exact valid hj
      let r:=S4.radix d
      have pos : 0<r := by dsimp [r,S4.radix];split <;> decide
      have size : j<r*S4.rowCount d := by simpa [sourceCount,low,r] using hj
      have par : j/r<S4.rowCount d := (Nat.div_lt_iff_lt_mul pos).mpr (Nat.mul_comm .. ▸ size)
      have where_ := row_slot d (j/r) (j%r) (Nat.mod_lt j pos)
      change nodeAddress d (r*(j/r)+j%r)=_ at where_
      rw [Nat.div_add_mod] at where_
      have a:=agree.missing d (j/r) (j%r) low (by unfold levelCount;rw [Nat.min_eq_left (by omega),←S4.row_width ⟨d,low⟩];exact par)
        (Nat.mod_lt j pos) (by change levelCount d≤r*(j/r)+j%r;rw [Nat.div_add_mod];omega)
      change _=Late.node tree d (r*(j/r)+j%r) at a
      rw [Nat.div_add_mod] at a;rw [where_];exact a
  salts i := (fixed_in td p _ _ (salt_ok i).1 (salt_ok i).2.1).trans (agree.salts i)

end CommitGolfCandidate.S5Machine.Open
