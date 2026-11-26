import CommitGolfCandidate.S4Inputs
import CommitGolfCandidate.S4Slots
import CommitGolfCandidate.S4Stores
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor TrapdoorAgrees Levels SaltTape Digest slice)
open Machine (W byte wordAt indexBase valueBase proofBase Moved Wrote)

def tdBase:=4294971424
def indices (p : Positions) := p.sort (· ≤ ·)
def ix (xs : List Index) (r : Nat) : Index := xs[r]?.getD ⟨0,by decide⟩
def initial (td : Trapdoor) (p : Positions) := Late.submission.initialState .opening (td,p)

private theorem selected_byte (td : Trapdoor) (p : Positions) (b : InputBuffer) (a : Nat)
    (below : a < 2^64)
    (pick : (Late.submission.inputBuffers .opening (td,p)).find?
      (fun buf => decide (buf.address≤a ∧ a<buf.address+buf.length)) = some b) :
    (initial td p).getByte (BitVec.ofNat 64 a) = b.byteAt (a-b.address) := by
  apply (initial_input_byte Late.submission .opening (td,p) a below).trans
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
    (Late.submission.inputBuffers .opening (td,p)).find? (fun b => decide (b.address≤a ∧ a<b.address+b.length)) =
        some (fixedBuffer tdBase td) := by
  apply firstBuffer
  exact ⟨lo,(fixed_end td).symm ▸ hi⟩

theorem fixed_in (td : Trapdoor) (p : Positions) (a n : Nat) (lo : tdBase≤a) (hi : a+n ≤ indexBase) :
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

theorem index_loaded (td : Trapdoor) (p : Positions) (r : Nat) (hr : r < (indices p).length) :
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

def Sources (td : Trapdoor) (ps : Positions) (s : MachineState) :=
  ∀ q,tdBase≤q → q<valueBase → byte s q=byte (initial td ps) q

theorem Sources.read {td : Trapdoor} {ps : Positions} {s : MachineState} (src : Sources td ps s)
    (a n : Nat) (lo : tdBase≤a) (hi : a+n≤valueBase) :
    readBuffer s a n=readBuffer (initial td ps) a n := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl
  intro j bj;have hj:=Finset.mem_range.mp bj
  exact congrArg (fun b : Byte=>b.toNat*2^(8*j)) (src (a+j) (by omega) (by omega))

theorem Sources.fixed {td : Trapdoor} {ps : Positions} {s : MachineState} (src : Sources td ps s)
    (a n : Nat) (lo : tdBase≤a) (hi : a+n ≤ indexBase) : readBuffer s a n=slice td a n :=
  (src.read a n lo (hi.trans (by decide))).trans (fixed_in td ps a n lo hi)

theorem Sources.moved {td : Trapdoor} {ps : Positions} {s t : MachineState} {a b n : Nat}
    (src : Sources td ps s) (move : Moved s t a b n) (out : proofBase≤b) : Sources td ps t := by
  intro q lo hi;have e : valueBase≤proofBase:=by decide
  exact (move q (by unfold valueBase at hi;omega)).trans ((if_neg (by omega)).trans (src q lo hi))

theorem Sources.mark {td : Trapdoor} {ps : Positions} {s t : MachineState} {a : Nat} {v : Nat→Byte}
    (src : Sources td ps s) (put : Wrote s t a 1 v) (scratch : a+1≤tdBase) : Sources td ps t := by
  intro q lo hi
  exact (put q (by unfold valueBase at hi;omega)).trans ((if_neg (by omega)).trans (src q lo hi))

theorem Sources.sameMem {td : Trapdoor} {ps : Positions} {s t : MachineState} (known : Sources td ps s)
    (e : t.mem=s.mem) : Sources td ps t := by
  intro q l h;simpa only [byte,MachineState.getByte,MachineState.getMem,e] using known q l h

end CommitGolfCandidate.S4.Open
