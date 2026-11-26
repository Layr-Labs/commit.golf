import CommitGolfCandidate.R4bTape
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open S4.Open (Sources targetAddr offsetAt widthAt)
open Machine (W Safe byte proofBase)
def Scratch (s t : MachineState) := ∀ r,r≠.x6 → r≠.x7 → r≠.x20 → t.getReg r=s.getReg r
theorem widths (q : Nat) (bq : q<17) :
    (widthAt true q=24 ∨ widthAt true q=30 ∨ widthAt true q=32) ∧
    (chunkCount q=(widthAt true q+7)/8) ∧ offsetAt true q%2=0 :=
  (show ∀ q : Fin 17,(widthAt true q=24 ∨ widthAt true q=30 ∨ widthAt true q=32) ∧
    chunkCount q=(widthAt true q+7)/8 ∧ offsetAt true q%2=0 by decide) ⟨q,bq⟩

theorem emit (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) (t l q : Nat)
    (bt : t<32) (bl : l<4) (bq : q<17) (s : MachineState) (src : Sources td ps s)
    (address : s.getReg .x12=W (targetAddr (recordIndex ps (4*t+l)) q))
    (output : s.getReg .x19=W (proofBase+2040*t))
    (prior : Cursor (tape td ps) (510*(4*t+l)+offsetAt true q) s) :
    ∃ z,Straight s ((List.range (chunkCount q)).flatMap (outputChunk l q)) z ∧ Protect s z ∧
      Scratch s z ∧ Cursor (tape td ps) (510*(4*t+l)+offsetAt true q+widthAt true q) z := by
  let r:=4*t+l
  let a:=targetAddr (recordIndex ps r) q
  let w:=widthAt true q
  let beginAt:=510*r+offsetAt true q
  have br : r<128:=by dsimp [r];omega
  have ⟨wlen,number,even⟩:=widths q bq
  have size:=offsetMore q bq
  have bounds:=Open.fieldBounds true q (recordIndex ps r) bq
  change Open.tdBase≤a ∧ a+32≤Machine.indexBase ∧ a%8=0 at bounds
  have edge : beginAt+w≤65280:=by dsimp [beginAt,w];omega
  have ind (j : Nat) (bj : j≤chunkCount q) :
      ∃ u,Straight s ((List.range j).flatMap (outputChunk l q)) u ∧ Protect s u ∧ Scratch s u ∧
        Cursor (tape td ps) (beginAt+min (8*j) w) u := by
    induction j with
    | zero=>exact ⟨s,.nil _,Protect.ofMem rfl,fun _ _ _ _=>rfl,by simpa [beginAt,r] using prior⟩
    | succ j ih=>
      obtain ⟨u,pre,frame,regs,cur⟩:=ih (by omega)
      let n:=min 8 (w-8*j)
      let k:=beginAt+8*j
      let o:=fieldOffset l q+8*j
      have h8 : 8*j<w := by dsimp [w];omega
      have nlen : n=6 ∨ n=8:=by dsimp [n,w];omega
      have endBound : k+n≤65280:=by dsimp [k,n];omega
      have evenK : k%2=0:=by dsimp [k,beginAt];omega
      have shortLane : k%8+n<8 → k%8=0:=by omega
      have origin : k=2040*t+o:=by dsimp [o,k,beginAt,fieldOffset,r];omega
      have mod : o%8=k%8:=by omega
      have block : proofBase+2040*t+completed o=proofBase+completed k:=by unfold completed;omega
      have oLim : completed o<2048:=by dsimp [completed,o,fieldOffset,w] at *;omega
      have srcPtr : u.getReg .x12+signExtend12 (imm12 (8*j))=W (a+8*j):=
        smallAddr _ _ _ _ ((regs _ (by decide) (by decide) (by decide)).trans address) (by dsimp [w] at *;omega)
      have dstPtr := (smallAddr u .x19 _ (completed o)
        ((regs _ (by decide) (by decide) (by decide)).trans output) oLim).trans (congrArg W block)
      have ss : Safe (a+8*j) 8:=⟨by change a+8*j+8≤68719476736;unfold Machine.indexBase at bounds;dsimp [w] at *;omega,by omega⟩
      have ds : Safe (proofBase+completed k) 8:=⟨by unfold proofBase completed;change _≤68719476736;omega,by unfold proofBase completed;omega⟩
      have input (b : Nat) (bh : b<n) : extractByte (u.getMem (W (a+8*j))) b=tape td ps (k+b) := by
        have bb : b<8:=by omega
        have field:=tapeSource td ps batch r q br bq u (frame.sources src) (8*j+b) (by dsimp [n,w] at *;omega)
        change byte u (a+(8*j+b))=_ at field
        rw [Machine.byteWord,show 8*((a+(8*j+b))/8)=a+8*j by omega,show (a+(8*j+b))%8=b by omega] at field
        simpa only [k,beginAt,Nat.add_assoc] using field
      obtain ⟨z,copy,saved,tail,stored⟩:=doChunk u (k%8) n (8*j) (completed o) (a+8*j) (proofBase+completed k)
        (Nat.mod_lt _ (by decide)) nlen srcPtr dstPtr ss ds
      rw [Nat.min_eq_left h8.le] at cur
      obtain ⟨next,away⟩:=advanceWord _ k n _ endBound nlen shortLane cur input tail stored
      have bits : outputChunk l q j=chunkOps (k%8) n (8*j) (completed o):=by unfold outputChunk;rw [←mod]
      rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,bits]
      refine ⟨z,pre.append copy,frame.trans away,fun x u v w=>(saved x u v w).trans (regs x u v w),?_⟩
      exact (show k+n=beginAt+min (8*(j+1)) w by dsimp [k,n];omega) ▸ next
  obtain ⟨z,h,f,g,out⟩:=ind (chunkCount q) le_rfl
  exact ⟨z,h,f,g,by rw [Nat.min_eq_right (by dsimp [w];omega)] at out;exact out⟩
end CommitGolfCandidate.R4b
