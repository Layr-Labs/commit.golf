import CommitGolfCandidate.S5LeafIteration
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem add_cursor (base pos n : Nat) :
    (BitVec.ofNat 64 (base+pos)+2048)+BitVec.ofNat 64 n=BitVec.ofNat 64 (base+(pos+n))+2048 := by
  have reorder (a b c : Word) : (a+b)+c=(a+c)+b := by rw [BitVec.add_assoc,BitVec.add_comm b c,←BitVec.add_assoc]
  rw [reorder,←BitVec.ofNat_add,show base+pos+n=base+(pos+n) by omega]

theorem after_regs (H : Compression) (s : MachineState) (k : Nat) (inside : k<LENGTH) (a : AtLeaf s k) :
    AtLeaf (afterLeaf H s k) (k+1) := by
  let i:=slotIndex k
  let t:=afterHashes H s k
  let u:=afterUpdates H s k
  have post (r : Reg) : (afterLeaf H s k).getReg r=u.getReg r := by unfold afterLeaf;split <;> rfl
  have old (r : Reg) (h10 : Reg.x10≠r) (h12 : Reg.x12≠r) : t.getReg r=s.getReg r := final_keeps H s _ _ r h10 h12
  have same (r : Reg) (h10 : Reg.x10≠r) (h12 : Reg.x12≠r) (a : Reg.x21≠r) (b : Reg.x22≠r) (c : Reg.x23≠r) (d : Reg.x20≠r) :
      (afterLeaf H s k).getReg r=s.getReg r := (post r).trans ((update_keeps t i r a b c d).trans (old r h10 h12))
  have ups:=update_regs t i
  have moved:=cursor_step k
  constructor
  · by_cases endTile : k%256=255
    · have next : slotIndex (k+1)=0 := Fin.ext (by change (k+1)%256=0;omega)
      unfold afterLeaf;rw [if_pos endTile];change pcAt (if k+1<LENGTH then 4124 else 7224)=_
      rw [next];rfl
    · have more : k+1<LENGTH := by change k<16777216 at inside;change k+1<16777216;omega
      unfold afterLeaf;rw [if_neg endTile,update_pc H a inside,if_pos more]
      let j : Fin 255:=⟨k%256,by omega⟩
      have next : slotIndex (k+1)=⟨j.val+1,by have :=j.isLt;omega⟩ := Fin.ext (by dsimp [slotIndex,j];omega)
      rw [next];exact congrArg pcAt (updates_next j)
  · rw [post,show u.getReg .x21=_ from ups.message,old _ (by decide) (by decide),old _ (by decide) (by decide),a.message,a.strideM,moved.1]
    by_cases e : k%16=15 <;> simpa [i,slotIndex,msgInc,e] using add_cursor 4096 (msgPos k) (msgInc (k%256))
  · rw [post,show u.getReg .x22=_ from ups.rows,old _ (by decide) (by decide),old _ (by decide) (by decide),old _ (by decide) (by decide),
      a.rows,a.strideR,a.strideEnd,moved.2.1]
    by_cases x : k%256%42=41 <;> by_cases e : k%256=255 <;>
      simpa [i,slotIndex,rowInc,x,e] using add_cursor rowBase (rowPos k) (rowInc (k%256))
  · rw [post,show u.getReg .x23=_ from ups.nodes,old _ (by decide) (by decide),old _ (by decide) (by decide),a.nodes,a.strideM,moved.2.2]
    by_cases x : k%128=127 <;>
      simpa [i,slotIndex,nodeInc,x] using add_cursor 4294975488 (nodePos k) (nodeInc (k%256))
  · exact (post _).trans (updated_count H a inside)
  all_goals first
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.strideM
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.strideR
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.strideEnd
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.base
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.root
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.scratch
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.selector
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.len
    | exact (same _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.kind

end CommitGolfCandidate.S5Machine
