import CommitGolfCandidate.S4Siblings
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)

theorem Matches.pair {c : Code} {pc : Nat} {a b : List Instr} (left : Matches c pc a)
    (right : Matches c (pc+a.length) b) : Matches c pc (a++b):=by
  intro j bj;by_cases inLeft : j<a.length
  · rw [List.getElem_append_left inLeft];exact left j inLeft
  · have rem : j-a.length<b.length:=by rw [List.length_append] at bj;omega
    rw [List.getElem_append_right (by omega),show pc+j=pc+a.length+(j-a.length) by omega];exact right _ rem

private theorem peerArg (h j : Nat) (v : Digest) (a b : Peers) (first : a.1=b.1) (second : h=0 → a.2=b.2) :
    payload (lane h j) v a=payload (lane h j) v b := by
  by_cases bottom : h=0
  · rw [show a=b from Prod.ext first (second bottom)]
  · unfold lane;rw [if_neg bottom];split <;> simp only [payload,first]

abbrev pathKeep (r : Reg) := r∉[Reg.x1,.x6,.x10,.x12,.x14,.x15,.x18,.x20]
structure NodeResult (o : Oracle) (s t : MachineState) (b : Bool) (h j src pc : Nat) : Prop where
  run : CheckRuns o s t (nodeCode b h).length 1
  next : t.pc=pcAt (pc+(nodeCode b h).length)
  idx : t.getReg .x20=W (j/radix h)
  nextProof : t.getReg .x18=W (src+nodeLength b h+otherSize h)
  keep : ∀ reg,pathKeep reg → t.getReg reg=s.getReg reg
  frame : SameOutside s t 256 352
  digest : readBuffer t 256 32=retained .byte (h+1) (o.compression
    (payload (lane h j) (readBuffer s 256 32) (peersBefore s src (nodeLength b h) h)))

set_option maxRecDepth 6000 in
private theorem offsets : ∀ b : Bool,∀ h : Fin 24,
    blockWord (nodeParts b h) 1=(loadCode 352 (nodeLength b h)).length ∧
    blockWord (nodeParts b h) 2=siblingsCost b h ∧
    blockWord (nodeParts b h) 3=siblingsCost b h+fillSize (decide (h.val=0)) := by decide

theorem nodeRun (o : Oracle) (s : MachineState) (b : Bool) (h j src pc : Nat) (bh : h<pathLevels b)
    (site : s.pc=pcAt pc) (room : pc+(nodeCode b h).length≤Code.check.count) (code : Matches .check pc (nodeCode b h))
    (idx : s.getReg .x20=W j) (small : j<2^64) (cursor : s.getReg .x18=W src)
    (low : 32768≤src) (endOf : src+nodeLength b h+otherSize h≤MEMORY_BYTES)
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96) (three : s.getReg .x23=3) :
    ∃ t,NodeResult o s t b h j src pc := by
  let start:=pc+siblingsCost b h
  let mid:=start+fillSize (decide (h=0))
  let cut:=projected (h+1)
  have costs : (nodeCode b h).length=siblingsCost b h+fillSize (decide (h=0))+(2+callSteps cut):=(nodeSize b h bh).2.2.1
  rw [costs] at room
  have enc:=segment pc (nodeParts b h) code
  have sizeB : (extraLoad h).length=(if h=0 then fieldSteps 32 else 0):=by unfold extraLoad;split <;> first | apply codeLength | rfl
  have num (k : Nat) (hi : k<4) : k<(nodeParts b h).length:=hi
  have lim : h<24:=by unfold pathLevels at bh;split at bh <;> omega
  obtain ⟨one,two,threeOff⟩:=offsets b ⟨h,lim⟩
  have secondary:=enc 1 (num 1 (by decide));rw [show blockWord (nodeParts b h) 1=_ from one] at secondary
  have first : Matches .check pc (siblingCode b h):=Matches.pair (enc 0 (num 0 (by decide))) secondary
  have loc2 : pc+blockWord (nodeParts b h) 2=start :=congrArg (pc+·) two
  have loc3 : pc+blockWord (nodeParts b h) 3=mid:=(congrArg (pc+·) threeOff).trans (Nat.add_assoc ..).symm
  obtain ⟨u,rd⟩:=siblingsRun s pc src h b bh site (by omega) first cursor low endOf
  have p:=enc 2 (num 2 (by decide));rw [loc2] at p
  obtain ⟨v,fill⟩:=fill o u start h j rd.pc (by dsimp only [start];omega) p
    ((rd.keep _ (by decide)).trans idx) small ((rd.keep _ (by decide)).trans three)
  have final:=enc 3 (num 3 (by decide));rw [loc3] at final
  have k (r : Reg) (hh : pathKeep r) : v.getReg r=s.getReg r:=by
    have inFill : untouchedFill r:=by simp only [pathKeep,untouchedFill,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢;tauto
    have inRead : siblingKeep r:=by simp only [pathKeep,siblingKeep,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh ⊢;tauto
    exact (fill.keep r inFill).trans (rd.keep r inRead)
  have res:=compressRun o v mid .x0 512 512 256 cut (by dsimp only [mid,start];omega) fill.pc final
    ((k _ (by decide)).trans mode) ((k _ (by decide)).trans kind) ((k _ (by decide)).trans len)
    rfl rfl (by exact ⟨by decide,by decide⟩) (by exact ⟨by decide,by decide⟩)
  refine ⟨_,⟨?_,?_,(res.keep _ (by decide) (by decide)).trans fill.idx,
    (res.keep _ (by decide) (by decide)).trans ((fill.keep _ (by decide)).trans rd.cursor),?_,?_,?_⟩⟩
  · rw [costs];exact ((ofRuns o rd.run).trans fill.run).trans res.run
  · apply res.pc.trans;rw [costs];exact congrArg pcAt (by dsimp [mid,start];omega)
  · intro r hr
    have exclude : r≠.x10 ∧ r≠.x12:=by simp only [pathKeep,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr;tauto
    exact (res.keep _ exclude.1 exclude.2).trans (k r hr)
  · exact bothScratch (bothScratch (protectedBytes rd.outside (by decide) (by decide))
      (protectedBytes fill.outside (by decide) (by decide))) (protectedBytes res.outside (by decide) (by decide))
  · rw [res.value,show trim cut (o.compression (readBuffer v 512 96))=_ from trimIsRetained (h+1) _,fill.row,rd.outside.read (b:=256) (m:=32) (by decide) (Or.inl (by decide))]
    apply congrArg (fun x=>retained .byte (h+1) (o.compression x));exact peerArg h j _ _ _ rd.a rd.b
end CommitGolfCandidate.S4.Machine
