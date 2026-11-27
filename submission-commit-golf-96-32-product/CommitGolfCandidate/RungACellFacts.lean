import CommitGolfCandidate.RungAProgram
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (NRegs Agree number)
open S4.Machine (W indexBase proofBase valueBase)
open Late (levelCount nodeAddress rowAddress)
def CellFacts (k r g h n : Nat) : Prop :=
  let v:=stageRegs k r g h
  let a:=finalRegs v (testOps h n)
  let t:=finalRegs a (pointers h n)
  okList v (testOps h n) ∧ Includes v a ∧ a (testReg h)=some (baseIndex g h+n) ∧ a (limReg h)=some (levelCount h) ∧
    okList a (pointers h n) ∧ Includes v t ∧ t .x10=some (inputAddr h (baseIndex g h+n)) ∧ t .x12=some (nodeAddress h (baseIndex g h+n))
private theorem cell0 (k r g n : Nat) (bg:g≤699050) (bn:n<sizeAt 0) : CellFacts k r g 0 n:=by
  by_cases off : originOff n<1024
  all_goals
    have bo:=off;try unfold originOff at bo
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | (intro reg x e;cases reg <;> simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at e bn ⊢ <;> omega) | (simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at bn ⊢ <;> omega)
private theorem cell1 (k r g n : Nat) (bg:g≤699050) (bn:n<sizeAt 1) : CellFacts k r g 1 n:=by
  by_cases off : originOff n<1024
  all_goals
    have bo:=off;try unfold originOff at bo
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | (intro reg x e;cases reg <;> simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at e bn ⊢ <;> omega) | (simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at bn ⊢ <;> omega)
private theorem cell2 (k r g n : Nat) (bg:g≤699050) (bn:n<sizeAt 2) : CellFacts k r g 2 n:=by
  by_cases off : originOff n<1024
  all_goals
    have bo:=off;try unfold originOff at bo
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | (intro reg x e;cases reg <;> simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at e bn ⊢ <;> omega) | (simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at bn ⊢ <;> omega)
private theorem cell3 (k r g n : Nat) (bg:g≤699050) (bn:n<sizeAt 3) : CellFacts k r g 3 n:=by
  by_cases off : originOff n<1024
  all_goals
    have bo:=off;try unfold originOff at bo
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals first | (intro reg x e;cases reg <;> simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at e bn ⊢ <;> omega) | (simp [off,bo,CellFacts,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH, testOps,testReg,limReg,pointers,originOff,inputAddr,finalRowAddress] at bn ⊢ <;> omega)
theorem cellFacts (k r g h n : Nat) (bg:g≤699050) (bh:h<4) (bn:n<sizeAt h) : CellFacts k r g h n:=by
  interval_cases h
  · exact cell0 _ _ _ _ bg bn
  · exact cell1 _ _ _ _ bg bn
  · exact cell2 _ _ _ _ bg bn
  · exact cell3 _ _ _ _ bg bn
end CommitGolfCandidate.RungA
