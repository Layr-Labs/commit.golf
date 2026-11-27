import CommitGolfCandidate.RungAProgram
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (NRegs Agree number)
open S4.Machine (W indexBase proofBase valueBase)
open Late (levelCount nodeAddress rowAddress)
def HeadFacts (k r i h : Nat) :=
  let v:=beforeHead k r i h
  okList v (headOps h) ∧ Includes (stageRegs k r (i/24) h) (finalRegs v (headOps h))
private theorem head0 (k r i : Nat) (bk:k≤16777216) (bi:i<16777216) : HeadFacts k r i 0:=by
  constructor
  · simp [HeadFacts,leafHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] <;> omega
  · intro reg x e;cases reg <;> simp [HeadFacts,leafHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] at e ⊢ <;> omega
private theorem head1 (k r i : Nat) (bk:k≤16777216) (bi:i<16777216) : HeadFacts k r i 1:=by
  constructor
  · simp [HeadFacts,oneHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] <;> omega
  · intro reg x e;cases reg <;> simp [HeadFacts,oneHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] at e ⊢ <;> omega
private theorem head2 (k r i : Nat) (bk:k≤16777216) (bi:i<16777216) : HeadFacts k r i 2:=by
  constructor
  · simp [HeadFacts,twoHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] <;> omega
  · intro reg x e;cases reg <;> simp [HeadFacts,twoHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] at e ⊢ <;> omega
private theorem head3 (k r i : Nat) (bk:k≤16777216) (bi:i<16777216) : HeadFacts k r i 3:=by
  constructor
  · simp [HeadFacts,threeHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] <;> omega
  · intro reg x e;cases reg <;> simp [HeadFacts,threeHeadOps,okList,Op.ok,Op.inputs,Op.dst,Op.put,Op.val,finalRegs,number, baseRegs,zeroRegs,abi,finishRegs,loaded,stageRegs,headOps,headPC,baseIndex,sizeAt,slots,depth,leaves,beforeHead, tdAddress,indexBase,proofBase,valueBase,Late.rowBase,Late.nodeAddress,Late.levelOffset,Late.rowAddress,Late.levelCount,Late.gapOffset,S4.layerOffset,S4.rowCount,S4.radix,S4.width,S4.span,LENGTH,LOG_LENGTH] at e ⊢ <;> omega
theorem headFacts (k r i h : Nat) (bk:k≤16777216) (bi:i<16777216) (bh:h<4) : HeadFacts k r i h:=by
  interval_cases h
  · exact head0 _ _ _ bk bi
  · exact head1 _ _ _ bk bi
  · exact head2 _ _ _ bk bi
  · exact head3 _ _ _ bk bi
end CommitGolfCandidate.RungA
