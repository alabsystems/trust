/- SPDX-License-Identifier: BSD-3-Clause
Actual pinned ASLRef producer packets, matched to fixture source/reference receipts.
No proprietary Arm data; wrong goals are closed independent-kernel controls.
-/
import Asl1.Wire
namespace Asl1.WireFixtures
open Asl1.Wire Asl1.Arithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def packetZero : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

def sourceZero : List Nat := [115,99,97,108,97,114]

def typedZero : List Nat := [115,99,97,108,97,114]

def Zero : Prop := evaluate sourceZero typedZero (.bits 64) packetZero = .ok (some (.bits 64 (BitVec.ofNat 64 0)))

def packetEight : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,64,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]

def sourceEight : List Nat := [115,99,97,108,97,114]

def typedEight : List Nat := [115,99,97,108,97,114]

def Eight : Prop := evaluate sourceEight typedEight (.bits 64) packetEight = .ok (some (.bits 64 (BitVec.ofNat 64 8)))

def packetMax : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,64,255,255,255,255,255,255,255,255,0,0,0,0,0,0,0,0,0,0]

def sourceMax : List Nat := [115,99,97,108,97,114]

def typedMax : List Nat := [115,99,97,108,97,114]

def Max : Prop := evaluate sourceMax typedMax (.bits 64) packetMax = .ok (some (.bits 64 (BitVec.ofNat 64 18446744073709551615)))

def packetFrameOffset : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,11,115,116,97,99,107,83,99,97,108,97,114,11,115,116,97,99,107,83,99,97,108,97,114,1,64,3,0,3,1,1,64,0,16,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0]

def sourceFrameOffset : List Nat := [115,116,97,99,107,83,99,97,108,97,114]

def typedFrameOffset : List Nat := [115,116,97,99,107,83,99,97,108,97,114]

def FrameOffset : Prop := evaluate sourceFrameOffset typedFrameOffset (.bits 64) packetFrameOffset = .ok (some (.bits 64 (BitVec.ofNat 64 4096)))

def packetRenamed : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,13,114,101,110,97,109,101,100,83,99,97,108,97,114,13,114,101,110,97,109,101,100,83,99,97,108,97,114,1,64,3,0,1,64,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]

def sourceRenamed : List Nat := [114,101,110,97,109,101,100,83,99,97,108,97,114]

def typedRenamed : List Nat := [114,101,110,97,109,101,100,83,99,97,108,97,114]

def Renamed : Prop := evaluate sourceRenamed typedRenamed (.bits 64) packetRenamed = .ok (some (.bits 64 (BitVec.ofNat 64 8)))

def packetInteger : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,13,105,110,116,101,103,101,114,83,99,97,108,97,114,13,105,110,116,101,103,101,114,83,99,97,108,97,114,0,3,1,3,0,0,0,40,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0]

def sourceInteger : List Nat := [105,110,116,101,103,101,114,83,99,97,108,97,114]

def typedInteger : List Nat := [105,110,116,101,103,101,114,83,99,97,108,97,114]

def Integer : Prop := evaluate sourceInteger typedInteger .int packetInteger = .ok (some (.int (41)))

def badPin : List Nat := [65,83,76,49,1,103,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,64,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]

def trailing : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,64,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0]

def truncated : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,64,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0]

def unknownOperator : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,2,1,64,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]

def wrongWidth : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,63,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]

def noncanonicalBits : List Nat := [65,83,76,49,1,102,102,97,100,50,54,57,50,99,52,53,56,48,53,51,56,101,56,100,98,55,98,102,54,54,51,49,97,97,56,56,54,101,100,102,99,55,52,50,51,6,115,99,97,108,97,114,6,115,99,97,108,97,114,1,64,3,0,1,1,2,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]

def RejectbadPin : Prop := checked sourceEight typedEight (.bits 64) badPin = .error .pin

def Rejecttrailing : Prop := checked sourceEight typedEight (.bits 64) trailing = .error .trailing

def Rejecttruncated : Prop := checked sourceEight typedEight (.bits 64) truncated = .error .truncated

def RejectunknownOperator : Prop := checked sourceEight typedEight (.bits 64) unknownOperator = .error .expression

def RejectwrongWidth : Prop := checked sourceEight typedEight (.bits 64) wrongWidth = .error .illTyped

def RejectnoncanonicalBits : Prop := checked sourceEight typedEight (.bits 64) noncanonicalBits = .error .importRejected

def RejectName : Prop := checked [120] typedEight (.bits 64) packetEight = .error .expectedName

def RejectType : Prop := checked sourceEight typedEight (.bits 63) packetEight = .error .expectedType

def RejectNonByte : Prop := checked sourceEight typedEight (.bits 64) [300] = .error .invalidByte

def WrongLiteral : Prop := evaluate sourceEight typedEight (.bits 64) packetEight = .ok (some (.bits 64 (BitVec.ofNat 64 9)))

def WrongName : Prop := evaluate [120] typedEight (.bits 64) packetEight = .ok (some (.bits 64 (BitVec.ofNat 64 8)))

def WrongType : Prop := evaluate sourceEight typedEight (.bits 63) packetEight = .ok (some (.bits 63 (BitVec.ofNat 63 8)))

def WrongOperator : Prop := evaluate sourceFrameOffset typedFrameOffset (.bits 64) packetFrameOffset = .ok (some (.bits 64 (BitVec.ofNat 64 4128)))

theorem zero : Zero := by rfl
theorem eight : Eight := by rfl
theorem max : Max := by rfl
theorem frame_offset : FrameOffset := by rfl
theorem renamed : Renamed := by rfl
theorem integer : Integer := by rfl
theorem reject_badPin : RejectbadPin := by rfl
theorem reject_trailing : Rejecttrailing := by rfl
theorem reject_truncated : Rejecttruncated := by rfl
theorem reject_unknownOperator : RejectunknownOperator := by rfl
theorem reject_wrongWidth : RejectwrongWidth := by rfl
theorem reject_noncanonicalBits : RejectnoncanonicalBits := by rfl
theorem reject_name : RejectName := by rfl
theorem reject_type : RejectType := by rfl
theorem reject_nonbyte : RejectNonByte := by rfl
end Asl1.WireFixtures
