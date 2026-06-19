import Out.Flow

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ArchSem

namespace Out.Functions

open option
open operand
open move_operand
open ast
open VARange
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open Shareability
open SecurityState
open Register
open Regime
open PASpace
open PARTIDspaceType
open MemType
open MemTagType
open MemAtomicOp
open MBReqTypes
open MBReqDomain
open GPCF
open Fault
open ErrorState
open DeviceType
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open Barrier
open AccessType

def undefined_move_imm_data (_ : Unit) : SailM move_imm_data := do
  (pure { imm := ← (undefined_bitvector 16)
          hw := ← (undefined_bitvector 2) })

def GPRs : (Vector (RegisterRef (BitVec 64)) 31) :=
  #v[(.Reg R0), (.Reg R1), (.Reg R2), (.Reg R3), (.Reg R4), (.Reg R5), (.Reg R6), (.Reg R7), (.Reg R8), (.Reg R9), (.Reg R10), (.Reg R11), (.Reg R12), (.Reg R13), (.Reg R14), (.Reg R15), (.Reg R16), (.Reg R17), (.Reg R18), (.Reg R19), (.Reg R20), (.Reg R21), (.Reg R22), (.Reg R23), (.Reg R24), (.Reg R25), (.Reg R26), (.Reg R27), (.Reg R28), (.Reg R29), (.Reg R30)]

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def wX (n : Nat) (value : (BitVec 64)) : SailM Unit := do
  if ((n != 31) : Bool)
  then writeRegRef (GetElem?.getElem! GPRs n) value
  else (pure ())

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def rX (n : Nat) : SailM (BitVec 64) := do
  if ((n != 31) : Bool)
  then (reg_deref (GetElem?.getElem! GPRs n))
  else (pure 0x0000000000000000#64)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def wW (n : Nat) (value : (BitVec 32)) : SailM Unit := do
  if ((n != 31) : Bool)
  then writeRegRef (GetElem?.getElem! GPRs n) (Sail.BitVec.zeroExtend value 64)
  else (pure ())

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def rW (n : Nat) : SailM (BitVec 32) := do
  if ((n != 31) : Bool)
  then (pure (Sail.BitVec.extractLsb (← (reg_deref (GetElem?.getElem! GPRs n))) 31 0))
  else (pure 0x00000000#32)

/-- Type quantifiers: n : Nat, size : Nat, size ∈ {32, 64}, 0 ≤ n ∧ n ≤ 31 -/
def rXS (n : Nat) (size : Nat) : SailM (BitVec size) := do
  if ((size == 64) : Bool)
  then (rX n)
  else (rW n)

/-- Type quantifiers: n : Nat, size : Nat, size ∈ {32, 64}, 0 ≤ n ∧ n ≤ 31 -/
def wXS (n : Nat) (size : Nat) (value : (BitVec size)) : SailM Unit := do
  if ((size == 64) : Bool)
  then (wX n value)
  else (wW n value)

def rPC (_ : Unit) : SailM (BitVec 64) := do
  readReg _PC

def wPC (pc : (BitVec 64)) : SailM Unit := do
  writeReg _PC pc

