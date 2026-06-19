import Out.Flow
import Out.Registers
import Out.Interface
import Out.Translation

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

def decodeLoadStoreRegister (size : (BitVec 2)) (opc : (BitVec 2)) (Rm : (BitVec 5)) (option_v : (BitVec 3)) (S : (BitVec 1)) (Rn : (BitVec 5)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if (((option_v != 0b011#3) || (S == 1#1)) : Bool)
  then none
  else
    (if ((opc == 0b01#2) : Bool)
    then (some (Load ((BitVec.toNatInt size), t, n, (OperandReg m))))
    else
      (if ((opc == 0b00#2) : Bool)
      then (some (Store ((BitVec.toNatInt size), t, n, (OperandReg m))))
      else none))

def decodeLoadStoreImmediate (size : (BitVec 2)) (opc : (BitVec 2)) (imm12 : (BitVec 12)) (Rn : (BitVec 5)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let n : reg_index := (BitVec.toNatInt Rn)
  if ((opc == 0b01#2) : Bool)
  then (some (Load ((BitVec.toNatInt size), t, n, (OperandImm imm12))))
  else
    (if ((opc == 0b00#2) : Bool)
    then (some (Store ((BitVec.toNatInt size), t, n, (OperandImm imm12))))
    else none)

def decodeExclusiveOr (sf : (BitVec 1)) (shift : (BitVec 2)) (N : (BitVec 1)) (Rm : (BitVec 5)) (imm6 : (BitVec 6)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : (Option ast) :=
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if ((imm6 != 0b000000#6) : Bool)
  then none
  else (some (ExclusiveOr (sf, d, n, m)))

def decodeAddSubShift (sf : (BitVec 1)) (op : (BitVec 1)) (shift : (BitVec 2)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : (Option ast) :=
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if ((imm6 != 0b000000#6) : Bool)
  then none
  else
    (if ((op == 0#1) : Bool)
    then (some (Add (sf, d, n, (OperandReg m))))
    else (some (Sub (sf, d, n, (OperandReg m)))))

def decodeAddSubImm (sf : (BitVec 1)) (op : (BitVec 1)) (sh : (BitVec 1)) (imm12 : (BitVec 12)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : (Option ast) :=
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  if ((sh != 0#1) : Bool)
  then none
  else
    (if ((op == 0#1) : Bool)
    then (some (Add (sf, d, n, (OperandImm imm12))))
    else (some (Sub (sf, d, n, (OperandImm imm12)))))

/-- Type quantifiers: k_ex15099_ : Bool -/
def decodeDataBarrier (CRm : (BitVec 4)) (is_sync : Bool) : (Option ast) := ExceptM.run do
  let domain ← (( do
    match (Sail.BitVec.extractLsb CRm 3 2) with
    | 0b11 => (pure MBReqDomain_FullSystem)
    | 0b10 => (pure MBReqDomain_InnerShareable)
    | 0b01 => (pure MBReqDomain_Nonshareable)
    | 0b00 => (pure MBReqDomain_OuterShareable)
    | _ => throw (none : (Option ast)) ) : ExceptM (Option ast) MBReqDomain )
  let types ← (( do
    match (Sail.BitVec.extractLsb CRm 1 0) with
    | 0b01 => (pure MBReqTypes_Reads)
    | 0b10 => (pure MBReqTypes_Writes)
    | 0b11 => (pure MBReqTypes_All)
    | _ => throw (none : (Option ast)) ) : ExceptM (Option ast) MBReqTypes )
  if (is_sync : Bool)
  then (pure (some (DataSynchronizationBarrier (domain, types))))
  else (pure (some (DataMemoryBarrier (domain, types))))

def decodeCompareAndBranch (sf : (BitVec 1)) (imm19 : (BitVec 19)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let offset : (BitVec 64) := (Sail.BitVec.signExtend (imm19 +++ 0b00#2) 64)
  (some (CompareAndBranch (sf, t, offset)))

/-- Type quantifiers: n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_Sub (sf : (BitVec 1)) (d : Nat) (n : Nat) (op : operand) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let op1 ← do (rXS n size)
  let op2 ← (( do
    match op with
    | .OperandReg m => (rXS m size)
    | .OperandImm imm12 => (pure (Sail.BitVec.zeroExtend imm12 size)) ) : SailM (BitVec size) )
  (wXS d size (op1 + (BitVec.addInt (Complement.complement op2) 1)))

/-- Type quantifiers: n : Nat, t : Nat, size : Nat, 0 ≤ size ∧ size ≤ 3, 0 ≤ t ∧ t ≤ 31, 0
  ≤ n ∧ n ≤ 31 -/
def execute_Store (size : Nat) (t : Nat) (n : Nat) (op : operand) : SailM Unit := SailME.run do
  let accdesc := (create_writeAccessDescriptor ())
  let vaddr ← (( do
    match op with
    | .OperandReg m => (pure ((← (rX n)) + (← (rX m))))
    | .OperandImm imm12 => (pure ((← (rX n)) + ((Sail.BitVec.zeroExtend imm12 64) <<< size))) ) :
    SailME Unit (BitVec 64) )
  let addr ← (( do
    match (translate_address vaddr accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let _ : Unit := (wMem_Addr addr)
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wMem (2 ^i size) addr (Sail.BitVec.extractLsb (← (rX t)) ((8 *i (2 ^i size)) -i 1) 0) accdesc)

/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_Move (sf : (BitVec 1)) (d : Nat) (op : move_operand) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  match op with
  | .MoveReg m => (wXS d size (← (rXS m size)))
  | .MoveImm data =>
    (do
      let res : (BitVec 64) :=
        ((Sail.BitVec.zeroExtend data.imm 64) <<< (16 *i (BitVec.toNatInt data.hw)))
      (wXS d size (Sail.BitVec.extractLsb res (size -i 1) 0)))

/-- Type quantifiers: n : Nat, t : Nat, size : Nat, 0 ≤ size ∧ size ≤ 3, 0 ≤ t ∧ t ≤ 31, 0
  ≤ n ∧ n ≤ 31 -/
def execute_Load (size : Nat) (t : Nat) (n : Nat) (op : operand) : SailM Unit := SailME.run do
  let accdesc := (create_readAccessDescriptor ())
  let vaddr ← (( do
    match op with
    | .OperandReg m => (pure ((← (rX n)) + (← (rX m))))
    | .OperandImm imm12 => (pure ((← (rX n)) + ((Sail.BitVec.zeroExtend imm12 64) <<< size))) ) :
    SailME Unit (BitVec 64) )
  let addr ← (( do
    match (translate_address vaddr accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (wX t (Sail.BitVec.zeroExtend (← (rMem (2 ^i size) addr accdesc)) 64))

def execute_InstructionSynchronizationBarrier (_ : Unit) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (instructionSynchronizationBarrier ())

/-- Type quantifiers: m : Nat, n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_ExclusiveOr (sf : (BitVec 1)) (d : Nat) (n : Nat) (m : Nat) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let operand1 ← do (rXS n size)
  let operand2 ← do (rXS m size)
  (wXS d size (operand1 ^^^ operand2))

def execute_DataSynchronizationBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (dataSynchronizationBarrer domain types)

def execute_DataMemoryBarrier (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (dataMemoryBarrier domain types)

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_CompareAndBranch (sf : (BitVec 1)) (t : Nat) (offset : (BitVec 64)) : SailM Unit := do
  let operand ← (( do
    if ((sf == 1#1) : Bool)
    then (rX t)
    else (pure (Sail.BitVec.zeroExtend (← (rW t)) 64)) ) : SailM (BitVec 64) )
  if ((operand == 0x0000000000000000#64) : Bool)
  then
    (do
      let base ← do (rPC ())
      let addr := (base + offset)
      (wPC addr))
  else writeReg _PC (BitVec.addInt (← readReg _PC) 4)

/-- Type quantifiers: n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31 -/
def execute_Add (sf : (BitVec 1)) (d : Nat) (n : Nat) (op : operand) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let size :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let op1 ← do (rXS n size)
  let op2 ← (( do
    match op with
    | .OperandReg m => (rXS m size)
    | .OperandImm imm12 => (pure (Sail.BitVec.zeroExtend imm12 size)) ) : SailM (BitVec size) )
  (wXS d size (op1 + op2))

def execute (merge_var : ast) : SailM Unit := do
  match merge_var with
  | .Load (size, t, n, op) => (execute_Load size t n op)
  | .Store (size, t, n, op) => (execute_Store size t n op)
  | .ExclusiveOr (sf, d, n, m) => (execute_ExclusiveOr sf d n m)
  | .Move (sf, d, op) => (execute_Move sf d op)
  | .Add (sf, d, n, op) => (execute_Add sf d n op)
  | .Sub (sf, d, n, op) => (execute_Sub sf d n op)
  | .DataMemoryBarrier (domain, types) => (execute_DataMemoryBarrier domain types)
  | .DataSynchronizationBarrier (domain, types) => (execute_DataSynchronizationBarrier domain types)
  | .InstructionSynchronizationBarrier arg0 => (execute_InstructionSynchronizationBarrier arg0)
  | .CompareAndBranch (sf, t, offset) => (execute_CompareAndBranch sf t offset)

