import Out.Registers
import Out.Interface
import Out.Translation
import Out.InstrsUser

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

def decode (v__0 : (BitVec 32)) : (Option ast) :=
  if ((((Sail.BitVec.extractLsb v__0 29 24) == (0b111000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
             v__0 21 21) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb v__0 11 10) == (0b10#2 : (BitVec 2))))) : Bool)
  then
    (let S := (BitVec.access v__0 12)
    let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
    let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
    let option_v : (BitVec 3) := (Sail.BitVec.extractLsb v__0 15 13)
    let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
    let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
    let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
    let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
    (decodeLoadStoreRegister size opc Rm option_v S Rn Rt))
  else
    (if (((Sail.BitVec.extractLsb v__0 29 24) == (0b111001#6 : (BitVec 6))) : Bool)
    then
      (let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
      let size : (BitVec 2) := (Sail.BitVec.extractLsb v__0 31 30)
      let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
      let imm12 : (BitVec 12) := (Sail.BitVec.extractLsb v__0 21 10)
      let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
      let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
      (decodeLoadStoreImmediate size opc imm12 Rn Rt))
    else
      (if (((Sail.BitVec.extractLsb v__0 30 24) == (0b1001010#7 : (BitVec 7))) : Bool)
      then
        (let sf := (BitVec.access v__0 31)
        let N := (BitVec.access v__0 21)
        let shift : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
        let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb v__0 15 10)
        let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
        let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
        let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
        (decodeExclusiveOr sf shift N Rm imm6 Rn Rd))
      else
        (if ((((Sail.BitVec.extractLsb v__0 30 21) == (0b0101010000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb
                 v__0 15 5) == (0b00000011111#11 : (BitVec 11)))) : Bool)
        then
          (let sf := (BitVec.access v__0 31)
          let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
          let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
          let d : reg_index := (BitVec.toNatInt Rd)
          let m : reg_index := (BitVec.toNatInt Rm)
          (some (Move (sf, d, (MoveReg m)))))
        else
          (if (((Sail.BitVec.extractLsb v__0 30 23) == (0xA5#8 : (BitVec 8))) : Bool)
          then
            (let sf := (BitVec.access v__0 31)
            let imm16 : (BitVec 16) := (Sail.BitVec.extractLsb v__0 20 5)
            let hw : (BitVec 2) := (Sail.BitVec.extractLsb v__0 22 21)
            let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
            let d : reg_index := (BitVec.toNatInt Rd)
            if (((sf == 0#1) && ((BitVec.access hw 1) == 1#1)) : Bool)
            then none
            else
              (some
                (Move
                  (sf, d, (MoveImm
                    { imm := imm16
                      hw := hw })))))
          else
            (if ((((Sail.BitVec.extractLsb v__0 29 24) == (0b001011#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb
                     v__0 21 21) == (0#1 : (BitVec 1)))) : Bool)
            then
              (let sf := (BitVec.access v__0 31)
              let op := (BitVec.access v__0 30)
              let shift : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
              let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb v__0 15 10)
              let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
              let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
              let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
              (decodeAddSubShift sf op shift imm6 Rm Rn Rd))
            else
              (if (((Sail.BitVec.extractLsb v__0 29 23) == (0b0100010#7 : (BitVec 7))) : Bool)
              then
                (let sf := (BitVec.access v__0 31)
                let op := (BitVec.access v__0 30)
                let sh : (BitVec 1) := (Sail.BitVec.extractLsb v__0 22 22)
                let imm12 : (BitVec 12) := (Sail.BitVec.extractLsb v__0 21 10)
                let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
                let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                (decodeAddSubImm sf op sh imm12 Rn Rd))
              else
                (if ((((Sail.BitVec.extractLsb v__0 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
                         v__0 7 0) == (0xBF#8 : (BitVec 8)))) : Bool)
                then
                  (let CRm : (BitVec 4) := (Sail.BitVec.extractLsb v__0 11 8)
                  (decodeDataBarrier CRm false))
                else
                  (if ((((Sail.BitVec.extractLsb v__0 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
                           v__0 7 0) == (0x9F#8 : (BitVec 8)))) : Bool)
                  then
                    (let CRm : (BitVec 4) := (Sail.BitVec.extractLsb v__0 11 8)
                    (decodeDataBarrier CRm true))
                  else
                    (if ((((Sail.BitVec.extractLsb v__0 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
                             v__0 7 0) == (0xDF#8 : (BitVec 8)))) : Bool)
                    then (some (InstructionSynchronizationBarrier ()))
                    else
                      (if (((Sail.BitVec.extractLsb v__0 30 24) == (0b0110100#7 : (BitVec 7))) : Bool)
                      then
                        (let sf := (BitVec.access v__0 31)
                        let imm19 : (BitVec 19) := (Sail.BitVec.extractLsb v__0 23 5)
                        let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
                        (decodeCompareAndBranch sf imm19 Rt))
                      else none))))))))))

def fetch_and_execute (_ : Unit) : SailM Unit := SailME.run do
  let accdesc := (create_iFetchAccessDescriptor ())
  let addr ← (( do
    match (translate_address (← readReg _PC) accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let machineCode ← do (iFetch addr accdesc)
  let instr := (decode machineCode)
  match instr with
  | .some instr => (execute instr)
  | none => assert false "Unsupported Encoding"

