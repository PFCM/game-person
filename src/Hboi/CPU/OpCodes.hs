{-| There are 256 opcodes, so it's inevitable that somewhere there is going to
be a function with 256 definitions. This is where it lives.

In practice, the opcodes don't all require the same parts of the state. These
are split out into different typeclasses in Hboi.CPU.State and these opcodes are
dispatched to appropriately constrained functions. This means slightly more
boilerplate here and in the State module, but makes testing a lot easier.

When discussing registers, (XX) refers to the memory at the 16 bit value XX.
$XXXX refers to a 16 bit memory address.-}
{-# LANGUAGE FlexibleContexts #-}
module Hboi.CPU.OpCodes where

import           Hboi.CPU.State
import           Hboi.Memory                              ( MonadMem(..) )

import           Control.Monad
import           Control.Monad.Except
import           Data.Bits
import           Data.Word                                ( Word8
                                                          , Word16
                                                          )
import           Data.Int                                 ( Int16
                                                          , Int8
                                                          )
import           Numeric                                  ( showHex )


-- * the main dispatch functions

-- |runs an opcode, updating the state in some way. In general we try and ensure
-- that the functions called from here need a minimum of constraints. It will be
-- common for a lot of takes n $ .... for example, because then the function
-- being called to do the operation does not require the MonadClock constraint
-- and is therefore at least one step easier to test.
op
  :: ( MonadPC m
     , MonadSP m
     , MonadReadReg8 m
     , MonadWriteReg8 m
     , MonadReadReg16 m
     , MonadWriteReg16 m
     , MonadClock m
     , MonadError String m
     , MonadFlags m
     , MonadMem m
     )
  => Word8
  -> m ()
-- NO OP
op 0x00 = incClock 1
-- Prefix to CB instructions
op 0xCB = next >>= cbop
-- Prefix to STOP
op 0x10 = throwError "STOP not implemented"
-- Disable/enable interrupts
op 0xF3 = takes 1 $ setFlag IME False -- di
op 0xFB = takes 1 $ setFlag IME True -- ei
-------------JUMPS-----------------
op 0xC3 = takes 3 $ next16 >>= setPC -- unconditional absolute jump to immediate value
op 0xE9 = takes 1 $ getHL >>= setPC  -- jump to contents of HL
-- some kind of conditional absolute jumpery, takes an extra cycle
-- if it does jump maybe?
-- TODO: double check this, adjust the auto test somehow so they
-- can pass
op 0xC2 = takes 3 . join $ cjump <$> next16 <*> (not <$> getFlag Zero)
op 0xCA = takes 3 . join $ cjump <$> next16 <*> getFlag Zero
op 0xD2 = takes 3 . join $ cjump <$> next16 <*> (not <$> getFlag Carry)
op 0xDA = takes 3 . join $ cjump <$> next16 <*> getFlag Carry
-- relative, add 8 bit signed to PC
op 0x18 = takes 2 $ (add16to8Signed <$> getPC <*> next) >>= setPC
-- relative conditional
-- op 0x20

-- op 0xCD call: push PC on the stack, set PC to immediate 16
-- op ?? conditional call
-- op 0xC9 ret: pop PC from stack
-- op 0xD9 reti: ret and ei
-- rst?
------------LOADS------------------
-- special loads for A
-- op 0x3e -- takes 2, load # into A (what is #??????)
op 0x0A = takes 2 (getBC >>= read8 >>= setA)
op 0x1A = takes 2 (getDE >>= read8 >>= setA)
op 0xFA = takes 4 (next16 >>= read8 >>= setA) -- takes 4, load (nn) into A, where nn is 2 immediates ls byte first
op 0x02 = takes 2 (join $ write8 <$> getBC <*> getA)
op 0x12 = takes 2 (join $ write8 <$> getDE <*> getA)
op 0x77 = takes 2 (join $ write8 <$> getHL <*> getA)
op 0xEA = takes 4 (join $ write8 <$> next16 <*> getA) -- load A into (nn), with nn as above
-- these are loads for IO
op 0xE0 = takes 3 (join $ write8 <$> (add16To8 0xFF00 <$> next) <*> getA) -- load A into $FF00 + n, for one byte immediate n
op 0xF0 = takes 3 (add16To8 0xFF00 <$> next >>= read8 >>= setA)-- load $FF00 + n into A, as above but backwards
-- A <-> (C), again IO but offset in a reg
op 0xE2 = takes 2 (join $ write8 <$> (add16To8 0xFF00 <$> getC) <*> getA) -- takes 2, load A into $FF00 + C
op 0xF2 = takes 2 (add16To8 0xFF00 <$> getC >>= read8 >>= setA) -- load $FF00 + C into A
-- Fancy load and muck around with HL, aka stack 2.0
op 0x3A = takes 2 (getHL >>= read8 >>= setA) >> dec16 getHL setHL -- takes 2, load (HL) into A, decrement HL
op 0x32 = takes 2 (join $ write8 <$> getHL <*> getA) >> dec16 getHL setHL -- load A into (HL), decrement HL
op 0x2A = takes 2 (getHL >>= read8 >>= setA) >> inc16 getHL setHL -- takes 2, load (HL) into A, increment HL
op 0x22 = takes 2 (join $ write8 <$> getHL <*> getA) >> inc16 getHL setHL -- load A into (HL), increment HL
-- 8-bit load immediate into register
op 0x06 = takes 2 (next >>= setB) -- takes 2, load immediate into B
op 0x0E = takes 2 (next >>= setC) -- takes 2, load immediate into C
op 0x16 = takes 2 (next >>= setD) -- takes 2, load immediate into D
op 0x1E = takes 2 (next >>= setE) -- takes 2, load immediate into E
op 0x26 = takes 2 (next >>= setH)-- takes 2, load immediate into H
op 0x2E = takes 2 (next >>= setL) -- takes 2, load immediate into L
op 0x36 = takes 3 (join $ write8 <$> getHL <*> next)
-- 8-bit load register into register
-- into A
op 0x7F = takes 1 $ getA >>= setA -- I wonder if anyone does this ever
op 0x78 = takes 1 $ getB >>= setA
op 0x79 = takes 1 $ getC >>= setA
op 0x7A = takes 1 $ getD >>= setA
op 0x7B = takes 1 $ getE >>= setA
op 0x7C = takes 1 $ getH >>= setA
op 0x7D = takes 1 $ getL >>= setA
op 0x7E = takes 2 (getHL >>= read8 >>= setA)
-- into B
op 0x40 = takes 1 $ getB >>= setB
op 0x41 = takes 1 $ getC >>= setB
op 0x42 = takes 1 $ getD >>= setB
op 0x43 = takes 1 $ getE >>= setB
op 0x44 = takes 1 $ getH >>= setB
op 0x45 = takes 1 $ getL >>= setB
op 0x46 = takes 2 (getHL >>= read8 >>= setB)
op 0x47 = takes 1 $ getA >>= setB
-- into C
op 0x48 = takes 1 $ getB >>= setC
op 0x49 = takes 1 $ getC >>= setC
op 0x4A = takes 1 $ getD >>= setC
op 0x4B = takes 1 $ getE >>= setC
op 0x4C = takes 1 $ getH >>= setC
op 0x4D = takes 1 $ getL >>= setC
op 0x4E = takes 2 (getHL >>= read8 >>= setB)
op 0x4F = takes 1 $ getA >>= setC
-- into D
op 0x50 = takes 1 $ getB >>= setD
op 0x51 = takes 1 $ getC >>= setD
op 0x52 = takes 1 $ getD >>= setD
op 0x53 = takes 1 $ getE >>= setD
op 0x54 = takes 1 $ getH >>= setD
op 0x55 = takes 1 $ getL >>= setD
op 0x56 = takes 2 (getHL >>= read8 >>= setD)
op 0x57 = takes 1 $ getA >>= setD
-- into E
op 0x58 = takes 1 $ getB >>= setE
op 0x59 = takes 1 $ getC >>= setE
op 0x5A = takes 1 $ getD >>= setE
op 0x5B = takes 1 $ getE >>= setE
op 0x5C = takes 1 $ getH >>= setE
op 0x5D = takes 1 $ getL >>= setE
op 0x5E = takes 2 (getHL >>= read8 >>= setE)
op 0x5F = takes 1 $ getA >>= setE
-- into H
op 0x60 = takes 1 $ getB >>= setH
op 0x61 = takes 1 $ getC >>= setH
op 0x62 = takes 1 $ getD >>= setH
op 0x63 = takes 1 $ getE >>= setH
op 0x64 = takes 1 $ getH >>= setH
op 0x65 = takes 1 $ getL >>= setH
op 0x66 = takes 2 (getHL >>= read8 >>= setH)
op 0x67 = takes 1 $ getA >>= setH
-- into L
op 0x68 = takes 1 $ getB >>= setL
op 0x69 = takes 1 $ getC >>= setL
op 0x6A = takes 1 $ getD >>= setL
op 0x6B = takes 1 $ getE >>= setL
op 0x6C = takes 1 $ getH >>= setL
op 0x6D = takes 1 $ getL >>= setL
op 0x6E = takes 2 (getHL >>= read8 >>= setL)
op 0x6F = takes 1 $ getA >>= setL
op 0x70 = takes 2 (join $ write8 <$> getHL <*> getB)
op 0x71 = takes 2 (join $ write8 <$> getHL <*> getC)
op 0x72 = takes 2 (join $ write8 <$> getHL <*> getD)
op 0x73 = takes 2 (join $ write8 <$> getHL <*> getE)
op 0x74 = takes 2 (join $ write8 <$> getHL <*> getH)
op 0x75 = takes 2 (join $ write8 <$> getHL <*> getL)
-- 16 bit immediate loads - gets nn by jumping PC twice
op 0x01 = takes 3 (next16 >>= setBC)
op 0x11 = takes 3 (next16 >>= setDE)
op 0x21 = takes 3 (next16 >>= setHL)
op 0x31 = takes 3 (next16 >>= setSP)
-- Misc. 16 bit loads
op 0xF9 = takes 2 (getHL >>= setSP)
op 0xF8 = takes 3 (add16to8Signed <$> getSP <*> next) >>= setHL -- load SP + n into HL, n IS SIGNED
op 0x08 = takes 5 (join $ write16 <$> getSP <*> next16) -- takes 5, load SP into (nn), two byte nn etc etc
---------STANDARD STACK OPS--------
-- PUSHH
op 0xF5 = takes 4 $ getAF >>= spush -- I suspect this actually happens in the opposite order
op 0xC5 = takes 4 $ getBC >>= spush -- takes 4, load BC into (SP), decrement SP twice
op 0xD5 = takes 4 $ getDE >>= spush -- takes 4, load DE into (SP), decrement SP twice
op 0xE5 = takes 4 $ getHL >>= spush -- takes 4, load HL into (SP), decrement SP twice
-- PPOPPP
op 0xF1 = takes 3 $ spop >>= setAF-- takes 3, load (SP) into AF, increment SP twice (or maybe the other way around)
op 0xC1 = takes 3 $ spop >>= setBC-- takes 3, load (SP) into BC, increment SP twice
op 0xD1 = takes 3 $ spop >>= setDE-- takes 3, load (SP) into DE, increment SP twice
op 0xE1 = takes 3 $ spop >>= setHL-- takes 3, load (SP) into HL, increment SP twice
---------ARITHMETIC----------------
-- 8-bit arithmetic directly on A
-- adds
op 0x87 = takes 1 $ add8 getA getA setA
op 0x80 = takes 1 $ add8 getA getB setA
op 0x81 = takes 1 $ add8 getA getC setA
op 0x82 = takes 1 $ add8 getA getD setA
op 0x83 = takes 1 $ add8 getA getE setA
op 0x84 = takes 1 $ add8 getA getH setA
op 0x85 = takes 1 $ add8 getA getL setA
op 0x86 = takes 2 $ add8 getA (getHL >>= read8) setA -- add (HL) onto A
-- op 0xC6 = A += # ?? what is #???, takes 2 though
-- add + carry
op 0x8F = takes 1 $ adc8 getA getA setA
op 0x88 = takes 1 $ adc8 getA getB setA
op 0x89 = takes 1 $ adc8 getA getC setA
op 0x8A = takes 1 $ adc8 getA getD setA
op 0x8B = takes 1 $ adc8 getA getE setA
op 0x8C = takes 1 $ adc8 getA getH setA
op 0x8D = takes 1 $ adc8 getA getL setA
op 0x8E = takes 2 $ adc8 getA (getHL >>= read8) setA-- add (HL) into A with carry
-- op 0xCE takes 2, add # onto A with carry...
-- subs (subtract _from_ A)
op 0x97 = takes 1 $ sub8 getA getA setA
op 0x90 = takes 1 $ sub8 getA getB setA
op 0x91 = takes 1 $ sub8 getA getC setA
op 0x92 = takes 1 $ sub8 getA getD setA
op 0x93 = takes 1 $ sub8 getA getE setA
op 0x94 = takes 1 $ sub8 getA getH setA
op 0x95 = takes 1 $ sub8 getA getL setA
op 0x96 = takes 2 $ sub8 getA (getHL >>= read8) setA -- subtracts (HL) from A
-- op 0xD6 takes 2, subtracts # from A
-- sbc, subtract with carry
op 0x9F = takes 1 $ sbc8 getA getA setA
op 0x98 = takes 1 $ sbc8 getA getA setA
op 0x99 = takes 1 $ sbc8 getA getA setA
op 0x9A = takes 1 $ sbc8 getA getA setA
op 0x9B = takes 1 $ sbc8 getA getA setA
op 0x9C = takes 1 $ sbc8 getA getA setA
op 0x9D = takes 1 $ sbc8 getA getA setA
op 0x9E = takes 2 $ sbc8 getA (getHL >>= read8) setA -- subtracts (HL) from A with carry
-- op ?? takes ? subtracts # from A ???
-- AND with A
op 0xA7 = takes 1 $ and8 getA getA setA
op 0xA0 = takes 1 $ and8 getA getB setA
op 0xA1 = takes 1 $ and8 getA getC setA
op 0xA2 = takes 1 $ and8 getA getD setA
op 0xA3 = takes 1 $ and8 getA getE setA
op 0xA4 = takes 1 $ and8 getA getH setA
op 0xA5 = takes 1 $ and8 getA getL setA
op 0xA6 = takes 2 $ and8 getA (getHL >>= read8) setA
-- op 0xE6 ands A with #, takes 2
-- OR with A
op 0xB7 = takes 1 $ or8 getA getA setA
op 0xB0 = takes 1 $ or8 getA getB setA
op 0xB1 = takes 1 $ or8 getA getC setA
op 0xB2 = takes 1 $ or8 getA getD setA
op 0xB3 = takes 1 $ or8 getA getE setA
op 0xB4 = takes 1 $ or8 getA getH setA
op 0xB5 = takes 1 $ or8 getA getL setA
op 0xB6 = takes 2 $ or8 getA (getHL >>= read8) setA
-- op 0xF6 ors A with #, takes 2
-- XOR with A
op 0xAF = takes 1 $ xor8 getA getA setA
op 0xA8 = takes 1 $ xor8 getA getB setA
op 0xA9 = takes 1 $ xor8 getA getC setA
op 0xAA = takes 1 $ xor8 getA getD setA
op 0xAB = takes 1 $ xor8 getA getE setA
op 0xAC = takes 1 $ xor8 getA getH setA
op 0xAD = takes 1 $ xor8 getA getL setA
op 0xAE = takes 2 $ xor8 getA (getHL >>= read8) setA
-- op 0xEE xors A with *, I think they mean #, takes 2
-- CP with A, like subtraction but no result, just set the flags
op 0xBF = takes 1 $ sub8 getA getA (\_ -> return ())
op 0xB8 = takes 1 $ sub8 getA getB (\_ -> return ())
op 0xB9 = takes 1 $ sub8 getA getC (\_ -> return ())
op 0xBA = takes 1 $ sub8 getA getD (\_ -> return ())
op 0xBB = takes 1 $ sub8 getA getE (\_ -> return ())
op 0xBC = takes 1 $ sub8 getA getH (\_ -> return ())
op 0xBD = takes 1 $ sub8 getA getL (\_ -> return ())
op 0xBE = takes 2 $ sub8 getA (getHL >>= read8) (\_ -> return ())
-- op 0xFE does this with #, takes 2
-- INC, increment registers, might set the half-carry flag but apparently not
-- the carry flag
op 0x3C = takes 1 $ inc8 getA setA
op 0x04 = takes 1 $ inc8 getB setB
op 0x0C = takes 1 $ inc8 getC setC
op 0x14 = takes 1 $ inc8 getD setD
op 0x1C = takes 1 $ inc8 getE setE
op 0x24 = takes 1 $ inc8 getH setH
op 0x2C = takes 1 $ inc8 getL setL
op 0x34 = takes 3 $ inc8
  (getHL >>= read8)
  (\v -> do
    hl <- getHL
    write8 hl v
  )
-- DEC, decrement a register. Sets half carry, zero etc. Not carry
op 0x3D = takes 1 $ dec8 getA setA
op 0x05 = takes 1 $ dec8 getB setB
op 0x0D = takes 1 $ dec8 getC setC
op 0x15 = takes 1 $ dec8 getD setD
op 0x1D = takes 1 $ dec8 getE setE
op 0x25 = takes 1 $ dec8 getH setH
op 0x2D = takes 1 $ dec8 getL setL
op 0x35 = takes 3 $ dec8
  (getHL >>= read8)
  (\v -> do
    hl <- getHL
    write8 hl v
  )
-- ADD for 16s, sets flags as expected but for more spaced out bits
op 0x09 = takes 2 $ add16 getHL getBC setBC
op 0x19 = takes 2 $ add16 getHL getDE setDE
op 0x29 = takes 2 $ add16 getHL getHL setHL
op 0x39 = takes 2 $ add16 getHL getSP setSP
-- ADD an 8 bit immediate to SP
op 0xE8 = takes 4 $ add16 getSP (fromIntegral <$> next) setSP
-- 16 bit increments
op 0x03 = takes 2 $ inc16 getBC setBC
op 0x13 = takes 2 $ inc16 getDE setDE
op 0x23 = takes 2 $ inc16 getHL setHL
op 0x33 = takes 2 $ inc16 getSP setSP
-- 16 bit decrements
op 0x0B = takes 2 $ dec16 getBC setBC
op 0x1B = takes 2 $ dec16 getDE setDE
op 0x2B = takes 2 $ dec16 getHL setHL
op 0x3B = takes 2 $ dec16 getSP setSP
-- complement the A register, sets N and H
op 0x2F =
  takes 1
    $   setFlag AddSub    True
    >>  setFlag HalfCarry True
    >>  complement
    <$> getA
    >>= setA
-- rotates just on A
op 0x07 = takes 1 $ rlc getA setA
op 0x17 = takes 1 $ rl getA setA
op 0x0F = takes 1 $ rrc getA setA
op 0x1F = takes 1 $ rr getA setA
-- anything else is invalid
op x    = throwError $ "Invalid opcode: " ++ showHex x ""

-- |CB-prefixed ops
cbop
  :: ( MonadPC m
     , MonadSP m
     , MonadReadReg8 m
     , MonadWriteReg8 m
     , MonadReadReg16 m
     , MonadWriteReg16 m
     , MonadClock m
     , MonadError String m
     , MonadFlags m
     , MonadMem m
     )
  => Word8
  -> m ()
-- SWAP upper and lower nibble
cbop 0x37 = takes 2 $ swap getA setA
cbop 0x30 = takes 2 $ swap getB setB
cbop 0x31 = takes 2 $ swap getC setC
cbop 0x32 = takes 2 $ swap getD setD
cbop 0x33 = takes 2 $ swap getE setE
cbop 0x34 = takes 2 $ swap getH setH
cbop 0x35 = takes 2 $ swap getH setH
cbop 0x36 = takes 4 $ swap
  (getHL >>= read8)
  (\v -> do
    hl <- getHL
    write8 hl v
  )
-- rotates
-- RLC, rotate left with carry
cbop 0x07 = takes 2 $ rlc getA setA
cbop 0x00 = takes 2 $ rlc getB setB
cbop 0x01 = takes 2 $ rlc getC setC
cbop 0x02 = takes 2 $ rlc getD setD
cbop 0x03 = takes 2 $ rlc getE setE
cbop 0x04 = takes 2 $ rlc getH setH
cbop 0x05 = takes 2 $ rlc getL setL
cbop 0x06 = takes 4 $ rlc (getHL >>= read8) (\v -> getHL >>= flip write8 v)
-- RL, rotate left without carry (still sets it if necessary)
cbop 0x10 = takes 2 $ rl getB setB
cbop 0x11 = takes 2 $ rl getC setC
cbop 0x12 = takes 2 $ rl getD setD
cbop 0x13 = takes 2 $ rl getE setE
cbop 0x14 = takes 2 $ rl getH setH
cbop 0x15 = takes 2 $ rl getL setL
cbop 0x16 = takes 4 $ rl (getHL >>= read8) (\v -> getHL >>= flip write8 v)
cbop 0x17 = takes 2 $ rl getA setA
-- RRC, rotate right with carry
cbop 0x08 = takes 2 $ rrc getB setB
cbop 0x09 = takes 2 $ rrc getC setC
cbop 0x0A = takes 2 $ rrc getD setD
cbop 0x0B = takes 2 $ rrc getE setE
cbop 0x0C = takes 2 $ rrc getH setH
cbop 0x0D = takes 2 $ rrc getL setL
cbop 0x0E = takes 4 $ rrc (getHL >>= read8) (\v -> getHL >>= flip write8 v)
cbop 0x0F = takes 2 $ rrc getA setA
-- RR, rotate right without carry
cbop 0x18 = takes 2 $ rr getB setB
cbop 0x19 = takes 2 $ rr getC setC
cbop 0x1A = takes 2 $ rr getD setD
cbop 0x1B = takes 2 $ rr getE setE
cbop 0x1C = takes 2 $ rr getH setH
cbop 0x1D = takes 2 $ rr getL setL
cbop 0x1E = takes 4 $ rr (getHL >>= read8) (\v -> getHL >>= flip write8 v)
cbop 0x1F = takes 2 $ rr getA setA
-- SLA, left shift
cbop 0x20 = takes 2 $ sla getB setB
cbop 0x21 = takes 2 $ sla getC setC
cbop 0x22 = takes 2 $ sla getD setD
cbop 0x23 = takes 2 $ sla getE setE
cbop 0x24 = takes 2 $ sla getH setH
cbop 0x25 = takes 2 $ sla getL setL
cbop 0x26 = takes 4 $ sla (getHL >>= read8) (\v -> getHL >>= flip write8 v)
cbop 0x27 = takes 2 $ sla getA setA
-- SRA, right shift (arithmetic)
cbop 0x28 = takes 2 $ sra getB setB
cbop 0x29 = takes 2 $ sra getC setC
cbop 0x2A = takes 2 $ sra getD setD
cbop 0x2B = takes 2 $ sra getE setE
cbop 0x2C = takes 2 $ sra getH setH
cbop 0x2D = takes 2 $ sra getL setL
cbop 0x2E = takes 4 $ sra (getHL >>= read8) (\v -> getHL >>= flip write8 v)
cbop 0x2F = takes 2 $ sra getA setA
-- SRL, right shift (logical)
cbop 0x38 = takes 2 $ srl getB setB
cbop 0x39 = takes 2 $ srl getC setC
cbop 0x3A = takes 2 $ srl getD setD
cbop 0x3B = takes 2 $ srl getE setE
cbop 0x3C = takes 2 $ srl getH setH
cbop 0x3D = takes 2 $ srl getL setL
cbop 0x3E = takes 4 $ srl (getHL >>= read8) (\v -> getHL >>= flip write8 v)
cbop 0x3F = takes 2 $ srl getA setA
-- BIT, test a bit. Presumably an 8 bit immediate???
cbop 0x40 = takes 2 $ bitTest <$> next <*> getB >>= setFlag Carry
cbop 0x41 = takes 2 $ bitTest <$> next <*> getC >>= setFlag Carry
cbop 0x42 = takes 2 $ bitTest <$> next <*> getD >>= setFlag Carry
cbop 0x43 = takes 2 $ bitTest <$> next <*> getE >>= setFlag Carry
cbop 0x44 = takes 2 $ bitTest <$> next <*> getH >>= setFlag Carry
cbop 0x45 = takes 2 $ bitTest <$> next <*> getL >>= setFlag Carry
cbop 0x46 = takes 4 $ bitTest <$> next <*> (getHL >>= read8) >>= setFlag Carry
cbop 0x47 = takes 2 $ bitTest <$> next <*> getA >>= setFlag Carry
-- SET, set a bit
cbop 0xC0 = takes 2 $ bitSet <$> next <*> getB >>= setB
cbop 0xC1 = takes 2 $ bitSet <$> next <*> getC >>= setC
cbop 0xC2 = takes 2 $ bitSet <$> next <*> getD >>= setD
cbop 0xC3 = takes 2 $ bitSet <$> next <*> getE >>= setE
cbop 0xC4 = takes 2 $ bitSet <$> next <*> getH >>= setH
cbop 0xC5 = takes 2 $ bitSet <$> next <*> getL >>= setL
cbop 0xC6 =
  takes 4
    $   bitSet
    <$> next
    <*> (getHL >>= read8)
    >>= (\v -> getHL >>= flip write8 v)
cbop 0xC7 = takes 2 $ bitSet <$> next <*> getA >>= setA
-- RES, reset bit aka clear
cbop 0x80 = takes 2 $ bitClear <$> next <*> getB >>= setB
cbop 0x81 = takes 2 $ bitClear <$> next <*> getC >>= setC
cbop 0x82 = takes 2 $ bitClear <$> next <*> getD >>= setD
cbop 0x83 = takes 2 $ bitClear <$> next <*> getE >>= setE
cbop 0x84 = takes 2 $ bitClear <$> next <*> getH >>= setH
cbop 0x85 = takes 2 $ bitClear <$> next <*> getL >>= setL
cbop 0x86 =
  takes 4
    $   bitClear
    <$> next
    <*> (getHL >>= read8)
    >>= (\v -> getHL >>= flip write8 v)
cbop 0x87 = takes 2 $ bitClear <$> next <*> getA >>= setA

cbop x    = throwError $ "Invalid opcode: cb " ++ showHex x ""

add16To8 :: Word16 -> Word8 -> Word16
add16To8 a b = a + fromIntegral b

-- as above, but interpret the 8 bit offset as signed
add16to8Signed :: Word16 -> Word8 -> Word16
add16to8Signed a b = fromIntegral (fromIntegral a + (fromIntegral b :: Int16))

-- * ops dispatched to

-- ** conditional jump helpers
-- | absolute jump based on some condition
cjump :: (MonadPC m, MonadClock m) => Word16 -> Bool -> m ()
cjump a c = when c $ takes 1 . setPC $ a

-- ** uncategorised due to laziness
bitClear :: Word8 -> Word8 -> Word8
bitClear b r = r `clearBit` (fromIntegral b)

bitTest :: Word8 -> Word8 -> Bool
bitTest b r = not $ testBit r (fromIntegral b)

bitSet :: Word8 -> Word8 -> Word8
bitSet b r = r `setBit` (fromIntegral b)

rlc :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
rlc g s = do
  c <- getFlag Carry
  w <- g
  let c'  = testBit w 7
      w'  = shiftL w 1
      w'' = if c then setBit w' 0 else clearBit w' 0
  setFlag Carry c'
  setFlag Zero  (w'' == 0)
  s w''

rrc :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
rrc g s = do
  c <- getFlag Carry
  w <- g
  let c'  = testBit w 0
      w'  = shiftR w 1
      w'' = if c then setBit w' 7 else clearBit w' 7
  setFlag Carry c'
  setFlag Zero  (w'' == 0)
  s w''

rl :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
rl g s = bitShift g (`rotate` 1) 7 >>= s

rr :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
rr g s = bitShift g (`rotate` (-1)) 0 >>= s

-- unsafe shifts are OK here, because we know the size we're dealing with and
-- the shift amount is fixed
sla :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
sla g s = bitShift g (`unsafeShiftL` 1) 7 >>= s

-- bit 7 needs to stay the same
sra :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
sra g s = bitShift g aShiftR 0 >>= s

-- logical, bit 7 set to 0
srl :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
srl g s = bitShift g (`unsafeShiftR` 1) 0 >>= s

-- words only do logical shifts, we need an arithmetic shift
aShiftR :: Word8 -> Word8
aShiftR x = fromIntegral . (`unsafeShiftR` 1) $ y
 where
  y :: Int8
  y = fromIntegral x

-- reduce some duplication
bitShift :: (MonadFlags m) => m Word8 -> (Word8 -> Word8) -> Int -> m Word8
bitShift g o b = do
  w <- g
  setFlag Carry (testBit w b)
  let w' = o w
  setFlag Zero      (w' == 0)
  setFlag AddSub    False
  setFlag HalfCarry False
  return w'

inc16 :: (MonadFlags m) => m Word16 -> (Word16 -> m ()) -> m ()
inc16 g = add16 g (pure 1)

-- ** 8 bit arithmetic/bitwise ops

-- |add two registers, may set carry, half carry, zero, clears add/sub
add8 :: (MonadFlags m) => m Word8 -> m Word8 -> (Word8 -> m ()) -> m ()
add8 x y s = do
  x' <- x
  y' <- y
  let r = x' + y'
  setFlag Carry     (testBit (x' .|. y') 7 && not (testBit r 7))
  setFlag HalfCarry (testBit (x' .|. y') 3 && not (testBit r 3))
  clearFlag AddSub
  setFlag Zero (r == 0)
  s r

-- |add two registers with carry, same as 'add8' but maybe with an extra 1
adc8 :: (MonadFlags m) => m Word8 -> m Word8 -> (Word8 -> m ()) -> m ()
adc8 x y s = do
  x' <- x
  y' <- y
  c  <- getFlag Carry
  let r = x' + y' + if c then 1 else 0
  setFlag Carry     (testBit (x' .|. y') 7 && not (testBit r 7))
  setFlag HalfCarry (testBit (x' .|. y') 3 && not (testBit r 3))
  clearFlag AddSub
  setFlag Zero (r == 0)
  s r

-- |subtract second arg from the first, may set carry and half carry if no
-- borrow occurred, could set 0 and defnitely sets add/sub
sub8 :: (MonadFlags m) => m Word8 -> m Word8 -> (Word8 -> m ()) -> m ()
sub8 x y s = do
  x' <- x
  y' <- y
  let r = x' - y'
  -- carry flags are set if there was _not_ a borrow
  setFlag Carry     True
  setFlag HalfCarry (not (testBit r 3) || not (testBit y' 3))
  setFlag AddSub    True
  setFlag Zero      (r == 0)
  s r

-- |subtract with carry, as per 'sub8' but sometimes one less
sbc8
  :: (MonadReadReg8 m, MonadWriteReg8 m, MonadFlags m)
  => m Word8
  -> m Word8
  -> (Word8 -> m ())
  -> m ()
sbc8 = undefined

-- |bitwise and, clears carry and add/sub, sets half carry, could set zero
and8 :: (MonadFlags m) => m Word8 -> m Word8 -> (Word8 -> m ()) -> m ()
and8 a b s =
  (.&.)
    <$> a
    <*> b
    >>= (\r -> do
          setFlag Carry     False
          setFlag HalfCarry True
          setFlag AddSub    False
          setFlag Zero      (r == 0)
          return r
        )
    >>= s

-- |bitwise or, clears carry, add/sub and half carry but could set zero
or8 :: (MonadFlags m) => m Word8 -> m Word8 -> (Word8 -> m ()) -> m ()
or8 a b s =
  (.|.)
    <$> a
    <*> b
    >>= (\r -> do
          setFlag Carry     False
          setFlag HalfCarry False
          setFlag AddSub    False
          setFlag Zero      (r == 0)
          return r
        )
    >>= s

-- |bitwise xor, might set zero and clears the rest
xor8 :: (MonadFlags m) => m Word8 -> m Word8 -> (Word8 -> m ()) -> m ()
xor8 a b s =
  xor
    <$> a
    <*> b
    >>= (\r -> do
          setFlag Zero      (r == 0)
          setFlag Carry     False
          setFlag AddSub    False
          setFlag HalfCarry False
          return r
        )
    >>= s

-- |increment a register. Never sets carry, may set half carry or zero and
-- clears add/sub
inc8 :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
inc8 a s = do
  a' <- a
  let r = a' + 1
  setFlag Zero      (r == 0)
  setFlag AddSub    False
  setFlag HalfCarry (testBit a' 3 && not (testBit r 3))
  s r

-- |decrement a register. Doesn't touch carry but will set zero or half carry
-- appropriately and set add/sub
dec8 :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
dec8 a s = do
  a' <- a
  let r = a' - 1
  setFlag Zero      (r == 0)
  setFlag AddSub    True
  setFlag HalfCarry (testBit r 3 && not (testBit a' 3))
  s r

-- |swap upper and lower nibbles, sets zero if appropriate clears the rest.
swap :: (MonadFlags m) => m Word8 -> (Word8 -> m ()) -> m ()
swap a s = a >>= sw >>= s
 where
  sw x = do
    x' <- a
    setFlag Zero      (x' == 0)
    setFlag HalfCarry False
    setFlag Carry     False
    setFlag AddSub    False
    return $ unsafeShiftL x' 4 .|. unsafeShiftR x' 4

-- ** 16 bit arithmetic

-- |add two sixteen bit ints. Sets half carry if bit 11 rolls over, carry for
-- bit 15
add16 :: (MonadFlags m) => m Word16 -> m Word16 -> (Word16 -> m ()) -> m ()
add16 a b s = do
  a' <- a
  b' <- b
  let r = a' + b'
  setFlag Carry     (testBit (a' .|. b') 15 && not (testBit r 15))
  setFlag HalfCarry (testBit (a' .|. b') 11 && not (testBit r 11))
  clearFlag AddSub
  setFlag Zero (r == 0)
  s r

-- |decrement 16 bits, leaving all flags untouched.
dec16 :: (MonadFlags m) => m Word16 -> (Word16 -> m ()) -> m ()
dec16 g s = (-) 1 <$> g >>= s

-- | gets the value at (PC) and increments PC, for fetching immediate values etc.
-- TODO maybe move this into MonadPC itself
next :: (MonadPC m, MonadMem m) => m Word8
next = (getPC >>= read8) <* incPC

-- | gets a 16 bit starting at PC and increments PC twice.
-- TODO check the order of the bytes in the 16 is as expected
next16 :: (MonadPC m, MonadMem m) => m Word16
next16 = (getPC >>= read16) <* incPC <* incPC
