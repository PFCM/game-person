{-| Types and classes for representing CPU state during execution. -}
module Hboi.CPU.State
  ( MonadClock(..)
  , MonadPC(..)
  , MonadSP(..)
  , MonadReadReg8(..)
  , MonadWriteReg8(..)
  , MonadReadReg16(..)
  , MonadWriteReg16(..)
  , MonadFlags(..)
  , Flag(..)
  )
where

import           Data.Word                                ( Word8
                                                          , Word16
                                                          )


{-| The internal state of the CPU:
  - timing
    - how many cycles have elapsed since boot
    - how many cycles the last instruction took
  - registers
    - 8 x 8 bit registers, some with special purposes:
      - A -- accumulator
      - B
      - C
      - D
      - E
      - F -- flags
      - H
      - L
    - 2 x 16 bit registers, both special
      - SP -- stack pointer, grows by _decrementing_ and usually initialised to
        0xFFEE on boot, but this is not guaranteed
      - PC -- program counter, initialized to 0x100 on boot
    - the 8 bit registers can also be viewed as 16 bit registers in the
      following pairs:
      - AF, BC, DE, HL
    - the flag register is special, it contains information about the previous
      operation. The layout is:
      -------------------------------------------------------------------------
      |bit | name | set | clear | desc.                                       |
      -------------------------------------------------------------------------
      | 7  | zf   | Z   | NZ    | zero flag, if the last op was 0             |
      | 6  | n    | -   |  -    | Add/Sub flag for BCD ops                    |
      | 5  | h    | -   |  -    | half-carry flag for BCD ops                 |
      | 4  | cy   | C   | NC    | carry flag                                  |
      |3-0 | -    | -   | -     | unused, always 0                            |
      -------------------------------------------------------------------------
-}
data State = State { regs :: Registers -- current register values
                   , oclock :: Clock -- overall timing since boot
                   }
data Registers = Registers { rA :: Word8
                           , rB :: Word8
                           , rC :: Word8
                           , rD :: Word8
                           , rE :: Word8
                           , rF :: Word8
                           , rH :: Word8
                           , rL :: Word8
                           , rSP :: Word16
                           , rPC :: Word16
                           }
data Clock = Clock Word16 Word16 -- actual

-- provides a way of running a monadic action that takes a certain number of
-- machine cycles, updating clocks accordingly
class Monad m => MonadClock m where
  incClock :: Word8 -> m ()

  takes :: Word8 -> m a -> m a
  takes inc a = do
    r <- a
    incClock inc
    return r

-- can read the 8 bit registers
class Monad m => MonadReadReg8 m where
  getA :: m Word8
  getB :: m Word8
  getC :: m Word8
  getD :: m Word8
  getE :: m Word8
  getF :: m Word8
  getH :: m Word8
  getL :: m Word8

-- can write the 8 bit registers
class Monad m => MonadWriteReg8 m where
  setA :: Word8 -> m ()
  setB :: Word8 -> m ()
  setC :: Word8 -> m ()
  setD :: Word8 -> m ()
  setE :: Word8 -> m ()
  setF :: Word8 -> m ()
  setH :: Word8 -> m ()
  setL :: Word8 -> m ()

-- can read the 16 bit aggregated registers
class Monad m => MonadReadReg16 m where
  getAF :: m Word16
  getBC :: m Word16
  getDE :: m Word16
  getHL :: m Word16
  getSP :: m Word16

-- can write the 16 bit aggregate registers
class Monad m => MonadWriteReg16 m where
  -- note setAF shouldn't be able to write all of F
  setAF :: Word16 -> m ()
  setBC :: Word16 -> m ()
  setDE :: Word16 -> m ()
  setHL :: Word16 -> m ()
  setSP :: Word16 -> m ()

-- use the stack pointer
class Monad m => MonadSP m where
  spush :: Word16 -> m ()
  spop :: m Word16
  readSP :: m Word16

-- can read/write the program counter, should only really be needed by jumps
class Monad m => MonadPC m where
  getPC :: m Word16
  setPC :: Word16 -> m ()
  incPC :: m ()
  incPC = fmap (+1) getPC >>= setPC

-- set, clear, query flags
data Flag = Zero | Carry | AddSub | HalfCarry | IME
class Monad m => MonadFlags m where
  getFlag :: Flag -> m Bool
  setFlag :: Flag -> Bool -> m ()
  clearFlag :: Flag -> m ()
  clearFlag f = setFlag f False
