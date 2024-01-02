{-| This is the interface to memory. Generally it appears that valid memory
addresses are between 0x0000 and 0xFFFF inclusive $FFFF is the interrupt
register and 0xFF00 to 0xFF7F are memory mapped to peripherals, such as the LCD.
We need to be able to read and write one byte at a time, and we need
16 bit addresses.

This module has the interface, concrete implementations are tbd.
-}
module Hboi.Memory
  ( MonadMem(..)
  )
where

import           Data.Word                                ( Word8
                                                          , Word16
                                                          )

class (Monad m) => MonadMem m where
  read8 :: Word16 -> m Word8
  write8 :: Word16 -> Word8 -> m ()

  read16 :: Word16 -> m Word16
  -- address -> value -> action
  write16 :: Word16 -> Word16 -> m ()
