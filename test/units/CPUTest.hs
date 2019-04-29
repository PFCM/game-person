{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-| tests for Hboi.CPU -}
module CPUTest where

import           Hboi.CPU
import           Hboi.CPU.OpCodes
import           Hboi.CPU.State

import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Writer.Strict
import           Data.Word
import           Data.Bits
import           Test.Hspec


newtype ClockT m a = ClockT {unClock :: WriterT (Sum Word16) m a}
  deriving (Functor, Applicative, Monad, MonadWriter (Sum Word16), MonadTrans)

instance (Monad m) => MonadClock (ClockT m) where
  incClock i = tell (Sum . fromIntegral $ i)

-- runs the action with a clock starting from 0, returns the result
runClock :: ClockT Identity () -> Word16
runClock = getSum . runIdentity . execWriterT . unClock

ignoreClock :: (Monad m) => ClockT m a -> m a
ignoreClock = fmap fst . runWriterT . unClock

data Reg16 = Reg16 { rAF::Word16, rBC::Word16, rDE::Word16, rHL::Word16, rSP::Word16}
  deriving (Eq, Show)
newtype Reg16T m a = Reg16T {unReg16 :: StateT Reg16 m a}
  deriving (Functor, Applicative, Monad, MonadState Reg16, MonadTrans)

instance (Monad m) => MonadReadReg16 (Reg16T m) where
  getAF = gets rAF
  getBC = gets rBC
  getDE = gets rDE
  getHL = gets rHL
  getSP = gets rSP

instance (Monad m) => MonadWriteReg16 (Reg16T m) where
  setAF v = modify' (\s -> s { rAF = v })
  setBC v = modify' (\s -> s { rBC = v })
  setDE v = modify' (\s -> s { rDE = v })
  setHL v = modify' (\s -> s { rHL = v })
  setSP v = modify' (\s -> s { rSP = v })

instance (Monad m) => MonadClock (Reg16T (ClockT m)) where
  incClock i = lift $ tell (Sum . fromIntegral $ i)

defaultReg16 :: Reg16
defaultReg16 = Reg16 { rAF = 0, rBC = 0, rDE = 0, rHL = 0, rSP = 0 }

runReg16 :: (Monad m) => Reg16 -> Reg16T m () -> m Reg16
runReg16 r a = execStateT (unReg16 a) r

data Reg8 = Reg8 {rA::Word8, rB::Word8, rC::Word8, rD::Word8, rE::Word8, rH::Word8, rL::Word8, flags::Word8}
defaultReg8 = Reg8 { rA    = 0x01
                   , rB    = 0x0F
                   , rC    = 0x11
                   , rD    = 0xF0
                   , rE    = 0xFF
                   , rH    = 0x11
                   , rL    = 0xCD
                   , flags = 0
                   }
newtype Reg8T m a = Reg8T {unReg8 :: StateT Reg8 m a}
  deriving (Functor, Applicative, Monad, MonadState Reg8, MonadTrans)

instance (Monad m) => MonadReadReg8 (Reg8T m) where
  getA = gets rA
  getB = gets rB
  getC = gets rC
  getD = gets rD
  getE = gets rE
  getF = gets flags
  getH = gets rH
  getL = gets rL

instance (Monad m) => MonadWriteReg8 (Reg8T m) where
  setA v = modify' (\s -> s { rA = v })
  setB v = modify' (\s -> s { rB = v })
  setC v = modify' (\s -> s { rC = v })
  setD v = modify' (\s -> s { rD = v })
  setE v = modify' (\s -> s { rE = v })
  setF v = modify' (\s -> s { flags = v })
  setH v = modify' (\s -> s { rH = v })
  setL v = modify' (\s -> s { rL = v })

instance (Monad m) => MonadFlags (Reg8T m) where
  getFlag Zero      = gets ((`testBit` 0) . flags)
  getFlag Carry     = gets ((`testBit` 1) . flags)
  getFlag AddSub    = gets ((`testBit` 2) . flags)
  getFlag HalfCarry = gets ((`testBit` 3) . flags)
  getFlag IME       = gets ((`testBit` 4) . flags)

  setFlag Zero      v = modify' (\s -> s { flags = setOrClear v (flags s) 0 })
  setFlag Carry     v = modify' (\s -> s { flags = setOrClear v (flags s) 1 })
  setFlag AddSub    v = modify' (\s -> s { flags = setOrClear v (flags s) 2 })
  setFlag HalfCarry v = modify' (\s -> s { flags = setOrClear v (flags s) 3 })
  setFlag IME       v = modify' (\s -> s { flags = setOrClear v (flags s) 4 })

instance (Monad m) => MonadClock (Reg8T (ClockT m)) where
  incClock i = lift $ tell (Sum . fromIntegral $ i)

setOrClear :: Bool -> Word8 -> Int -> Word8
setOrClear True  a i = setBit a i
setOrClear False a i = clearBit a i

runReg8Default :: Reg8T (ClockT Identity) () -> Reg8
runReg8Default a =
  runIdentity (ignoreClock (execStateT (unReg8 a) defaultReg8))

runReg8Carry :: Reg8T (ClockT Identity) () -> Reg8
runReg8Carry a = runReg8Default (setFlag Carry True >> a)


cpuUnits :: Spec
cpuUnits = do
  describe "inc (16 bit)" $ it "increments correct value" $ do
    runIdentity (ignoreClock (runReg16 defaultReg16 $ inc16 getAF setAF))
      `shouldBe` Reg16 { rAF = 1, rBC = 0, rDE = 0, rHL = 0, rSP = 0 }
    runIdentity (ignoreClock (runReg16 defaultReg16 $ inc16 getBC setBC))
      `shouldBe` Reg16 { rAF = 0, rBC = 1, rDE = 0, rHL = 0, rSP = 0 }
    runIdentity (ignoreClock (runReg16 defaultReg16 $ inc16 getDE setDE))
      `shouldBe` Reg16 { rAF = 0, rBC = 0, rDE = 1, rHL = 0, rSP = 0 }
    runIdentity (ignoreClock (runReg16 defaultReg16 $ inc16 getHL setHL))
      `shouldBe` Reg16 { rAF = 0, rBC = 0, rDE = 0, rHL = 1, rSP = 0 }

  describe "add8" $ do
    it "computes the correct values" $ do
      (rA . runReg8Default $ add8 getA getA setA) `shouldBe` 2
      (rB . runReg8Default $ add8 getB getA setB) `shouldBe` 0x10
      (rA . runReg8Default $ add8 getC getD setC) `shouldBe` 1
      (rD . runReg8Default $ add8 getC getD setD) `shouldBe` 1 -- overflows
      (rH . runReg8Default $ add8 getH getL setH) `shouldBe` 0xDE
      (rL . runReg8Default $ add8 getL getA setL) `shouldBe` 0xCE
    it "sets the correct flags" $ do
      (flags . runReg8Default $ add8 getA getA setA) `shouldBe` 0
      (flags . runReg8Default $ add8 getA getB setA) `shouldBe` 8 -- half carry flag should be set (bit 3)
      (flags . runReg8Default $ add8 getD getC setD) `shouldBe` 2
      (flags . runReg8Default $ add8 getE getA setE) `shouldBe` 11 -- carry, half carry, zero
      (flags . runReg8Default $ (add8 getE getA setE >> add8 getA getA setA))
        `shouldBe` 0

  describe "adc8" $ do
    it "computes the correct values without carry" $ do
      (rA . runReg8Default $ adc8 getA getA setA) `shouldBe` 2
      (rB . runReg8Default $ adc8 getB getA setB) `shouldBe` 0x10
      (rA . runReg8Default $ adc8 getC getD setC) `shouldBe` 1
      (rD . runReg8Default $ adc8 getC getD setD) `shouldBe` 1 -- overflows
      (rH . runReg8Default $ adc8 getH getL setH) `shouldBe` 0xDE
      (rL . runReg8Default $ adc8 getL getA setL) `shouldBe` 0xCE
    it "sets the correct flags without carry" $ do
      (flags . runReg8Default $ adc8 getA getA setA) `shouldBe` 0
      (flags . runReg8Default $ adc8 getA getB setA) `shouldBe` 8 -- half carry flag should be set (bit 3)
      (flags . runReg8Default $ adc8 getD getC setD) `shouldBe` 2
      (flags . runReg8Default $ adc8 getE getA setE) `shouldBe` 11 -- carry, half carry, zero
      (flags . runReg8Default $ (adc8 getE getA setE >> adc8 getA getA setA))
        `shouldBe` 0
    it "computes the correct values with carry" $ do
      -- should add a test that wouldn't overflow except for the carry
      (rA . runReg8Carry $ adc8 getA getA setA) `shouldBe` 3
      (rB . runReg8Carry $ adc8 getB getA setB) `shouldBe` 0x11
      (rA . runReg8Carry $ adc8 getC getD setC) `shouldBe` 1
      (rD . runReg8Carry $ adc8 getC getD setD) `shouldBe` 2 -- overflows
      (rH . runReg8Carry $ adc8 getH getL setH) `shouldBe` 0xDF
      (rL . runReg8Carry $ adc8 getL getA setL) `shouldBe` 0xCF
    it "sets the correct flags with carry" $ do
      (flags . runReg8Carry $ adc8 getA getA setA) `shouldBe` 0
      (flags . runReg8Carry $ adc8 getA getB setA) `shouldBe` 0b1000 -- half carry flag should be set (bit 3)
      (flags . runReg8Carry $ adc8 getD getC setD) `shouldBe` 0b0010
      (flags . runReg8Carry $ adc8 getE getA setE) `shouldBe` 0b1010
      (flags . runReg8Carry $ (adc8 getE getA setE >> adc8 getA getA setA))
        `shouldBe` 0

  describe "sub8" $ do
    it "computes correct values" $ do
      (rA . runReg8Default $ sub8 getA getA setA) `shouldBe` 0
      (rB . runReg8Default $ sub8 getB getA setB) `shouldBe` 0x0E
      (rA . runReg8Default $ sub8 getC getD setC) `shouldBe` 1
      (rD . runReg8Default $ sub8 getC getD setD) `shouldBe` 0x21 -- overflows
      (rH . runReg8Default $ sub8 getH getL setH) `shouldBe` 0x44
      (rL . runReg8Default $ sub8 getL getA setL) `shouldBe` 0xCC
    it "sets correct flags" $ do -- recall flags are stored hncz
      (flags . runReg8Carry $ sub8 getA getA setA) `shouldBe` 0b1111
      (flags . runReg8Carry $ sub8 getD getA setD) `shouldBe` 0b1110

  describe "and8" $ do
    it "computes correct values" $ do
      (rA . runReg8Default $ and8 getA getA setA) `shouldBe` 1
      (rB . runReg8Default $ and8 getB getA setB) `shouldBe` 0x01
      (rA . runReg8Default $ and8 getC getD setC) `shouldBe` 1
      (rD . runReg8Default $ and8 getC getD setD) `shouldBe` 0x10
      (rH . runReg8Default $ and8 getH getL setH) `shouldBe` 0x01
      (rL . runReg8Default $ and8 getL getA setL) `shouldBe` 0x01
    it "sets correct flags" $ do
      (flags . runReg8Carry $ and8 getA getD setA) `shouldBe` 0b1001
      (flags . runReg8Carry $ and8 getA getB setB) `shouldBe` 0b1000
      (flags . runReg8Default $ and8 getA getD setA) `shouldBe` 0b1001
      (flags . runReg8Default $ and8 getA getB setB) `shouldBe` 0b1000

  describe "or8" $ do
    it "computes correct values" $ do
      (rA . runReg8Default $ or8 getA getA setA) `shouldBe` 1
      (rB . runReg8Default $ or8 getB getA setB) `shouldBe` 0x0F
      (rA . runReg8Default $ or8 getC getD setC) `shouldBe` 1
      (rD . runReg8Default $ or8 getC getD setD) `shouldBe` 0xF1
      (rH . runReg8Default $ or8 getH getL setH) `shouldBe` 0xDD
      (rL . runReg8Default $ or8 getL getA setL) `shouldBe` 0xCD
    it "sets correct flags" $ do
      (flags . runReg8Carry $ or8 getH getL setH) `shouldBe` 0b0000
      (flags . runReg8Carry $ or8 getA getB setB) `shouldBe` 0b0000
      (flags . runReg8Default $ or8 getF getF setA) `shouldBe` 0b0001
      (flags . runReg8Default $ or8 getA getB setB) `shouldBe` 0b0000

  describe "xor8" $ do
    it "computes correct values" $ do
      (rA . runReg8Default $ xor8 getA getA setA) `shouldBe` 0
      (rB . runReg8Default $ xor8 getB getA setB) `shouldBe` 0x0E
      (rA . runReg8Default $ xor8 getC getD setC) `shouldBe` 1
      (rD . runReg8Default $ xor8 getC getD setD) `shouldBe` 0xE1
      (rH . runReg8Default $ xor8 getH getL setH) `shouldBe` 0xDC
      (rL . runReg8Default $ xor8 getL getA setL) `shouldBe` 0xCC
    it "sets correct flags" $ do
      (flags . runReg8Carry $ xor8 getH getL setH) `shouldBe` 0b0000
      (flags . runReg8Carry $ xor8 getA getA setA) `shouldBe` 0b0001
      (flags . runReg8Default $ xor8 getA getA setA) `shouldBe` 0b0001
      (flags . runReg8Default $ xor8 getA getB setB) `shouldBe` 0b0000

      {- { rA    = 0x01
                   , rF    = 0x08
                   , rB    = 0x0F
                   , rC    = 0x11
                   , rD    = 0xF0
                   , rE    = 0xFF
                   , rH    = 0x11
                   , rL    = 0xCD
                   , flags = 0
                   }-}
  describe "inc8" $ do
    it "computes correct values" $ do
      (rA . runReg8Default $ inc8 getA setA) `shouldBe` 0x02
      (rB . runReg8Default $ inc8 getB setB) `shouldBe` 0x10
      (rC . runReg8Default $ inc8 getC setC) `shouldBe` 0x12
      (rD . runReg8Default $ inc8 getD setD) `shouldBe` 0xF1
      (rE . runReg8Default $ inc8 getE setE) `shouldBe` 0x00
      (rH . runReg8Default $ inc8 getH setH) `shouldBe` 0x12
      (rL . runReg8Default $ inc8 getL setL) `shouldBe` 0xCE
      (rA . runReg8Default $ inc8 getL setL) `shouldBe` 0x01
    it "sets correct flags" $ do
      (flags . runReg8Default $ inc8 getA setA) `shouldBe` 0b0000
      -- zero, should also set half carry
      (flags . runReg8Default $ inc8 getE setE) `shouldBe` 0b1001
      -- half carry
      (flags . runReg8Default $ inc8 getB setB) `shouldBe` 0b1000
      -- carry flag should be left alone
      (flags . runReg8Carry $ inc8 getA setA) `shouldBe` 0b0010
      (flags . runReg8Carry $ inc8 getE setE) `shouldBe` 0b1011
      (flags . runReg8Carry $ inc8 getB setB) `shouldBe` 0b1010
