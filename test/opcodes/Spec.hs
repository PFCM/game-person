{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-|
Opcode coverage, automatically generated thans to the fine people at
https://github.com/lmmendes/game-boy-opcodes

To get the test data, there is a script "get-opcodes.sh" which you will need
to run before attempting these tests.
 -}
import           Hboi.CPU.State
import           Hboi.CPU.OpCodes                         ( op )
import           Hboi.Memory

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Aeson
import           Data.Aeson.Types
import           Data.Bits
import qualified Data.ByteString.Lazy.Char8    as B
import           Data.Functor
import qualified Data.Map.Strict               as M
import qualified Data.Text                     as T
import qualified Data.Text.Read                as T
import qualified Data.Vector.Unboxed           as V
import           Data.Word
import           Numeric                                  ( showHex )
import           Test.Hspec
import           GHC.Generics
import           System.Exit

data Opcode = Opcode { mnemonic :: String
                     , len :: Int
                     , code :: Word8
                     , cycles :: Int
                     , operand1 :: Maybe String
                     , operand2 :: Maybe String
                     } deriving (Show)

instance FromJSON Opcode where
  parseJSON (Object a) =
    Opcode
      <$> (a .: "mnemonic")
      <*> (a .: "length")
      <*> (a .: "addr" >>= readHex)
      <*> (head <$> a .: "cycles")
      <*> (a .:? "operand1")
      <*> (a .:? "operand2")
  parseJSON invalid = typeMismatch "Object" invalid

readHex :: T.Text -> Parser Word8
readHex t = case T.hexadecimal t of
  Right (i, r) -> return . fromIntegral $ i
  Left  msg    -> fail $ "need a hexadecimal int, got: " ++ T.unpack t

data Opcodes = Opcodes { unprefixed :: M.Map String Opcode
                       , cbprefixed :: M.Map String Opcode
                       } deriving (Generic, Show)

instance FromJSON Opcodes where
  -- GHC can do it for us


-- We need a working basic implementation of all the constraints that 'op'
-- requires. We will do it the simplest way with a record type and the state
-- monad.
data CPUState = CPUState { clock :: Int
                         , rPC :: Word16
                         , rSP :: Word16
                         , rF :: Word8
                         , rA :: Word8
                         , rB :: Word8
                         , rC :: Word8
                         , rD :: Word8
                         , rE :: Word8
                         , rH :: Word8
                         , rL :: Word8
                         , mem :: V.Vector Word8
                         , ime :: Bool
                         } deriving (Show)

defaultState :: CPUState
defaultState = CPUState 0 0x100 0xFF00 0 0 0 0 0 0 0 0 defaultMem True

defaultMem :: V.Vector Word8
defaultMem = V.enumFromN 0 65536

defaultNext :: Word8 -> CPUState
defaultNext oc = defaultState
  { mem = mem defaultState V.// [(fromIntegral . rPC $ defaultState, oc)]
  }

newtype MonadCPUT m a = MonadCPUT  {unCPUT :: StateT CPUState (ExceptT String m) a}
                    deriving (Functor, Applicative, Monad, MonadState CPUState, MonadError String)

instance (Monad m) => MonadClock (MonadCPUT m) where
  incClock i = modify' (\s -> s { clock = clock s + fromIntegral i * 4 })

instance (Monad m) => MonadReadReg8 (MonadCPUT m) where
  getA = gets rA
  getB = gets rB
  getC = gets rC
  getD = gets rD
  getE = gets rE
  getH = gets rH
  getL = gets rL
  getF = gets rF

instance (Monad m) => MonadWriteReg8 (MonadCPUT m) where
  setA v = modify' (\s -> s { rA = v })
  setB v = modify' (\s -> s { rB = v })
  setC v = modify' (\s -> s { rC = v })
  setD v = modify' (\s -> s { rD = v })
  setE v = modify' (\s -> s { rE = v })
  setF v = modify' (\s -> s { rF = v })
  setH v = modify' (\s -> s { rH = v })
  setL v = modify' (\s -> s { rL = v })

instance (Monad m) => MonadFlags (MonadCPUT m) where
  getFlag Zero      = gets ((`testBit` 0) . rF)
  getFlag Carry     = gets ((`testBit` 1) . rF)
  getFlag AddSub    = gets ((`testBit` 2) . rF)
  getFlag HalfCarry = gets ((`testBit` 3) . rF)
  getFlag IME       = gets ime

  setFlag Zero      v = modify' (\s -> s { rF = setOrClear v (rF s) 0 })
  setFlag Carry     v = modify' (\s -> s { rF = setOrClear v (rF s) 1 })
  setFlag AddSub    v = modify' (\s -> s { rF = setOrClear v (rF s) 2 })
  setFlag HalfCarry v = modify' (\s -> s { rF = setOrClear v (rF s) 3 })
  setFlag IME       v = modify' (\s -> s { ime = v })

setOrClear :: Bool -> Word8 -> Int -> Word8
setOrClear True  a i = setBit a i
setOrClear False a i = clearBit a i

instance (Monad m) => MonadReadReg16 (MonadCPUT m) where
  getSP = gets rSP
  getAF = gets (aggregate rA rF)
  getBC = gets (aggregate rB rC)
  getDE = gets (aggregate rD rE)
  getHL = gets (aggregate rH rL)

aggregate :: (a -> Word8) -> (a -> Word8) -> a -> Word16
aggregate a b s = upper .|. lower
 where
  upper = (fromIntegral . a $ s) `shiftL` 8
  lower = fromIntegral . b $ s

instance (Monad m) => MonadWriteReg16 (MonadCPUT m) where
  setSP v = modify' (\s -> s { rSP = v })
  setAF v = modify' (\s -> s { rA = upper v, rF = lower v })
  setBC v = modify' (\s -> s { rB = upper v, rC = lower v })
  setDE v = modify' (\s -> s { rD = upper v, rE = lower v })
  setHL v = modify' (\s -> s { rH = upper v, rL = lower v })

upper :: Word16 -> Word8
upper = fromIntegral . flip shiftR 8

lower :: Word16 -> Word8
lower = fromIntegral

instance (Monad m) => MonadMem (MonadCPUT m) where
  read8 a = gets ((V.! fromIntegral a) . mem)
  write8 a v = modify' (\s -> s { mem = mem s V.// [(fromIntegral a, v)] })

  read16 a = gets $ aggregate ((V.! fromIntegral a) . mem)
                              ((V.! (fromIntegral a + 1)) . mem)
  write16 a v = modify'
    (\s -> s
      { mem = mem s
                V.// [(fromIntegral a, upper v), (fromIntegral a + 1, lower v)]
      }
    )

instance (Monad m) => MonadSP (MonadCPUT m) where
  spush v =
    getSP
      >>= (\sp -> do
            write16 sp v
            setSP (sp - 2)
          )
  spop =
    getSP
      >>= (\sp -> do
            v <- read16 sp
            setSP (sp + 2)
            return v
          )
  readSP = getSP

instance (Monad m) => MonadPC (MonadCPUT m) where
  getPC = gets rPC
  setPC v = modify' (\s -> s { rPC = v })

runOp :: Word8 -> Either String CPUState
runOp oc = runIdentity (runExceptT (execStateT (unCPUT (op oc)) defaultState))

runCBOp :: Word8 -> Either String CPUState
runCBOp oc =
  runIdentity (runExceptT (execStateT (unCPUT (op 0xCB)) (defaultNext oc)))

buildCase :: Opcode -> Spec
buildCase o = it title test
 where
  title = showHex
    (code o)
    (" (" ++ mnemonic o ++ ") takes " ++ (show . cycles $ o) ++ " cycles")
  test = clock <$> runOp (code o) `shouldBe` Right (cycles o)

buildCBCase :: Opcode -> Spec
buildCBCase o = it title test
 where
  title = showHex
    (code o)
    (" (" ++ mnemonic o ++ ") takes " ++ (show . cycles $ o) ++ " cycles")
  test = clock <$> runCBOp (code o) `shouldBe` Right (cycles o)

genNormal :: M.Map String Opcode -> Spec
genNormal ocs = traverse buildCase ocs $> ()

genCB :: M.Map String Opcode -> Spec
genCB ocs = traverse buildCBCase ocs $> ()

genSpec :: Opcodes -> Spec
genSpec ocs = do
  describe "normal opcode:" . genNormal . unprefixed $ ocs
  describe "cb prefixed:" . genCB . cbprefixed $ ocs


main :: IO ()
main = do
  bytes <- B.readFile "test/data/opcodes.json"
  case eitherDecode' bytes of
    Right ops -> hspec . genSpec $ ops
    Left  err -> print err >> exitWith (ExitFailure 1)
