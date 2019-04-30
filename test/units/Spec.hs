{-| collects all the tests -}

import           Test.Hspec

import           CPUTest                                  ( cpuUnits )

main :: IO ()
main = hspec cpuUnits
