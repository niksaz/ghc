module GHCi.UI.Prompt (
  PModule,
  PFunction
) where

data PModule = Module {
  modulePackageKey :: String,
  moduleName :: String
}

type PFunction = [PModule]
              -> Int
              -> IO String

