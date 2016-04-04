module GHCi.UI.Prompt (
  PModule      
) where

data PModule = Module {
  modulePackageKey :: String,
  moduleName :: String
}

type PFunction = [PModule] 
              -> Int
              -> IO String

