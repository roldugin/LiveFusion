module Data.LiveFusion.Backend where

import Data.Typeable

class Code code where
  getNative :: code t -> t
