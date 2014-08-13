module Data.LiveFusion.HsBackend.Types where

import Language.Haskell.TH as TH


class THElt e where
  cgElt :: THElt e => e -> TH.Exp


instance THElt Int where
  cgElt = TH.LitE . IntegerL . toInteger

instance THElt Float where
  cgElt = TH.LitE . RationalL . toRational

instance THElt Double where
  cgElt = TH.LitE . RationalL . toRational

instance THElt Bool where
  cgElt True  = TH.ConE trueName
  cgElt False = TH.ConE falseName

instance (THElt a, THElt b) => THElt (a,b) where
  cgElt (a,b) = TH.TupE [cgElt a, cgElt b]

instance (THElt a, THElt b, THElt c) => THElt (a,b,c) where
  cgElt (a,b,c) = TH.TupE [cgElt a, cgElt b, cgElt c]

instance (THElt a, THElt b, THElt c, THElt d) => THElt (a,b,c,d) where
  cgElt (a,b,c,d) = TH.TupE [cgElt a, cgElt b, cgElt c, cgElt d]

instance (THElt a, THElt b, THElt c, THElt d, THElt e) => THElt (a,b,c,d,e) where
  cgElt (a,b,c,d,e) = TH.TupE [cgElt a, cgElt b, cgElt c, cgElt d, cgElt e]

instance (THElt a, THElt b, THElt c, THElt d, THElt e, THElt f) => THElt (a,b,c,d,e,f) where
  cgElt (a,b,c,d,e,f) = TH.TupE [cgElt a, cgElt b, cgElt c, cgElt d, cgElt e, cgElt f]


trueName, falseName :: TH.Name
trueName  = mkName "True"
falseName = mkName "False"
