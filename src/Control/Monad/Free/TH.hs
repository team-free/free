{-# LANGUAGE TemplateHaskell #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.TH
-- Copyright   :  (C) 2008-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Automatic generation of free monadic actions.
--
----------------------------------------------------------------------------
module Control.Monad.Free.TH
  ( makeFree ) where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.Free.TH.Internal (liftDec)
import Data.Char (toLower)
import Language.Haskell.TH

-- | @$(makeFree ''Type)@ provides free monadic actions for the
-- constructors of the given type.
makeFree :: Name -> Q [Dec]
makeFree tyCon = do
  info <- reify tyCon
  case info of
    TyConI dec -> liftDec dec
    _ -> fail "makeFree expects a type constructor"

