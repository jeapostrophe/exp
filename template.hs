#!/usr/bin/env stack
{- stack runghc
--package hspec
--package smallcheck
--package hspec-smallcheck
--package text
--package containers
--package mtl
--package generic-deriving
 -}
{- --resolver lts-14.16
--install-ghc
-}

{-# OPTIONS_GHC -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wredundant-constraints #-}
{- MAYBE: -fno-warn-orphans -}

{-# LANGUAGE ApplicativeDo, BangPatterns, ConstraintKinds, DataKinds,
DefaultSignatures, DeriveFoldable, DeriveFunctor, DeriveGeneric,
DeriveLift, DeriveTraversable, DerivingStrategies, EmptyCase,
ExistentialQuantification, FlexibleContexts, FlexibleInstances,
FunctionalDependencies, GADTs, GeneralizedNewtypeDeriving,
InstanceSigs, KindSignatures, LambdaCase, MultiParamTypeClasses,
MultiWayIf, NamedFieldPuns, OverloadedStrings, PatternSynonyms,
RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections,
TypeApplications, TypeFamilies, TypeFamilyDependencies, TypeOperators
#-}

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.Hspec.SmallCheck
import Data.Text

main :: IO ()
main = hspec $ do
  return ()
