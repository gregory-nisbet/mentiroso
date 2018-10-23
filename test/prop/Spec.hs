{-# LANGUAGE BangPatterns #-}

-- NOTE:
--
-- The NoExcept tests rely on the fact that an "undefined" or similar
-- will crash the program and the test suite.
-- That is what the "noexcept" tests are for. They quickly run through
-- the domain of the functions given to make sure that they don't throw
-- exceptions inadvertently.
-- TODO: we are using True (due to implies) instead of skipping tests.
-- this is a problem. do something about it.
import Control.Monad (unless)
import System.Exit (exitFailure)
import Test.QuickCheck
  ( Result
  , Testable
  , maxDiscardRatio
  , maxShrinks
  , maxSuccess
  , property
  , quickCheckWithResult
  , reason
  , stdArgs
  )
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Property (failed, succeeded)
import qualified Test.QuickCheck.Property as P
import Test.QuickCheck.Test (isSuccess)
import qualified Typesys as T
import Typesys (From(..), To(..))

data SimpleFailure
  = SFSuccess
  | SFMessage String
  deriving (Eq, Show)

instance QC.Testable SimpleFailure where
  property SFSuccess = property $ succeeded
  property (SFMessage msg) = out
    where
      prop :: P.Result
      prop = (failed {P.reason = msg})
      out :: P.Property
      out = property prop

-- use ints as the type for vars in these examples.
-- it looks a little weird but makes sense after a while.
type VarType = Int

(-->) :: Bool -> Bool -> Bool
x --> y = (not x) || y

-- same as equals, but for documentation purposes
(<-->) :: Bool -> Bool -> Bool
x <--> y = x == y

(~~) :: Eq k => Either a k -> Either a k -> Bool
(Right a) ~~ (Right b) = a == b
(Left _) ~~ (Left _) = True
_ ~~ _ = False

(|>) x f = f x

k_pred_noexcept_trials = 5000

-- mostly just used to force evaluation, still somewhat useful
eq_self_strict :: Eq a => a -> Bool
eq_self_strict !x = x == x

-- PREAMBLE: check that none of the basic types ever throw an exception 
prop_gettype_noexcept :: T.Term VarType -> Bool
prop_gettype_noexcept x = eq_self_strict $ T.gettype x

prop_gettype_noexcept' :: IO Result
prop_gettype_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_gettype_noexcept

prop_is_well_formed_noexcept :: T.Term VarType -> Bool
prop_is_well_formed_noexcept x = eq_self_strict $ T.is_well_formed x

prop_is_well_formed_noexcept' :: IO Result
prop_is_well_formed_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_well_formed_noexcept

prop_is_at_top_noexcept :: T.Term VarType -> Bool
prop_is_at_top_noexcept x = eq_self_strict $ T.is_at_top x

prop_is_at_top_noexcept' :: IO Result
prop_is_at_top_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_at_top_noexcept

prop_is_ground_noexcept :: T.Term VarType -> Bool
prop_is_ground_noexcept x = eq_self_strict $ T.is_ground x

prop_is_ground_noexcept' :: IO Result
prop_is_ground_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_ground_noexcept

prop_is_type_noexcept :: T.Term VarType -> Bool
prop_is_type_noexcept x = eq_self_strict $ T.is_type x

prop_is_type_noexcept' :: IO Result
prop_is_type_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_type_noexcept

prop_is_var_noexcept :: T.Term VarType -> Bool
prop_is_var_noexcept x = eq_self_strict $ T.is_var x

prop_is_var_noexcept' :: IO Result
prop_is_var_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_var_noexcept

prop_is_metavar_noexcept :: T.Term VarType -> Bool
prop_is_metavar_noexcept x = eq_self_strict $ T.is_var x

prop_is_metavar_noexcept' :: IO Result
prop_is_metavar_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_metavar_noexcept

prop_is_value_noexcept :: T.Term VarType -> Bool
prop_is_value_noexcept x = eq_self_strict $ T.is_var x

prop_is_value_noexcept' :: IO Result
prop_is_value_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_is_value_noexcept

prop_substitute_noexcept ::
     T.Term VarType
  -> T.From
  -> T.Term VarType
  -> T.To
  -> T.Term VarType
  -> Bool
prop_substitute_noexcept s from_ x to_ z =
  eq_self_strict $ T.substitute s from_ x to_ z

prop_substitute_noexcept' :: IO Result
prop_substitute_noexcept' =
  quickCheckWithResult
    stdArgs {maxSuccess = k_pred_noexcept_trials}
    prop_substitute_noexcept

-- [t is value] iff [typeof t is type]
prop_gettype_value_lemma :: T.Term VarType -> Bool
prop_gettype_value_lemma x = T.is_value x <--> (T.gettype x |> is_type)
  where
    is_type (Right a) = T.is_type a
    is_type (Left _) = False

prop_gettype_value_lemma' :: IO Result
prop_gettype_value_lemma' =
  (quickCheckWithResult stdArgs prop_gettype_value_lemma)

-- types can only be substituted with types
prop_type_sub_with_type_lemma ::
     T.Term VarType -> T.Term VarType -> T.Term VarType -> Bool
prop_type_sub_with_type_lemma x var y =
  T.is_var var --> (T.is_type x <--> sub_is_type)
  where
    x' = T.substitute x From var To y
    sub_is_type =
      (case x' of
         Right x'' -> T.is_type x''
         Left _ -> False)

prop_type_sub_with_type_lemma' :: IO Result
prop_type_sub_with_type_lemma' =
  (quickCheckWithResult stdArgs prop_type_sub_with_type_lemma)

-- a = a[x := a]  implies  s[x := a] = s[x := a][x := b]
prop_substitution_lemma1 ::
     T.Term VarType
  -> T.Term VarType
  -> T.Term VarType
  -> T.Term VarType
  -> SimpleFailure
prop_substitution_lemma1 s x a b = result
  where
    (s', x', a', b') = (Right s, Right x, Right a, Right b)
    sub (Right a) (Right b, Right c) = T.substitute a From b To c
    sub _ _ = Left "sub failure"
    sub2 w pair1 pair2 = (w `sub` pair1) `sub` pair2
    replace_once = sub s' (x', a')
    replace_twice = sub2 s' (x', a') (x', b')
    result =
      if replace_once ~~ replace_twice
        then SFSuccess
        else (SFMessage $
              concat [show replace_once ++ "\n" ++ show replace_twice ++ "\n"])

prop_substitution_lemma1' :: IO Result
prop_substitution_lemma1' =
  (quickCheckWithResult stdArgs prop_substitution_lemma1)
     -- ~ T.Term VarType
  -- ~ -> T.Term VarType
  -- ~ -> T.Term VarType
  -- ~ -> T.Term VarType
  -- ~ -> SimpleFailure
     -- ~ T.Term VarType
  -- ~ -> T.Term VarType
  -- ~ -> T.Term VarType
  -- ~ -> T.Term VarType
  -- ~ -> Bool
  -- ~ sub2 s' (x', a') (x', b') == sub2 s' (x', a'') (x', b')
  -- ~ where
    -- ~ (s', x', a', b') = (Right s, Right x, Right a, Right b)
    -- ~ a'' = a' `sub` (x', b')
    -- ~ sub (Right a) (Right b, Right c) = T.substitute a From b To c
    -- ~ sub _ _ = Left "sub failure"
    -- ~ sub2 w pair1 pair2 = (w `sub` pair1) `sub` pair2
  -- ~ (quickCheckWithResult
     -- ~ stdArgs
     -- ~ prop_substitution_lemma1)

-- ~ -- s[x := a][y := b] 
-- ~ prop_substitution_lemma2 ::
-- ~ prop_substitution_lemma2 s x a b
-- ~ -- substitution lemma 1 --- kind of weak but whatever.
-- ~ -- s[x := a][x := b] === s[x := a[x := b]][x := b]
-- ~ prop_substitution_lemma1 ::
-- ~ prop_substitution_lemma1 s x a b =
-- ~ -- no idea why this lemma is failing
-- ~ prop_substitution_lemma1' :: IO Result
-- ~ prop_substitution_lemma1' =
--       { maxSuccess = k_lemma_trials
--       , maxShrinks = k_lemma_max_shrinks
--       , maxDiscardRatio = k_lemma_max_discard_ratio
--       }
main :: IO ()
main = do
  r1 <- prop_gettype_noexcept'
  r2 <- prop_is_well_formed_noexcept'
  r3 <- prop_is_at_top_noexcept'
  r4 <- prop_is_ground_noexcept'
  r5 <- prop_is_type_noexcept'
  r6 <- prop_is_var_noexcept'
  r7 <- prop_is_metavar_noexcept'
  r8 <- prop_is_value_noexcept'
  r9 <- prop_substitute_noexcept'
  r10 <- prop_gettype_value_lemma'
  r11 <- prop_type_sub_with_type_lemma'
  r12 <- prop_substitution_lemma1'
  rs <- return [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]
  (unless (all isSuccess rs) exitFailure)
