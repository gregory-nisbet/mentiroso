{-# LANGUAGE ScopedTypeVariables, DeriveGeneric #-}

-- SUBSTITUTION AND GETTYPE MUST COMMUTE!
-- This is a simple theorem prover written in Haskell
--
-- The inner language consists of (term, type) pairs.
--
-- There is no assumption that terms have a unique or even a principle type,
-- However, it is always possible to get the type for a term.
--
--
-- Given a term it needs to be possible to:
-- 1) get a type. (not necessarily unique or principle type, but *a* type)
-- 2) check whether a (type, term) pair is valid or not
-- 3) construct a fresh term from a type if you have the right axiom
-- there are a few axioms that we insist everyone have.
-- TODO: pick a naming convention to separate type and term-level operations.
-- TODO: okay, terms, types, inference rules, &c are all separate
-- consider unifying them into the same thing.
-- TODO: how to handle bottom?
--
-- In order to support refutation proofs (jargon?) -- right now you are in fact
-- allowed to construct a proof of bottom.
-- TODO: case is really large, find a better way to represent it.
-- TODO: the syntax here is really bad. find a way to make it symbolier.
-- we are introducing a bizarre distinction between "syntactically having a type"
-- and "being verified as a member of that type"
module Typesys where

import qualified GHC.Generics as G
import qualified Generic.Random as R
import Test.QuickCheck as QC

-- A proof system is some extra structure that a type representing terms in
-- some language can carry around with it (aka a typeclass)
--
-- given any term T1 you can construct a new term T2 that is its type.
-- this construction might fail. It is guaranteed to fail if the term is not well-formed.
--
-- getting the type of a term will also fail if the term is at the top of the hierarchy.
-- systems where there's nothing above kinds, for instance, are allowed.
--
-- substitution ... 
-- TODO: predicates for substitution.
--
-- so the problem is that we have two types of variables.
-- one is a Var (which just stands for a generic concrete type).
-- the other is a MetaVar (which stands for an arbitrary expression)
--
-- substitution for a Var only succeeds if the thing we're replacing it with is actually a type.
-- a Var cannot be replaced with 4, for instance.
--
-- However, a MetaVar can indeed be replaced with anything.
-- stupid marker for substitution
data From =
  From
  deriving (Eq, Ord, Show, G.Generic)

instance Arbitrary From where
  arbitrary = return From

data To =
  To
  deriving (Eq, Ord, Show, G.Generic)

instance Arbitrary To where
  arbitrary = return To

-- don't use this yet.
data With =
  With
  deriving (Eq, Ord, Show, G.Generic)

class ProofSystem a where
  gettype :: a -> Either String a
  is_well_formed :: a -> Bool
  is_at_top :: a -> Bool
  is_ground :: a -> Bool
  is_type :: a -> Bool
  is_var :: a -> Bool
  is_metavar :: a -> Bool
  is_value :: a -> Bool
  -- this is just to keep the arguments straight
  substitute :: a -> From -> a -> To -> a -> Either String a

-- potential yagni:
-- change representation to [([k], k, [k])]
-- note: the representation we've picked for the "axiom witness"
-- is self-verifying.
-- primitive tautology, and then additional stuff
-- Γ, B |- B, Δ
-- written as: Constructor of Γ, B, Δ
-- things of the form
-- k type of entire expression
-- this is a list of disjuncts with a dedicated "conflict variable"
-- that appears in the middle.
data PropDisjunct k =
  PropDisjunct [k]
               k
               [k]
  deriving (Eq, Ord, Show, G.Generic)

-- note: this is wrong! only generates singleton lists
instance (QC.Arbitrary k) => QC.Arbitrary (PropDisjunct k) where
  arbitrary = R.genericArbitrary' R.uniform

instance (QC.Arbitrary k) => R.BaseCase (PropDisjunct k) where
  baseCase = (\x -> PropDisjunct [] x []) `fmap` arbitrary

-- a PropAxiom is just an and-ed together list of disjuncts.
-- can't be empty so we use this crazy representation.
-- an empty list of disjuncts or whatever would just be false.
type PropAxiom k = (PropDisjunct k, [PropDisjunct k])

-- this thing can fail ... because the list can be empty, but shouldn't be.
prop_axiom_of_list_exn :: [([k], k, [k])] -> PropAxiom k
prop_axiom_of_list_exn x = f $ to_list $ x
  where
    f [] = error "cannot create PropAxiom of empty list."
    f (x:xs) = (x, xs)
    --
    to_list [] = []
    to_list ((gs, k, ds):xs) = (PropDisjunct gs k ds) : (to_list xs)

-- this is an actual term/type ... the object that we're going to care about
-- for defining the ProofSystem instance
data Term k
  = FromAxiom (PropAxiom (Term k)) -- every axiom has a term in it by fiat.
                            -- this representation does not need to be checked.
  | Func (Term k)
         (Term k) -- function type
  | Bottom -- empty type! useful for negation
  | Var k -- not exactly sure what *kind* of var this is yet. I think we need multiple kinds
  deriving (Eq, Ord, G.Generic)

instance Show k => Show (Term k) where
  show (FromAxiom x) = "FromAxiom (" ++ show x ++ ")"
  show (Func x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"
  show Bottom = "F"
  show (Var k) = "'" ++ show k

instance QC.Arbitrary k => QC.Arbitrary (Term k) where
  arbitrary = R.genericArbitrary' R.uniform

varify :: ([k], k, [k]) -> ([Term k], Term k, [Term k])
varify (gs, k, ds) = (map Var gs, Var k, map Var ds)

prop_axiom_of_var_list_exn :: [([k], k, [k])] -> PropAxiom (Term k)
prop_axiom_of_var_list_exn xs = prop_axiom_of_list_exn (map varify xs)

-- there's some trickiness involving the elements of Γ being
-- reversed. TODO: just store them "reversed" initially in the data structure.
-- might need to be careful here -- or implement some kind of normalization of function
-- signatures or something.
pd_gettype :: PropDisjunct (Term k) -> Term k
pd_gettype (PropDisjunct [] k []) = Func k k -- base case A -> A
-- this case is important to get right. 
pd_gettype (PropDisjunct (g:gs) k []) =
  (Func g (pd_gettype (PropDisjunct gs k [])))
-- if our "alternative conclusions" aren't empty, move them over to the left
-- as negated premises.
pd_gettype (PropDisjunct gs k (d:ds)) =
  pd_gettype (PropDisjunct ((Func d Bottom) : gs) k ds)

term_and :: Term k -> Term k -> Term k
term_and x1 x2 = (n (x1 `func` (n x2)))
  where
    func = Func
    n x = Func x Bottom

prop_axiom_gettype :: PropAxiom (Term k) -> Term k
prop_axiom_gettype (x, xs) = foldl term_and (pd_gettype x) (map pd_gettype xs)

term_gettype :: Term k -> Either String (Term k)
term_gettype (FromAxiom x) = Right $ prop_axiom_gettype x
term_gettype (Func _ _) = Left "Func does not have a type"
term_gettype Bottom = Left "Bottom does not have a type"
term_gettype (Var _) = Left "Var does not have a type"

term_is_well_formed :: Term k -> Bool
term_is_well_formed (FromAxiom _) = True
term_is_well_formed (Func _ _) = True
term_is_well_formed Bottom = True
term_is_well_formed (Var _) = True

term_is_at_top :: Term k -> Bool
term_is_at_top (FromAxiom _) = False
term_is_at_top (Func _ _) = True
term_is_at_top Bottom = True
term_is_at_top (Var _) = True

-- we will need to change this once we introduce metavars
term_is_ground :: Term k -> Bool
term_is_ground (FromAxiom _) = True
term_is_ground (Func _ _) = True
term_is_ground Bottom = True
term_is_ground (Var _) = True

-- A thing created from an axiom is a value, that's important
-- to remember
term_is_type :: Term k -> Bool
term_is_type (FromAxiom _) = False
term_is_type (Func _ _) = True
term_is_type Bottom = True
term_is_type (Var _) = True

-- IsVar literally detects if something is an opaque type
-- (called a var here)
-- only things made with the right constructor are vars.
-- containing vars is not enough to be a var
term_is_var :: Term k -> Bool
term_is_var (Var _) = True
term_is_var _ = False

-- only a metavar is a metavar, it is not enough to
-- contan a metavar.
term_is_metavar :: Term k -> Bool
term_is_metavar _ = False

-- it happens to be mutually exclusive here, but in general
-- values and types are not mutually exclusive!
term_is_value :: Term k -> Bool
term_is_value (FromAxiom _) = True
term_is_value (Func _ _) = False
term_is_value Bottom = False
term_is_value (Var _) = False

pd_substitute ::
     Eq k
  => PropDisjunct (Term k)
  -> From
  -> Term k
  -> To
  -> Term k
  -> Either String (PropDisjunct (Term k))
pd_substitute (PropDisjunct gs k ds) From x To z =
  (case (gs', k', ds') of
     (Right gs'', Right k'', Right ds'') -> Right $ PropDisjunct gs'' k'' ds''
     _ -> Left "cannot perform substitution")
  where
    sub w = term_substitute w From x To z
    gs' = sequence $ [sub g | g <- gs]
    k' = sub k
    ds' = sequence $ [sub d | d <- ds]

pa_substitute ::
     Eq k
  => PropAxiom (Term k)
  -> From
  -> Term k
  -> To
  -> Term k
  -> Either String (PropAxiom (Term k))
pa_substitute (s, ss) from_ x to_ z = out
  where
    first = pd_substitute s from_ x to_ z
    rest = sequence [pd_substitute w from_ x to_ z | w <- ss]
    combined (Right x, Right y) = Right (x, y)
    combined _ = Left "cannot perform substitution"
    out = combined (first, rest)

-- it is potentially a problem if we allow variables to be replaced
-- with expressions containing the same variable.
-- it isn't a problem yet, but it will be once we have binders.
term_substitute ::
     Eq k => Term k -> From -> Term k -> To -> Term k -> Either String (Term k)
term_substitute (Var s) From (Var x) To z
  | s == x = Right $ z
  | otherwise = Right $ Var s
term_substitute (Var s) From (FromAxiom _) To _ =
  Left "FromAxiom is not a subtitution lhs"
term_substitute (Var s) From (Func _ _) To _ =
  Left "Func is not a substitution lhs"
term_substitute (Var s) From Bottom To _ =
  Left "Bottom is not a substitution lhs"
term_substitute (FromAxiom s) From x To z = f s'
  where
    s' = pa_substitute s From x To z
    f (Left s') = Left s'
    f (Right s') = Right (FromAxiom s')
term_substitute (Func a b) From x to z = f (a', b')
  where
    a' = term_substitute a From x To z
    b' = term_substitute b From x To z
    f (Right a', Right b') = Right (Func a' b')
    f _ = Left "substitution failed"
term_substitute Bottom From _ to _ = Right Bottom

-- showing exactly how Terms make a proof system
instance (Eq a) => ProofSystem (Term a) where
  gettype x = term_gettype x
  is_well_formed x = term_is_well_formed x
  is_at_top x = term_is_at_top x
  is_ground x = term_is_ground x
  is_type x = term_is_type x
  is_var x = term_is_var x
  is_metavar x = term_is_metavar x
  is_value x = term_is_value x
  substitute s From x To z = term_substitute s From x To z
