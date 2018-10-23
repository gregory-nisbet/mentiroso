import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import qualified Typesys as T

(|>) :: a -> (a -> b) -> b
(|>) x f = f x

main = defaultMain unitTests

unitTests =
  testGroup
    "Notation"
    [inflate_type1, inflate_type2, inflate_type3, inflate_type4, inflate_type5]

-- a clause with just a type and its negation gets desugared in the obvious way.
inflate_type1 =
  testCase "'1 |- '1  -->  '1 -> '1" $
  assertEqual
    []
    "('1 -> '1)"
    ([([], 1, [])] |> T.prop_axiom_of_var_list_exn |> T.prop_axiom_gettype |>
     show)

-- an extra premise becomes an argument right outside the main identity function.
inflate_type2 =
  testCase "'2, '1 |- '1  -->  '2 -> ('1 -> '1)" $
  assertEqual
    []
    "('2 -> ('1 -> '1))"
    ([([2], 1, [])] |> T.prop_axiom_of_var_list_exn |> T.prop_axiom_gettype |>
     show)

-- an alternative conclusion becomes a negated premise.
inflate_type3 =
  testCase "'1 |- '1, '9  -->  (('9 -> F) -> ('1 -> '1))" $
  assertEqual
    []
    "(('9 -> F) -> ('1 -> '1))"
    ([([], 1, [9])] |> T.prop_axiom_of_var_list_exn |> T.prop_axiom_gettype |>
     show)

-- conjunction of primitive sequents becomes "and".
inflate_type4 =
  testCase
    "'1 |- '1  and  '7 |- '7  -->  ((('1 -> '1) -> (('7 -> '7) -> F)) -> F)" $
  assertEqual
    []
    "((('1 -> '1) -> (('7 -> '7) -> F)) -> F)"
    ([([], 1, []), ([], 7, [])] |> T.prop_axiom_of_var_list_exn |>
     T.prop_axiom_gettype |>
     show)

inflate_type5 =
  testCase "'1, '2, '3 |- '3, '4, '5  and  '6, '7, '8 |- '8, '9, '0" $
  assertEqual
    []
    "(((('5 -> F) -> (('4 -> F) -> ('1 -> ('2 -> ('3 -> '3))))) -> ((('0 -> F) -> (('9 -> F) -> ('6 -> ('7 -> ('8 -> '8))))) -> F)) -> F)"
    ([([1, 2], 3, [4, 5]), ([6, 7], 8, [9, 0])] |> T.prop_axiom_of_var_list_exn |>
     T.prop_axiom_gettype |>
     show)
