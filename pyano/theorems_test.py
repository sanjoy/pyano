from theorems import *
from proof_checker import *
from axioms import *
from formula_helpers import *
from proof_builder import *


def _check_proof(fn, theorem):
    builder = ProofBuilder()
    fn(builder)
    assert_proof_is_valid(builder.proof)
    builder.simplify_proof()
    assert_proof_is_valid(builder.proof)
    builder.assert_proved(theorem)


def test_prove_adding_zero_commutes():
    _check_proof(prove_adding_zero_commutes, "(forall m. ((m + 0) = (0 + m)))")


def test_prove_succ_commutes_with_addition():
    _check_proof(
        prove_succ_commutes_with_addition, "(forall a, b. ((a + S(b)) = (S(a) + b)))"
    )


def test_prove_addition_is_commutative():
    _check_proof(prove_addition_is_commutative, "(forall a, b. ((a + b) = (b + a)))")


def test_prove_one_less_than_two():
    _check_proof(prove_one_less_than_two, "(exists z. ((S(0) + z) = S(S(0))))")
