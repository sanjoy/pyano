from theorems import *
from proof_checker import *
from axioms import *
from formula_helpers import *
from proof_builder import *


def test_prove_adding_zero_commutes():
    builder = ProofBuilder()
    prove_adding_zero_commutes(builder)
    assert_proof_is_valid(builder.proof)
    builder.assert_proved("(forall m. ((m + 0) = (0 + m)))")


def test_prove_succ_commutes_with_addition():
    builder = ProofBuilder()
    prove_succ_commutes_with_addition(builder)
    assert_proof_is_valid(builder.proof)
    builder.assert_proved("(forall a, b. ((a + S(b)) = (S(a) + b)))")


def test_prove_addition_is_commutative():
    builder = ProofBuilder()
    prove_addition_is_commutative(builder)
    assert_proof_is_valid(builder.proof)
    builder.assert_proved("(forall a, b. ((a + b) = (b + a)))")
