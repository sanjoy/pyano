from theorems import *
from proof_checker import *
from axioms import *
from formula_helpers import *
from proof_builder import *


import subprocess


def _check_proof(fn, theorem):
    builder = ProofBuilder()
    fn(builder)
    assert_proof_is_valid(builder.proof)
    builder.simplify_proof()
    assert_proof_is_valid(builder.proof)
    builder.assert_proved(theorem)


def _get_git_root_dir():
    git_cmd = ["git", "rev-parse", "--show-toplevel"]
    return subprocess.run(git_cmd, capture_output=True, text=True).stdout.strip()


def test_prove_adding_zero_commutes():
    _check_proof(prove_adding_zero_commutes, "(forall m. ((m + 0) = (0 + m)))")


def test_prove_succ_commutes_with_addition():
    _check_proof(
        prove_succ_commutes_with_addition, "(forall a, b. ((a + S(b)) = (S(a) + b)))"
    )


def test_prove_addition_is_commutative():
    _check_proof(prove_addition_is_commutative, "(forall a, b. ((a + b) = (b + a)))")


def test_prove_one_less_than_or_eq_two():
    _check_proof(prove_one_less_than_or_eq_two, "(exists z. ((S(0) + z) = S(S(0))))")


def test_exported_proofs():
    assert_exported_proofs_match(f"{_get_git_root_dir()}/pyano/proved_theorems")
