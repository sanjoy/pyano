from proof_checker import *
from formula import *
from axioms import *
from formula_helpers import *


def test_proof_basic_0():
    proof = [ForAll("x", Eq(Var("x"), Var("x")))]
    assert_proof_is_valid(proof)


def test_proof_basic_0():
    proof = [ForAll("x", Eq(Var("x"), Var("x"))), ForAll("x", Eq(Var("x"), Zero()))]

    try:
        assert_proof_is_valid(proof)
    except InvalidProofError as ipe:
        assert ipe.invalid_formula_idx == 1
        return

    assert False, "Expected proof verification to fail"


def test_one_plus_one_is_two():
    one = Succ(Zero())
    two = Succ(one)

    theorem = Eq(Add(one, one), two)

    # x + s(y) = s(x + y)
    x_plus_succ_y = get_peano_axiom_x_plus_succ_y()
    # s(0) + s(0) = s(s(0) + 0)
    x_plus_succ_y_subst_ = substitute_forall(x_plus_succ_y, one)
    x_plus_succ_y_subst = substitute_forall(x_plus_succ_y_subst_, Zero())

    # x + 0 = x
    x_plus_zero = get_peano_axiom_x_plus_zero()
    # s(0) + 0 = s(0)
    x_plus_zero_subst = substitute_forall(x_plus_zero, one)

    # s(0) + 0 = s(0) => s(0) + s(0) = s(s(0) + 0) => s(0) + s(0) = s(s(0))
    subst = Implies(x_plus_zero_subst, Implies(x_plus_succ_y_subst, theorem))

    proof = [
        "x + s(y) = s(x + y)",
        x_plus_succ_y,
        "1 + 1 = s(1 + 0)",
        Implies(x_plus_succ_y, x_plus_succ_y_subst_),
        x_plus_succ_y_subst_,
        Implies(x_plus_succ_y_subst_, x_plus_succ_y_subst),
        x_plus_succ_y_subst,
        "x + 0 = x",
        x_plus_zero,
        "1 + 0 = 1",
        Implies(x_plus_zero, x_plus_zero_subst),
        x_plus_zero_subst,
        "((1 + 0) = 1) => ((1 + 1) = s(1 + 0)) => ((1 + 1) = s(1))",
        subst,
        subst.q,
        theorem,
    ]

    assert_proof_is_valid(proof)


def test_one_plus_one_is_two_wrong_proof():
    one = Succ(Zero())
    two = Succ(one)

    theorem = Eq(Add(one, one), two)

    # x + s(y) = s(x + y)
    x_plus_succ_y = get_peano_axiom_x_plus_succ_y()
    # s(0) + s(0) = s(s(0) + 0)
    x_plus_succ_y_subst_ = substitute_forall(x_plus_succ_y, one)

    # BUG: needs to be substitute_forall(x_plus_succ_y_subst_, Zero())
    #
    # As written, `x_plus_succ_y_subst` is saying 1+s(1) = s(1+1)
    x_plus_succ_y_subst = substitute_forall(x_plus_succ_y_subst_, one)

    # x + 0 = x
    x_plus_zero = get_peano_axiom_x_plus_zero()
    # s(0) + 0 = s(0)
    x_plus_zero_subst = substitute_forall(x_plus_zero, one)

    # s(0) + 0 = s(0) => s(0) + s(0) = s(s(0) + 0) => s(0) + s(0) = s(s(0))
    subst = Implies(x_plus_zero_subst, Implies(x_plus_succ_y_subst, theorem))

    proof = [
        "x + s(y) = s(x + y)",
        x_plus_succ_y,
        "1 + 1 = s(1 + 0)",
        Implies(x_plus_succ_y, x_plus_succ_y_subst_),
        x_plus_succ_y_subst_,
        Implies(x_plus_succ_y_subst_, x_plus_succ_y_subst),
        x_plus_succ_y_subst,
        "x + 0 = x",
        x_plus_zero,
        "1 + 0 = 1",
        Implies(x_plus_zero, x_plus_zero_subst),
        x_plus_zero_subst,
        "((1 + 0) = 1) => ((1 + 1) = s(1 + 0)) => ((1 + 1) = s(1))",
        subst,
        subst.q,
        theorem,
    ]

    try:
        assert_proof_is_valid(proof)
    except InvalidProofError as ipe:
        assert ipe.invalid_formula_idx == 13
        return

    assert False, "Expected proof verification to fail"
