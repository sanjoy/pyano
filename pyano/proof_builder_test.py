from proof_builder import *


def test_forallxy_split():
    v = get_cached_vars()
    builder = ProofBuilder()
    builder.forall_split("med", builder.prove_eq_is_symmetric())
    builder.assert_proved("(forall x, y. (x = y)) => (forall x, y. (y = x))")
    assert_proof_is_valid(builder.proof)


def test_forallxyz_split():
    v = get_cached_vars()
    builder = ProofBuilder()
    builder.forall_split("med", builder.prove_eq_is_transitive())
    builder.assert_proved(
        "(forall x, y, z. (x = y)) => (forall x, y, z. (y = z) => (x = z))"
    )
    assert_proof_is_valid(builder.proof)


def test_prove_eq_is_symmetric():
    builder = ProofBuilder()
    builder.prove_eq_is_symmetric()
    builder.assert_proved("(forall x, y. (x = y) => (y = x))")
    assert_proof_is_valid(builder.proof)


def test_extract_and_prove_inner_consequent():
    v = get_cached_vars()
    builder = ProofBuilder()
    example = foralld(Implies(Eq(v.d, v.d), forallf(Eq(v.d, v.d))))
    builder.p(example)
    builder.p(foralld(Eq(v.d, v.d)))
    builder.forall_split("high", example)
    builder.assert_proved("(forall d, f. (d = d))")
    assert_proof_is_valid(builder.proof)


def test_flip_equality():
    v = get_cached_vars()
    builder = ProofBuilder()
    eq = builder.peano_axiom_x_plus_zero()
    assert str(eq) == "(forall x. ((x + 0) = x))"
    builder.flip_equality(eq)
    builder.assert_proved("(forall x. (x = (x + 0)))")
    assert_proof_is_valid(builder.proof)


def test_prove_eq_is_transitive():
    builder = ProofBuilder()
    builder.prove_eq_is_transitive()
    builder.assert_proved("(forall x, y, z. (x = y) => (y = z) => (x = z))")
    assert_proof_is_valid(builder.proof)


def test_prove_values_transitively_equal():
    v = get_cached_vars()
    builder = ProofBuilder()

    a = lambda x: Succ(x)
    b = lambda x: Add(x, v.i1)
    c = lambda x: Add(v.i1, x)

    builder.prove_values_transitively_equal(a, b, c)
    builder.assert_proved(
        "(forall m. (S(m) = (m + S(0))) => ((m + S(0)) = (S(0) + m)) => (S(m) = (S(0) + m)))"
    )
    assert_proof_is_valid(builder.proof)


def test_flip_xy_order_in_forall():
    builder = ProofBuilder()
    builder.flip_xy_order_in_forall(builder.peano_axiom_x_plus_succ_y())
    builder.assert_proved("(forall a, b. ((b + S(a)) = S((b + a))))")
    assert_proof_is_valid(builder.proof)


def test_apply_fn_on_eq():
    builder = ProofBuilder()
    builder.peano_axiom_x_plus_zero()
    builder.apply_fn_on_eq(Succ)
    builder.assert_proved("(forall x. (S((x + 0)) = S(x)))")
    assert_proof_is_valid(builder.proof)


def test_printing_proof():
    builder = ProofBuilder()
    builder.peano_axiom_x_plus_zero()
    builder.apply_fn_on_eq(Succ)
    assert_proof_is_valid(builder.proof)
    proof_str = """
0. (forall x. ((x + 0) = x))
1. (forall x. (S((x + 0)) = S((x + 0))))
2. (forall x. ((x + 0) = x) => (S((x + 0)) = S((x + 0))) => (S((x + 0)) = S(x)))
3. (forall x. ((x + 0) = x) => (S((x + 0)) = S((x + 0))) => (S((x + 0)) = S(x))) => (forall x. ((x + 0) = x)) => (forall x. (S((x + 0)) = S((x + 0))) => (S((x + 0)) = S(x)))
4. (forall x. ((x + 0) = x)) => (forall x. (S((x + 0)) = S((x + 0))) => (S((x + 0)) = S(x)))
5. (forall x. (S((x + 0)) = S((x + 0))) => (S((x + 0)) = S(x)))
6. (forall x. (S((x + 0)) = S((x + 0))) => (S((x + 0)) = S(x))) => (forall x. (S((x + 0)) = S((x + 0)))) => (forall x. (S((x + 0)) = S(x)))
7. (forall x. (S((x + 0)) = S((x + 0)))) => (forall x. (S((x + 0)) = S(x)))
8. (forall x. (S((x + 0)) = S(x)))"""
    assert str(builder) == proof_str[1:]


def test_simplify_proof():
    builder = ProofBuilder()
    builder.peano_axiom_x_plus_zero()
    builder.peano_axiom_x_plus_zero()
    builder.assert_proved("(forall x. ((x + 0) = x))")
    assert len(builder.proof) == 2
    saved = builder.simplify_proof()
    assert saved == 1
    assert len(builder.proof) == 1
