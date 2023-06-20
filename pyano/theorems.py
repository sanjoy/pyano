from proof_checker import *
from formula import *
from axioms import *
from formula_helpers import *
from proof_builder import *

import inspect
import os


def prove_adding_zero_commutes(b):
    """Proves (f x. x+0=0+x)"""

    v = get_cached_vars()
    p = b.p

    # First prove 0+x=x, by induction
    base_case = b.subst_forall_with_const(b.peano_axiom_x_plus_zero(), v.Z)

    b.subst_forall_with_const(b.peano_axiom_x_plus_succ_y(), v.Z)
    b.assert_proved("(forall y. ((0 + S(y)) = S((0 + y))))")

    A = Eq(Add(v.Z, v.x), v.x)
    B = Eq(Add(v.Z, v.sx), Succ(Add(v.Z, v.x)))
    C = Eq(Add(v.Z, v.sx), v.sx)

    p(forallx(ImpliesN(A, B, C)))

    p(
        forallx(
            Implies(
                ImpliesN(A, B, C),
                ImpliesN(B, A, C),
            )
        )
    )

    b.forall_split()
    inductive_step = b.forall_split()
    b.assert_proved("(forall x. ((0 + x) = x) => ((0 + S(x)) = S(x)))")

    p(gen_induction_axiom("x", Eq(Add(v.Z, v.x), v.x)))

    b.immediately_implies(base_case, inductive_step, And(base_case, inductive_step))
    p(forallx(Eq(Add(v.Z, v.x), v.x)))

    b.assert_proved("(forall x. ((0 + x) = x))")

    b.flip_equality()
    p(forallx(Eq(v.x, Add(v.Z, v.x))))

    b.assert_proved("(forall x. (x = (0 + x)))")

    b.peano_axiom_x_plus_zero()
    b.prove_values_transitively_equal(
        lambda x: Add(x, v.Z), lambda x: x, lambda x: Add(v.Z, x)
    )
    b.assert_proved("(forall m. ((m + 0) = m) => (m = (0 + m)) => ((m + 0) = (0 + m)))")

    b.forall_split()
    b.forall_split()

    b.assert_proved("(forall m. ((m + 0) = (0 + m)))")


def prove_succ_commutes_with_addition(b):
    # forall m, n. m + S(n) = S(m) + n

    # Let's first prove forall m, n. n + S(m) = S(n) + m since that makes the induction
    # easier.  After that we can just flip m & n.

    v = get_cached_vars()
    p = b.p

    # Proof by induction on m.
    # Base case: n + S(0) = S(n) + 0

    b.peano_axiom_x_plus_succ_y()
    b.flip_xy_order_in_forall()
    b.subst_forall_with_const(b.last_formula, v.Z)
    b.assert_proved("(forall b. ((b + S(0)) = S((b + 0))))")

    b.peano_axiom_x_plus_zero()
    b.apply_fn_on_eq(Succ)
    b.assert_proved("(forall x. (S((x + 0)) = S(x)))")

    b.prove_values_transitively_equal(
        lambda x: Add(x, v.i1), lambda x: Succ(Add(x, v.Z)), Succ
    )
    b.forall_split()
    b.forall_split()
    b.assert_proved("(forall m. ((m + S(0)) = S(m)))")

    b.subst_forall_with_expr(b.peano_axiom_x_plus_zero(), Succ)
    b.flip_equality()
    b.assert_proved("(forall t. (S(t) = (S(t) + 0)))")

    b.prove_values_transitively_equal(
        lambda x: Add(x, v.i1), Succ, lambda x: Add(Succ(x), v.Z)
    )
    b.forall_split()
    base = b.forall_split()
    b.assert_proved("(forall m. ((m + S(0)) = (S(m) + 0)))")

    # Inductive case: (n + S(m) = S(n) + m) => (n + S(S(m)) = S(n) + S(m))

    # Axioms
    # x+0=x
    # x+sy=s(x+y)
    #
    # n+sm=sn+m => n+ssm=sn+sm
    #
    #               P_B (needs inductive step)
    #            vvvvvvvvv
    # n+ssm = s(n+sm)=s(sn+m)=sn+sm
    #  ^^^^^^^^^^        ^^^^^^^^^
    #    P_A                P_C
    #
    # fmn. n+sm=sn+m => s(n+sm)=s(sn+m)  == X
    # fmn. n+ssm=s(n+sm)                 == Y
    # fmn. s(sn+m)=sn+sm                 == Z
    #
    # fmn. (n+sm=sn+m => s(n+sm)=s(n+sm) => s(n+sm)=s(sn+m))
    # fmn. ((n+sm=sn+m => s(n+sm)=s(n+sm) => s(n+sm)=s(sn+m)) => (s(n+sm)=s(n+sm) => n+sm=sn+m => s(n+sm)=s(sn+m)))
    # fmn. (n+sm=sn+m => s(n+sm)=s(n+sm) => s(n+sm)=s(sn+m))  => fmn. (s(n+sm)=s(n+sm) => n+sm=sn+m => s(n+sm)=s(sn+m))
    # fmn. (s(n+sm)=s(n+sm) => n+sm=sn+m => s(n+sm)=s(sn+m))
    # fmn. (s(n+sm)=s(n+sm)) => fmn. (n+sm=sn+m => s(n+sm)=s(sn+m))
    # fmn. (s(n+sm)=s(n+sm))
    # fmn. (n+sm=sn+m => s(n+sm)=s(sn+m)) == X

    # fmn. (s(n+sm)=n+ssm => (n+sm=sn+m => s(n+sm)=s(sn+m)) => (n+sm=sn+m => n+ssm=s(sn+m)))
    # fmn. (s(n+sm)=n+ssm) => fmn. ((n+sm=sn+m => s(n+sm)=s(sn+m)) => (n+sm=sn+m => n+ssm=s(sn+m)))
    # fmn. ((n+sm=sn+m => s(n+sm)=s(sn+m)) => (n+sm=sn+m => n+ssm=s(sn+m)))
    # fmn. ((n+sm=sn+m => s(n+sm)=s(sn+m))) => fmn. ((n+sm=sn+m => n+ssm=s(sn+m)))
    # fmn. (n+sm=sn+m => n+ssm=s(sn+m))

    # fmn. (s(sn+m)=sn+sm => ((n+sm=sn+m => n+ssm=s(sn+m))) => ((n+sm=sn+m => n+ssm=sn+sm)))
    # fmn. (s(sn+m)=sn+sm) => fmn. (((n+sm=sn+m => n+ssm=s(sn+m))) => ((n+sm=sn+m => n+ssm=sn+sm)))
    # fmn. (((n+sm=sn+m => n+ssm=s(sn+m))) => ((n+sm=sn+m => n+ssm=sn+sm)))
    # fmn. ((n+sm=sn+m => n+ssm=s(sn+m))) => fmn. ((n+sm=sn+m => n+ssm=sn+sm))
    # fmn. ((n+sm=sn+m => n+ssm=sn+sm)) == inductive step

    b.peano_axiom_x_plus_succ_y()

    A = Eq(Add(v.n, v.sm), Add(v.sn, v.m))
    B = Eq(Succ(Add(v.n, v.sm)), Succ(Add(v.n, v.sm)))
    C = Eq(Succ(Add(v.n, v.sm)), Succ(Add(v.sn, v.m)))

    p(forallmn(B))
    p(forallmn(ImpliesN(A, B, C)))
    p(forallmn(Implies(ImpliesN(A, B, C), ImpliesN(B, A, C))))
    b.forall_split()
    p(forallmn(ImpliesN(B, A, C)))
    ind = b.forall_split()
    b.assert_proved(
        "(forall m, n. ((n + S(m)) = (S(n) + m)) => (S((n + S(m))) = S((S(n) + m))))"
    )

    b.peano_axiom_x_plus_succ_y()
    b.flip_xy_order_in_forall()
    b.subst_forall_with_expr(b.last_formula, Succ)
    b.flip_equality()

    b.assert_proved("(forall t, b. (S((b + S(t))) = (b + S(S(t)))))")

    p(
        forallmn(
            ImpliesN(
                Eq(Succ(Add(v.n, v.sm)), Add(v.n, Succ(v.sm))),
                ind.body.body,
                Implies(
                    Eq(Add(v.n, v.sm), Add(v.sn, v.m)),
                    Eq(Add(v.n, Succ(v.sm)), Succ(Add(v.sn, v.m))),
                ),
            )
        )
    )

    b.forall_split()
    ind = b.forall_split()

    b.assert_proved(
        "(forall m, n. ((n + S(m)) = (S(n) + m)) => ((n + S(S(m))) = S((S(n) + m))))"
    )

    b.peano_axiom_x_plus_succ_y()
    b.subst_forall_with_expr(b.last_formula, Succ)
    b.flip_equality()
    b.rename_forall_quantifier("x")
    b.flip_xy_order_in_forall()

    p(
        forallmn(
            ImpliesN(
                Eq(Succ(Add(v.sn, v.m)), Add(v.sn, v.sm)),
                ind.body.body,
                Implies(
                    Eq(Add(v.n, v.sm), Add(v.sn, v.m)),
                    Eq(Add(v.n, Succ(v.sm)), Add(v.sn, v.sm)),
                ),
            )
        )
    )
    b.forall_split()
    ind = b.forall_split()

    b.assert_proved(
        "(forall m, n. ((n + S(m)) = (S(n) + m)) => ((n + S(S(m))) = (S(n) + S(m))))"
    )

    p(
        forallm(
            Implies(
                foralln(
                    Implies(
                        Eq(Add(v.n, v.sm), Add(v.sn, v.m)),
                        Eq(Add(v.n, Succ(v.sm)), Add(v.sn, v.sm)),
                    )
                ),
                Implies(
                    foralln(Eq(Add(v.n, v.sm), Add(v.sn, v.m))),
                    foralln(Eq(Add(v.n, Succ(v.sm)), Add(v.sn, v.sm))),
                ),
            )
        )
    )

    ind = b.forall_split()

    b.immediately_implies(base, ind, And(base, ind))

    p(gen_induction_axiom("x", forally(Eq(Add(v.y, v.sx), Add(v.sy, v.x)))))
    p(forallxy(Eq(Add(v.y, v.sx), Add(v.sy, v.x))))
    b.flip_xy_order_in_forall()

    b.assert_proved("(forall a, b. ((a + S(b)) = (S(a) + b)))")


def prove_addition_is_commutative(b):
    v = get_cached_vars()
    p = b.p

    # forall mn. m+n=n+m
    #
    # Let's first prove f mn. n+m=m+n
    #
    # Proof by induction; x+0=0+x already proved above.
    #
    # n+sm=s(n+m)=s(m+n)=m+sn=sm+n
    #
    # fmn. n+m=m+n => s(n+m)=s(n+m) => s(n+m)=s(m+n)
    # fmn. (n+m=m+n => s(n+m)=s(n+m) => s(n+m)=s(m+n)) => (s(n+m)=s(n+m) => n+m=m+n => s(n+m)=s(m+n))
    # fmn. (s(n+m)=s(n+m) => n+m=m+n => s(n+m)=s(m+n))
    # fmn. (s(n+m)=s(n+m)
    # fmn. n+m=m+n => s(n+m)=s(m+n)
    #
    # fmn. s(n+m)=n+sm => (n+m=m+n => s(n+m)=s(m+n)) => (n+m=m+n => n+sm=s(m+n))
    # forall_split() x 2
    # fmn. n+m=m+n => n+sm=s(m+n)
    #
    # fmn. s(m+n)=m+sn => (n+m=m+n => n+sm=s(m+n) => (n+m=m+n => n+sm=m+sn)
    # forall_split() x 2
    # fmn. n+m=m+n => n+sm=m+sn
    #
    # fmn. m+sn=sm+n => (n+m=m+n => n+sm=m+sn) => (n+m=m+n => n+sm=sm+n)
    # forall_split() x 2
    # fmn. n+m=m+n => n+sm=sm+n

    A = Eq(Add(v.n, v.m), Add(v.m, v.n))
    B = Eq(Succ(Add(v.n, v.m)), Succ(Add(v.n, v.m)))
    C = Eq(Succ(Add(v.n, v.m)), Succ(Add(v.m, v.n)))

    p(forallmn(B))
    p(forallmn(ImpliesN(A, B, C)))
    p(forallmn(Implies(ImpliesN(A, B, C), ImpliesN(B, A, C))))
    b.forall_split()
    p(forallmn(ImpliesN(B, A, C)))
    ind = b.forall_split()
    b.assert_proved("(forall m, n. ((n + m) = (m + n)) => (S((n + m)) = S((m + n))))")

    b.peano_axiom_x_plus_succ_y()
    b.flip_xy_order_in_forall()
    b.flip_equality()

    p(
        forallmn(
            ImpliesN(
                Eq(Succ(Add(v.n, v.m)), Add(v.n, v.sm)),
                ind.body.body,
                Implies(
                    Eq(Add(v.n, v.m), Add(v.m, v.n)),
                    Eq(Add(v.n, v.sm), Succ(Add(v.m, v.n))),
                ),
            )
        )
    )
    b.forall_split()
    ind = b.forall_split()

    b.peano_axiom_x_plus_succ_y()
    b.flip_equality()

    p(
        forallmn(
            ImpliesN(
                Eq(Succ(Add(v.m, v.n)), Add(v.m, v.sn)),
                ind.body.body,
                Implies(
                    Eq(Add(v.n, v.m), Add(v.m, v.n)),
                    Eq(Add(v.n, v.sm), Add(v.m, v.sn)),
                ),
            )
        )
    )
    b.forall_split()
    ind = b.forall_split()

    prove_succ_commutes_with_addition(b)

    p(
        forallmn(
            ImpliesN(
                Eq(Add(v.m, v.sn), Add(v.sm, v.n)),
                ind.body.body,
                Implies(
                    Eq(Add(v.n, v.m), Add(v.m, v.n)),
                    Eq(Add(v.n, v.sm), Add(v.sm, v.n)),
                ),
            )
        )
    )
    b.forall_split()
    b.forall_split()

    p(
        forallm(
            Implies(
                foralln(
                    Implies(
                        Eq(Add(v.n, v.m), Add(v.m, v.n)),
                        Eq(Add(v.n, v.sm), Add(v.sm, v.n)),
                    )
                ),
                Implies(
                    foralln(Eq(Add(v.n, v.m), Add(v.m, v.n))),
                    foralln(Eq(Add(v.n, v.sm), Add(v.sm, v.n))),
                ),
            )
        )
    )

    ind = b.forall_split()

    prove_adding_zero_commutes(b)
    base = b.last_formula

    b.immediately_implies(base, ind, And(base, ind))

    p(gen_induction_axiom("m", foralln(Eq(Add(v.n, v.m), Add(v.m, v.n)))))
    p(forallmn(Eq(Add(v.n, v.m), Add(v.m, v.n))))
    b.flip_xy_order_in_forall()


def prove_one_less_than_two(b):
    p = b.p
    v = get_cached_vars()

    theorem = LessThan(v.i1, v.i2)

    two_eq_two = Eq(v.i2, v.i2)

    p(forallx(Eq(v.x, v.x)))
    b.immediately_implies(two_eq_two)

    p(ImpliesN(two_eq_two, Implies(theorem.x, Not(two_eq_two)), theorem))
    p(ImpliesN(Implies(theorem.x, Not(two_eq_two)), theorem))
    p(Implies(theorem.x, Not(Eq(Add(v.i1, v.i1), v.i2))))

    # Now all we need to do is show 1+1=2 and we'll have the proof.

    b.immediately_implies(
        b.peano_axiom_x_plus_succ_y(),
        forallx(Eq(Add(v.i1, v.sx), Succ(Add(v.i1, v.x)))),
    )
    one_plus_1_eq_succ_1_plus_0 = b.immediately_implies(
        b.last_formula, Eq(Add(v.i1, v.i1), Succ(Add(v.i1, v.Z)))
    )

    one_plus_0_eq_1 = b.immediately_implies(
        b.peano_axiom_x_plus_zero(), Eq(Add(v.i1, v.Z), v.i1)
    )
    one_plus_1_eq_2 = b.immediately_implies(
        one_plus_0_eq_1, one_plus_1_eq_succ_1_plus_0, Eq(Add(v.i1, v.i1), v.i2)
    )

    b.immediately_implies(
        one_plus_1_eq_2,
        Implies(theorem.x, Not(Eq(Add(v.i1, v.i1), v.i2))),
        Implies(theorem.x, Not(Eq(v.i2, v.i2))),
    )
    p(theorem)


def _export_proofs(root_dir):
    if not os.path.exists(root_dir):
        os.makedirs(root_dir)

    for func_name, func in globals().items():
        if func_name.startswith("prove_"):
            proof_name = func_name[len("prove_") :]
            with open(f"{root_dir}/{proof_name}.proof", "w") as f:
                builder = ProofBuilder()
                func(builder)
                formulae_removed = builder.simplify_proof()
                print(
                    f"Optimizations removed {formulae_removed} formulae from {proof_name}."
                )
                assert_proof_is_valid(builder.proof)
                f.write(str(builder))
            print(f"Wrote {root_dir}/{proof_name}.proof")


def main():
    _export_proofs(f"{os.getcwd()}/proved_theorems")


if __name__ == "__main__":
    main()
