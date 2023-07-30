from proof_checker import *
from formula import *
from axioms import *
from formula_helpers import *


class ProofBuilder:
    """`ProofBuilder` is a stateful helper for constructing formal proofs."""

    def __init__(self, check_each_step=False):
        self._proof = []
        self._proved_eq_is_symmetric = False
        self._proved_eq_is_transitive = False
        self._check_each_step = check_each_step

    def p(self, formula):
        self._proof.append(formula)
        if self._check_each_step:
            assert_proof_is_valid(self._proof)
        return formula

    def simplify_proof(self):
        """Removes redundant formulae from the proof.  Returns the number of such formulae
        removed.

        """
        formulae = set()
        new_proof = []
        for p in self.proof:
            if p not in formulae:
                new_proof.append(p)
                formulae.add(p)
        formulae_removed = len(self._proof) - len(new_proof)
        self._proof = new_proof
        return formulae_removed

    @property
    def proof(self):
        return self._proof

    def __str__(self):
        fs = []
        for i, p in enumerate(self.proof):
            fs.append(f"{i}. {p}")
        return "\n".join(fs)

    @property
    def last_formula(self):
        for p in self.proof[::-1]:
            if isinstance(p, Formula):
                return p
        return None

    def assert_proved(self, formula):
        """Asserts that last statement in the proof is `formula`.

        Note that this doesn't actually assert that the proof so far is correct.  That
        will be established when the entire proof is checked.

        """

        assert isinstance(formula, str) or isinstance(formula, Formula)
        if isinstance(formula, str):
            assert (
                str(self.last_formula) == formula
            ), f"proved: {str(self.last_formula)}; expected: {formula}"
        else:
            assert (
                self.last_formula == formula
            ), f"proved: {str(self.last_formula)}; expected: {formula}"

    def _forallx_split(self, forall):
        p = self.p

        def _forallx(body):
            return ForAll(forall.var, body)

        return p(
            ImpliesN(
                forall,
                _forallx(forall.body.p),
                _forallx(forall.body.q),
            )
        )

    def _forallxy_split(self, forall):
        def _forallx(body):
            return ForAll(forall.var, body)

        def _forally(body):
            return ForAll(forall.body.var, body)

        def _forallxy(body):
            return _forallx(_forally(body))

        p = self.p

        P = forall.body.body.p
        Q = forall.body.body.q

        A = forall
        B = _forallxy(P)
        C = _forallxy(Q)
        D = _forallx(ImpliesN(_forally(ImpliesN(P, Q)), _forally(P), _forally(Q)))
        E = _forallx(ImpliesN(_forally(P), _forally(Q)))

        A_B_C = ImpliesN(A, B, C)

        p(D)
        p(ImpliesN(D, A, E))
        A_E = p(ImpliesN(A, E))
        E_B_C = p(ImpliesN(E, B, C))
        return self.immediately_implies(A_E, E_B_C, A_B_C)

    def _forallxyz_split(self, forall):
        p = self.p

        def _forallx(body):
            return ForAll(forall.var, body)

        def _forally(body):
            return ForAll(forall.body.var, body)

        def _forallz(body):
            return ForAll(forall.body.body.var, body)

        def _forallxy(body):
            return _forallx(_forally(body))

        def _forallxyz(body):
            return _forallx(_forally(_forallz(body)))

        P = forall.body.body.body.p
        Q = forall.body.body.body.q

        A = forall
        B = _forallxyz(P)
        C = _forallxyz(Q)
        A_B_C = ImpliesN(A, B, C)
        B_C = ImpliesN(B, C)

        FZ_P_Q = forallz(Implies(P, Q))
        FZ_P_FZ_Q = Implies(forallz(P), forallz(Q))
        assert forallxy(FZ_P_Q) == A

        p(forallxy(Implies(FZ_P_Q, FZ_P_FZ_Q)))

        X = self.forall_split()
        self.assert_proved(forallxy(FZ_P_FZ_Q))

        Y = self.forall_split("med")
        self.assert_proved(Implies(_forallxyz(P), _forallxyz(Q)))

        return self.immediately_implies(X, Y, A_B_C)

    def forall_split(self, resolution_level="high", forall=None):
        """From "forall x. P(x) => Q(x)" do one of three things depending on the value of
        `resolution_level`:

        1. If it is `"high"` then prove "forall x. Q(x)".  Assumes forall x. P(x) has
           been proved.
        2. If it is `"med"` then prove "forall x. P(x) => forall x. Q(x)".  Assumes
           "forall x. P(x) => Q(x)" has been proved already.
        3. If it is `"low"` then prove "(forall x. P(x) => Q(x)) => (forall x. P(x) =>
           forall x. Q(x))".

        Also works for two and three quantifiers.  Note that (3) is an axiom for a
        single quantifier (so trivial to prove) but requires a bit of work when there
        are multiple quantifiers.
        """

        if forall is None:
            forall = self.last_formula

        p = self.p

        num_level = 0
        i = forall
        while isinstance(i, ForAll):
            i = i.body
            num_level = num_level + 1

        assert num_level in [1, 2, 3], f"num_level = {num_level} not supported!"
        assert resolution_level in [
            "low",
            "med",
            "high",
        ], f"resolution_level = {resolution_level}"

        if num_level == 1:
            prop = self._forallx_split(forall)
        elif num_level == 2:
            prop = self._forallxy_split(forall)
        else:
            prop = self._forallxyz_split(forall)

        if resolution_level == "low":
            return self.last_formula

        p(prop.q)

        if resolution_level == "med":
            return self.last_formula

        return p(prop.q.q)

    def prove_eq_is_symmetric(self):
        """Proves f xy. (x=y => y=x)"""

        if self._proved_eq_is_symmetric:
            return

        self._proved_eq_is_symmetric = True

        v = get_cached_vars()
        p = self.p

        theorem = forallxy(Implies(Eq(v.x, v.y), Eq(v.y, v.x)))

        X_X = Eq(v.x, v.x)
        X_Y = Eq(v.x, v.y)
        Y_X = Eq(v.y, v.x)

        p(
            forallxy(
                Implies(
                    ImpliesN(X_Y, X_X, Y_X),
                    ImpliesN(X_X, X_Y, Y_X),
                )
            )
        )

        self.forall_split("med")
        p(forallxy(ImpliesN(X_Y, X_X, Y_X)))  # Subst axiom
        p(forallxy(ImpliesN(X_X, X_Y, Y_X)))

        self.forall_split("med")
        p(forallyx(X_X))
        self.flip_xy_order_in_forall()
        return p(theorem)

    def immediately_implies(self, *formulae):
        """`immediately_implies(A, B, C, ...)` first adds `A->B->C->...` to the proof then
        `B->C->...` and then `C->...` and so on.

        This is useful when A, B, C, ... have been proved already and the `A->B->C->...`
        implication is an axiom.

        """
        if len(formulae) == 1:
            formulae = (self.last_formula,) + formulae

        self.p(ImpliesN(*formulae))
        if len(formulae) > 2:
            return self.immediately_implies(*formulae[1:])
        else:
            return self.p(formulae[1])

    def flip_equality(self, eq=None):
        """Given a proven formula for "forall x. F(x) = G(x)" proves "forall x. G(x) = F(x)." """

        if eq is None:
            eq = self.last_formula

        v = get_cached_vars()
        p = self.p

        varlist = []
        i = eq
        while isinstance(i, ForAll):
            varlist.append(i.var)
            i = i.body

        F = i.a
        G = i.b

        assert len(varlist) > 0

        def _forall(body):
            return ForAllN(varlist, body)

        available_vars = sorted(list(set(string.ascii_lowercase) - set(varlist)))

        vx = Var(available_vars[0])
        vy = Var(available_vars[1])

        def _forallxy(body):
            return ForAllN([vx.name, vy.name], body)

        self.prove_eq_is_symmetric()

        symmetric_axiom = p(_forallxy(Implies(Eq(vx, vy), Eq(vy, vx))))

        wrapped_symmetric_axiom = symmetric_axiom
        for v in varlist[::-1]:
            wrapped_symmetric_axiom = ForAll(v, wrapped_symmetric_axiom)
            self.immediately_implies(
                wrapped_symmetric_axiom.body, wrapped_symmetric_axiom
            )

        subst_F = substitute_forall(symmetric_axiom, F)
        subst_FG = substitute_forall(subst_F, G)

        p(_forall(Implies(symmetric_axiom, subst_F)))
        self.forall_split()

        p(_forall(Implies(subst_F, subst_FG)))
        self.forall_split()
        return self.forall_split()

    def prove_eq_is_transitive(self):
        """Proves forall x, y, z: x = y => y = z => x = z"""
        if self._proved_eq_is_transitive:
            return

        self._proved_eq_is_transitive = True

        v = get_cached_vars()
        p = self.p

        X_Y = Eq(v.x, v.y)
        Y_Z = Eq(v.y, v.z)
        X_Z = Eq(v.x, v.z)

        theorem = forallxyz(ImpliesN(X_Y, Y_Z, X_Z))

        P = ImpliesN(Y_Z, X_Y, X_Z)
        Q = ImpliesN(X_Y, Y_Z, X_Z)

        assert forallxyz(Q) == theorem

        p(forallxyz(P))
        p(forallxyz(Implies(P, Q)))
        return self.forall_split()

    def _prove_values_transitively_equal_1arg(self, a, b, c):
        v = get_cached_vars()
        p = self.p

        self.prove_eq_is_transitive()

        def body(x, y, z):
            return ImpliesN(Eq(x, y), Eq(y, z), Eq(x, z))

        eq_transitive = forallxyz(body(v.x, v.y, v.z))
        eq_transitive_m = forallm(eq_transitive)
        self.immediately_implies(eq_transitive, eq_transitive_m)

        A = a(v.m)
        B = b(v.m)
        C = c(v.m)

        theorem = forallm(body(A, B, C))

        p(forallm(Implies(eq_transitive, forallyz(body(A, v.y, v.z)))))

        self.immediately_implies(
            self.last_formula, eq_transitive_m, forallm(forallyz(body(A, v.y, v.z)))
        )

        p(forallm(Implies(forallyz(body(A, v.y, v.z)), forallz(body(A, B, v.z)))))
        self.immediately_implies(
            self.last_formula,
            forallm(forallyz(body(A, v.y, v.z))),
            forallm(forallz(body(A, B, v.z))),
        )

        p(forallm(Implies(forallz(body(A, B, v.z)), body(A, B, C))))
        return self.immediately_implies(
            self.last_formula, forallm(forallz(body(A, B, v.z))), theorem
        )

    def _prove_values_transitively_equal_2args(self, a, b, c):
        v = get_cached_vars()
        p = self.p

        self.prove_eq_is_transitive()

        def body(x, y, z):
            return ImpliesN(Eq(x, y), Eq(y, z), Eq(x, z))

        eq_transitive = forallxyz(body(v.x, v.y, v.z))
        eq_transitive_m = forallm(eq_transitive)
        self.immediately_implies(eq_transitive, eq_transitive_m)
        eq_transitive_mn = foralln(eq_transitive_m)
        self.immediately_implies(eq_transitive, eq_transitive_mn)

        A = a(v.m, v.n)
        B = b(v.m, v.n)
        C = c(v.m, v.n)

        theorem = forallmn(body(A, B, C))

        p(forallmn(Implies(eq_transitive, forallyz(body(A, v.y, v.z)))))
        self.forall_split()
        p(forallmn(Implies(forallyz(body(A, v.y, v.z)), forallz(body(A, B, v.z)))))
        self.forall_split()
        p(forallmn(Implies(forallz(body(A, B, v.z)), body(A, B, C))))
        return self.forall_split()

    def prove_values_transitively_equal(self, a, b, c, nargs=1):
        """Proves "f x. A(x)=B(x) => B(x)=C(x) => A(x)=C(x)".

        `a`, `b` and `c` are Python functions that return A, B, C respectively when
        called.

        If `nargs` is 2 then proves "f x,y. A(x,y)=B(x,y) => B(x,y)=C(x,y) =>
        A(x,y)=C(x,y)"

        """

        assert nargs in [1, 2], f"nargs = {nargs}"
        if nargs == 1:
            return self._prove_values_transitively_equal_1arg(a, b, c)
        else:
            return self._prove_values_transitively_equal_2args(a, b, c)

    def subst_forall_with_expr(self, forall, f):
        """Given a formula "forall x. P(x)", proves "forall x. P(F(x))".

        `f` is a Python function that generates `F(x)` when called.
        """
        v = get_cached_vars()
        assert forall.var != "t"
        self.immediately_implies(forall, forallt(forall))
        self.p(forallt(Implies(forall, substitute_forall(forall, f(v.t)))))
        return self.forall_split()

    def subst_forall_with_const(self, forall, c):
        return self.immediately_implies(forall, substitute_forall(forall, c))

    def flip_xy_order_in_forall(self, forall=None):
        """Given "forall x, y. P(x, y)", proves "forall y, x. P(x, y)"."""
        if forall is None:
            forall = self.last_formula

        v = get_cached_vars()
        p = self.p

        available_vars = sorted(
            list(set(["a", "b", "c", "d"]) - set([forall.var, forall.body.var]))
        )
        vx = Var(available_vars[0])
        vy = Var(available_vars[1])

        def _forallx(body):
            return ForAll(vx.name, body)

        def _forally(body):
            return ForAll(vy.name, body)

        def _forallxy(body):
            return _forallx(_forally(body))

        def body(x, y):
            return substitute_forall(substitute_forall(forall, x), y)

        p(_forallxy(Implies(forall, foralln(body(vy, v.n)))))
        self.forall_split("med")
        self.immediately_implies(forall, _forally(forall))
        self.immediately_implies(_forally(forall), _forallxy(forall))
        self.immediately_implies(_forallxy(forall), _forallxy(foralln(body(vy, v.n))))

        p(_forallxy(Implies(foralln(body(vy, v.n)), body(vy, vx))))
        self.forall_split("med")
        return p(_forallxy(body(vy, vx)))

    def prove_expr_eq_to_itself(self, expr, free_vars):
        """Generate a proof that `expr` is equal to itself."""
        p = self.p
        v = get_cached_vars()

        assert set(free_vars) == get_free_vars(
            expr
        ), f"free_vars = {free_vars}, get_free_vars(expr) = {get_free_vars(expr)}"
        assert len(free_vars) == 1 or len(free_vars) == 2
        available_vars = sorted(list(set(["p", "q", "r"]) - set(free_vars)))

        x = Var(available_vars[0])

        def _forallx(expr):
            return ForAll(x.name, expr)

        def _forally(expr):
            return ForAllN(free_vars, expr)

        # forallyx. x=x
        # forally. (forallx. x=x) => fn(y)=fn(y)
        # (forallyx. x=x) => forally. fn(y)=fn(y)

        x_eq_x = Eq(x, x)
        p(_forally(_forallx(x_eq_x)))
        p(_forally(Implies(_forallx(x_eq_x), Eq(expr, expr))))
        self.forall_split()

    def apply_fn_on_eq(self, fn, eq=None):
        """Given "forall x. M(x)=N(x)" proves "forall x. F(M(x))=F(N(x))"

        `fn` is a Python function that generates F(x).
        """
        if eq is None:
            eq = self.last_formula

        p = self.p

        A = eq.body.a
        B = eq.body.b

        def _forallx(body):
            return ForAll(eq.var, body)

        self.prove_expr_eq_to_itself(fn(A), [eq.var])
        p(_forallx(ImpliesN(eq.body, Eq(fn(A), fn(A)), Eq(fn(A), fn(B)))))
        self.forall_split()
        return self.forall_split()

    def flip_implication_order(self, impl=None):
        """Given "A->B->C" prove "B->A->C" """
        if impl is None:
            impl = self.last_formula

        self.p(
            Implies(
                ImpliesN(impl.p, impl.q.p, impl.q.q),
                ImpliesN(impl.q.p, impl.p, impl.q.q),
            )
        )
        return self.p(ImpliesN(impl.q.p, impl.p, impl.q.q))

    def compose_implications(self, a, b):
        """Given A->B and B->C prove A->C"""
        self.p(ImpliesN(a, b, a.p, b.q))
        self.p(ImpliesN(b, a.p, b.q))
        return self.p(ImpliesN(a.p, b.q))

    def _recursively_rename_forall_quantifier(self, var, formula):
        ftype = type(formula)
        if ftype == ForAll:
            return ForAll(var, substitute_forall(formula, Var(var)))
        elif ftype == Implies:
            return Implies(
                self._recursively_rename_forall_quantifier(var, formula.p),
                self._recursively_rename_forall_quantifier(var, formula.q),
            )
        elif ftype == And:
            return And(
                self._recursively_rename_forall_quantifier(var, formula.a),
                self._recursively_rename_forall_quantifier(var, formula.b),
            )
        else:
            assert False, f"Unhandled type: {ftype}"

    def rename_forall_quantifier(self, var, formula=None):
        if formula is None:
            formula = self.last_formula

        for n in get_all_subformulae(formula):
            assert not (isinstance(n, Var) and n.name == var)

        return self.p(self._recursively_rename_forall_quantifier(var, formula))

    def peano_axiom_zero_is_not_succ(self):
        return self.p(get_peano_axiom_zero_is_not_succ())

    def peano_axiom_succ_is_injective(self):
        return self.p(get_peano_axiom_succ_is_injective())

    def peano_axiom_x_plus_zero(self):
        return self.p(get_peano_axiom_x_plus_zero())

    def peano_axiom_x_plus_succ_y(self):
        return self.p(get_peano_axiom_x_plus_succ_y())

    def peano_axiom_x_times_zero(self):
        return self.p(get_peano_axiom_x_times_zero())

    def peano_axiom_x_times_succ_y(self):
        return self.p(get_peano_axiom_x_times_succ_y())
