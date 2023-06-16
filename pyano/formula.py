"""Core data structures to represent first order formulas."""

import itertools
import functools


class Formula:
    """Base class for all formula sub-classes."""

    def __eq__(self, other):
        if hash(self) != hash(other):
            # This is a performance optimization; not needed for correct behavior.
            return False

        # Equality is just matching without any special treatment of free variables.
        return _match_free_vars(
            self,
            other,
            var_replacements={},
            vars_to_capture=set(),
            b_bindings_stack=[],
            captured_formulae={},
        )

    def __hash__(self):
        # We construct and store _hash on construction.
        return self._hash


class Nat(Formula):
    """Base class for all formulae that represent natural numbers."""

    pass


def _assert_type(x, t):
    assert isinstance(x, t), f"Expected x to be of type {t}, found {type(x)}"


class Zero(Nat):
    """Symbol for zero in Peano's axioms."""

    def __init__(self):
        self._hash = self._compute_hash()

    def __str__(self):
        return "0"

    def _compute_hash(self):
        return hash((Zero,))


class Succ(Nat):
    """Symbol for the successor function (https://en.wikipedia.org/wiki/Successor_function)
    in Peano's axioms."""

    def __init__(self, x):
        _assert_type(x, Nat)

        self._x = x
        self._hash = self._compute_hash()

    def __str__(self):
        return f"S({self.x})"

    def _compute_hash(self):
        return hash((Succ, self.x))

    @property
    def x(self):
        return self._x


class Add(Nat):
    def __init__(self, a: Nat, b: Nat):
        _assert_type(a, Nat)
        _assert_type(b, Nat)

        self._a = a
        self._b = b

        self._hash = self._compute_hash()

    def __str__(self):
        return f"({self.a} + {self.b})"

    def _compute_hash(self):
        return hash((Add, self.a, self.b))

    @property
    def a(self):
        return self._a

    @property
    def b(self):
        return self._b


class Mul(Nat):
    def __init__(self, a: Nat, b: Nat):
        _assert_type(a, Nat)
        _assert_type(b, Nat)

        self._a = a
        self._b = b

        self._hash = self._compute_hash()

    def __str__(self):
        return f"({self.a} * {self.b})"

    def _compute_hash(self):
        return hash((Mul, self.a, self.b))

    @property
    def a(self):
        return self._a

    @property
    def b(self):
        return self._b


class Var(Nat):
    """Represents a variable.

    Variables can be bound to an outer `ForAll` or be free.

    """

    def __init__(self, name):
        _assert_type(name, str)

        self._name = name

        self._hash = self._compute_hash()

    def __str__(self):
        return self.name

    def _compute_hash(self):
        # Don't include the name in the hash; if we do then alpha-equivalent forall
        # expressions will have different hashes.
        return hash((Var,))

    @property
    def name(self):
        return self._name


class Pred(Formula):
    """Base class for all formulae that represent predicates."""

    pass


class Eq(Pred):
    def __init__(self, a, b):
        _assert_type(a, Nat)
        _assert_type(b, Nat)

        self._a = a
        self._b = b

        self._hash = self._compute_hash()

    def __str__(self):
        return f"({self.a} = {self.b})"

    def _compute_hash(self):
        return hash((Eq, self.a, self.b))

    @property
    def a(self):
        return self._a

    @property
    def b(self):
        return self._b


class And(Pred):
    def __init__(self, a, b):
        _assert_type(a, Pred)
        _assert_type(b, Pred)

        self._a = a
        self._b = b

        self._hash = self._compute_hash()

    def __str__(self):
        return f"({self.a} & {self.b})"

    def _compute_hash(self):
        return hash((And, self.a, self.b))

    @property
    def a(self):
        return self._a

    @property
    def b(self):
        return self._b


class Not(Pred):
    def __init__(self, x: Pred):
        _assert_type(x, Pred)

        self._x = x

        self._hash = self._compute_hash()

    def __str__(self):
        return f"!{self.x}"

    def _compute_hash(self):
        return hash((Not, self.x))

    @property
    def x(self):
        return self._x


class Implies(Pred):
    def __init__(self, p, q):
        _assert_type(p, Pred)
        _assert_type(q, Pred)

        self._p = p
        self._q = q

        self._hash = self._compute_hash()

    def __str__(self):
        if isinstance(self.p, Implies):
            return f"({self.p}) => {self.q}"
        else:
            return f"{self.p} => {self.q}"

    def _compute_hash(self):
        return hash((Implies, self.p, self.q))

    @property
    def p(self):
        return self._p

    @property
    def q(self):
        return self._q


class ForAll(Pred):
    def __init__(self, var, body):
        _assert_type(var, str)
        _assert_type(body, Pred)

        self._var = var
        self._body = body

        self._hash = self._compute_hash()

    def __str__(self):
        return f"(forall {self.var}. {self.body})"

    def _compute_hash(self):
        return hash((ForAll, self.body))

    @property
    def var(self):
        return self._var

    @property
    def body(self):
        return self._body


def _recursively_get_all_subformulae(f):
    yield f

    ftype = type(f)
    if ftype == Succ or ftype == Not:
        yield from _recursively_get_all_subformulae(f.x)
    elif ftype == Add or ftype == Eq or ftype == And:
        yield from _recursively_get_all_subformulae(f.a)
        yield from _recursively_get_all_subformulae(f.b)
    elif ftype == Implies:
        yield from _recursively_get_all_subformulae(f.p)
        yield from _recursively_get_all_subformulae(f.q)
    elif ftype == ForAll:
        yield from _recursively_get_all_subformulae(f.body)


def get_all_subformulae(f):
    """Returns all the subformulae in `f`.

    >>> fs = get_all_subformulae(ForAll("x", Eq(Var("x"), Var("x"))))
    >>> print(", ".join([str(f) for f in fs]))
    (forall x. (x = x)), (x = x), x, x
    """

    yield from _recursively_get_all_subformulae(f)


def _match_free_vars(
    a, b, var_replacements, vars_to_capture, b_bindings_stack, captured_formulae
):
    def recurse(aa, bb):
        return _match_free_vars(
            aa,
            bb,
            var_replacements,
            vars_to_capture,
            b_bindings_stack,
            captured_formulae,
        )

    atype = type(a)

    if atype == Var and a.name in vars_to_capture:
        if a.name in captured_formulae:
            return captured_formulae[a.name] == b
        for subb in get_all_subformulae(b):
            if isinstance(subb, Var) and subb.name in b_bindings_stack:
                return False
        captured_formulae[a.name] = b
        return True

    if atype != type(b):
        return False

    if atype == Var:
        b_name = var_replacements.get(b.name, b.name)
        return a.name == b_name
    elif atype == Zero:
        return True
    elif atype == Succ or atype == Not:
        return recurse(a.x, b.x)
    elif atype == Add or atype == Mul or atype == Eq or atype == And:
        return recurse(a.a, b.a) and recurse(a.b, b.b)
    elif atype == Implies:
        return recurse(a.p, b.p) and recurse(a.q, b.q)
    elif atype == ForAll:
        if a.var != b.var:
            var_replacements = var_replacements.copy()
            var_replacements[b.var] = a.var
        if a.var in vars_to_capture:
            vars_to_capture = vars_to_capture.copy()
            vars_to_capture.remove(a.var)
        b_bindings_stack = b_bindings_stack.copy()
        b_bindings_stack.append(b.var)
        return _match_free_vars(
            a.body,
            b.body,
            var_replacements,
            vars_to_capture,
            b_bindings_stack,
            captured_formulae,
        )

    assert False, f"Unhandled type: {atype}"


def _recursively_subst_vars(f, var_assignment):
    def recurse(subexpr):
        return _recursively_subst_vars(subexpr, var_assignment)

    ftype = type(f)
    if ftype == Var and f.name in var_assignment:
        return var_assignment[f.name]
    elif ftype == Succ or ftype == Not:
        return ftype(recurse(f.x))
    elif ftype == Add or ftype == Mul or ftype == Eq or ftype == And:
        return ftype(recurse(f.a), recurse(f.b))
    elif ftype == Implies:
        return Implies(recurse(f.p), recurse(f.q))
    elif ftype == ForAll:
        if f.var in var_assignment:
            var_assignment = var_assignment.copy()
            del var_assignment[f.var]
        return ForAll(f.var, _recursively_subst_vars(f.body, var_assignment))
    else:
        return f


def substitute_forall(f, value):
    """Replace the variable in `f` (which must be a `ForAll`) with `value`.

    >>> f = ForAll("x", Eq(Var("x"), Var("x")))
    >>> newf = substitute_forall(f, Succ(Zero()))
    >>> print(newf)
    (S(0) = S(0))
    """

    _assert_type(f, ForAll)
    return _recursively_subst_vars(f.body, {f.var: value})


def substitute_free_var(f, free_var, value):
    """Replace free instances of `free_var` in `f` with `value`.

    >>> f = Eq(Var("x"), Var("x"))
    >>> newf = substitute_free_var(f, "x", Zero())
    >>> print(newf)
    (0 = 0)

    >>> f = ForAll("x", Eq(Var("x"), Var("x")))
    >>> newf = substitute_free_var(f, "x", Zero())
    >>> print(newf)
    (forall x. (x = x))
    """
    return _recursively_subst_vars(f, {free_var: value})


def get_name_generator(fs):
    """Returns a callable that generates fresh names that don't clash in
    the names in `fs`.  `fs` can be a formula or a list of formulae.

    >>> f = ForAll("x", Eq(Var("x"), Var("x")))
    >>> gen = get_name_generator(f)
    >>> print(f"{gen()}, {gen()}, {gen()}")
    $0, $1, $2

    >>> f = ForAll("$0", Eq(Var("$0"), Var("$1")))
    >>> gen = get_name_generator(f)
    >>> print(f"{gen()}, {gen()}, {gen()}")
    $2, $3, $4
    """

    if not isinstance(fs, list):
        fs = [fs]

    all_names = set()
    for f in fs:
        subformulae = get_all_subformulae(f)
        names = [x.name for x in subformulae if isinstance(x, Var)]
        all_names.update(names)

    max_suffix = -1
    for n in all_names:
        if n.startswith("$") and n[1:].isdigit():
            max_suffix = max(max_suffix, int(n[1:]))

    def generate():
        nonlocal max_suffix
        max_suffix = max_suffix + 1
        return f"${max_suffix}"

    return generate


def _recursively_get_free_vars(f, env, result):
    def recurse(subf):
        _recursively_get_free_vars(subf, env, result)

    ftype = type(f)
    if ftype == Zero:
        pass
    elif ftype == Var:
        if f.name not in env:
            result.add(f.name)
    elif ftype == Succ or ftype == Not:
        return recurse(f.x)
    elif ftype == Add or ftype == Mul or ftype == Eq or ftype == And:
        recurse(f.a)
        recurse(f.b)
    elif ftype == Implies:
        recurse(f.p)
        recurse(f.q)
    else:
        assert ftype == ForAll, f"ftype = {ftype}"
        _recursively_get_free_vars(f.body, env + [f.var], result)


def get_free_vars(f):
    """Returns the set of free variables in `f`.

    >>> get_free_vars(ForAll("x", Eq(Var("x"), Var("y"))))
    {'y'}
    """

    result = set()
    _recursively_get_free_vars(f, [], result)
    return result


def replace_subformula(f, x, y):
    """Replaces all instances of `x` in `f` with `y`.

    >>> f = ForAll("x", Eq(Succ(Var("y")), Var("x")))
    >>> x = Succ(Var("y"))
    >>> y = Zero()
    >>> print(replace_subformula(f, x, y))
    (forall x. (0 = x))

    This checks for alpha-equivalence, not just syntactic equality:

    >>> f = And(ForAll("x", Eq(Zero(), Var("x"))), Eq(Succ(Zero()), Var("x")))
    >>> x = ForAll("z", Eq(Zero(), Var("z")))
    >>> y = Eq(Zero(), Succ(Zero()))
    >>> print(replace_subformula(f, x, y))
    ((0 = S(0)) & (S(0) = x))

    """

    def recurse(subf):
        return replace_subformula(subf, x, y)

    if f == x:
        if callable(y):
            return y()
        else:
            return y

    ftype = type(f)
    if ftype == Var or ftype == Zero:
        return f
    elif ftype == Succ or ftype == Not:
        return Succ(recurse(f.x))
    elif ftype == Add or ftype == Mul or ftype == Eq or ftype == And:
        return ftype(recurse(f.a), recurse(f.b))
    elif ftype == Implies:
        return Implies(recurse(f.p), recurse(f.q))
    else:
        assert ftype == ForAll, f"ftype = {ftype}"
        return ForAll(f.var, recurse(f.body))


def _recursively_canonicalize_bound_vars(f, bindings, vargen, free_vars):
    def recurse(subf):
        return _recursively_canonicalize_bound_vars(subf, bindings, vargen, free_vars)

    ftype = type(f)
    if ftype == Zero:
        return f
    elif ftype == Var:
        if f.name in bindings:
            return bindings[f.name]
        free_vars.add(f)
        return f
    elif ftype == Succ or ftype == Not:
        return ftype(recurse(f.x))
    elif ftype == Add or ftype == Mul or ftype == Eq or ftype == And:
        return ftype(recurse(f.a), recurse(f.b))
    elif ftype == Implies:
        return Implies(recurse(f.p), recurse(f.q))
    else:
        assert ftype == ForAll, f"ftype = {ftype}"
        newvar = vargen()

        bindings = bindings.copy()
        bindings[f.var] = Var(newvar)

        body = _recursively_canonicalize_bound_vars(f.body, bindings, vargen, free_vars)

        return ForAll(newvar, body)


def canonicalize_bound_vars(f, free_vars=None):
    """Rewrites all the bound variables in `f` to be unique and sequential.

    >>> f = And(ForAll("x", Eq(Var("x"), Zero())),
    ...         ForAll("y", Eq(Var("y"), Var("z"))))
    >>> print(f)
    ((forall x. (x = 0)) & (forall y. (y = z)))
    >>> print(canonicalize_bound_vars(f))
    ((forall $0. ($0 = 0)) & (forall $1. ($1 = z)))

    """
    if free_vars is None:
        free_vars = set()

    var_counter = 0

    def vargen():
        nonlocal var_counter
        x = var_counter
        var_counter = var_counter + 1
        return f"${x}"

    return _recursively_canonicalize_bound_vars(f, {}, vargen, free_vars)


def match_template(template, f, vars_to_capture, captured_formulae=None):
    """Tries to match `f` against `template`.  Succeeds if there is a
    `captured_formulae` such that the following substitutions produces a formula
    alpha-equivalent to `f`:

      f = template
      for var in vars_to_capture:
          f = substitute_free_var(f, var, captured_formulae[var])

    In a way, you can think of this method as an "inverse" of substitution.

    If `vars_to_capture` is empty then this is equivalent to checking for
    alpha-equivalence.

    Basic usage:

    >>> captures = {}
    >>> result = match_template(Succ(Var("x")), Succ(Succ(Zero())), ["x"], captures)
    >>> print(result)
    True
    >>> print(captures["x"])
    S(0)

    A given variable must be assigned the same value consistently:

    >>> one = Succ(Zero())
    >>> result = match_template(Add(Var("x"), Var("x")), Add(Zero(), one), ["x"])
    >>> print(result)
    False

    We also don't match in cases situations that can never arise through
    substitution:

    >>> template = ForAll("x", Eq(Var("x"), Var("capture")))
    >>> f = ForAll("x", Eq(Var("x"), Var("x")))
    >>> result = match_template(template, f, ["z"])
    >>> print(result)
    False

    """

    if captured_formulae is None:
        captured_formulae = {}

    return _match_free_vars(
        template,
        f,
        var_replacements={},
        vars_to_capture=set(vars_to_capture),
        b_bindings_stack=[],
        captured_formulae=captured_formulae,
    )
