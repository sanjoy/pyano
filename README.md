# Pyano

Pyano (pronounced "piano") is a formalization of first-order logic and Peano's
axioms in Python.

It consists of a few things:

1. A representation for proofs in first-order logic.
2. An automated proof verifier.
3. Python helpers to generate proofs.

Pyano is a toy project and not suitable for production use.  Having said that,
I'd love to hear from you if you found it useful in some way.

## Getting started

Pyano uses `pytest` to run its unit tests and `black` to keep the Python code
formatted.  I recommend installing these into a local virtual environment in the
following way:

```
python3 -m venv venv && \
	source venv/bin/activate && \
	pip install --upgrade pip && \
	pip install -r requirements.txt
```

Running `pytest` in the `pyano` directory will execute all of Pyano's unit
tests.

If you learn by doing and enjoy throwing yourself in the deep end, try extending
`prove_one_less_than_or_eq_two` in `theorems.py` (which proves `1` is less than
or equal to `2`) to prove that `1` is less than or equal to `3`.  See
`theorems_test.py` on how to formally verify the proof.

## Code structure

* `formula.py` contains the data structures to represent first-order formulae
  and functions to manipulate and query them.  `formula_helpers.py` has some
  ergonomic helpers that seemed natural to split out.
* `axioms.py` contains the list of axioms allowed in Pyano.
* `proof_checker.py` contains `assert_proof_is_valid` which checks whether a
  formal proof is valid.
* `proof_builder.py` defines `ProofBuilder` which is a (stateful) builder class
  that makes writing proofs easier.
* `theorems.py` proves a couple of theorems.  The full proofs for these theorems
  are checked-in at `pyano/proved_theorems`, and running `theorems.py`
  regenerates these.

## What is a correct proof?

A formally correct proof in first-order logic is a sequence of formulae where
each statement is either an axiom (and thus assumed to be true) or follows from
two previous axioms through [modus
ponens](https://en.wikipedia.org/wiki/Modus_ponens).  There are equivalent
formulations, but this is the definition used in Pyano.

So the following is a valid proof that shows 0=0.  The text in square brackets
are comments which aren't part of the formal proof.

1. `forall x. x = x`.  [This is an axiom.]
2. `forall x. x = x => 0=0`  [This is an axiom.]
3. `0=0` [Follows from modus ponens in 1 and 2.]

As a counterexample, the following proof is incorrect:

1. `forall x. x = x`.  [This is an axiom.]
2. `0=0` [Invalid step.]

### How are proofs verified?

The description above immediately suggests a straightforward algorithm to verify
proofs:

```
for i in range(0, len(proof)):
  if is_axiom(proof[i]):
    continue

  modus_ponens = False
  for j in range(0, i):
    for k in range(0, i):
      if (proof[j] is P=>Q and
          proof[k] is P and
          proof[i] is Q)
        modus_ponens = True

  if not modus_ponens:
    fail_verification()
```

`proof_checker.py` implements a slightly more optimized version of this
algorithm.

## Axioms

The axioms encode much of the firepower of this proof system.

I picked this set from Antonio Montalban's excellent [Math 125A -- Mathematical
Logic
course](https://www.youtube.com/playlist?list=PLjJhPCaCziSRSUtQiTA_yx5TJ76G_EqUJ).

### ForAll Axioms

These two are hopefully intuitively clear:

* For any `k` the following is an axiom `forall x. P(x) => P(k)`.
* `P => forall x. P(x)`, assuming `x` is not a free variable in `P`.

Finally, we have an axiom that lets us split forall formulae: `(forall x. P(x)
=> Q(x)) => forall x. P(x) => forall x. Q(x)`.

I understood it intuitively as: if everyone who loves chocolate also loves
ice-cream, and everyone loves chocolate then everyone loves ice-cream

Note that the converse, `(forall x. P(x) => forall x. Q(x)) => (forall x. P(x)
=> Q(x))` cannot be an axiom since it is false -- consider `P(x) = x == 2` and
`Q(x) = x == 3`.

### Sentential Tautology

Any And/Not/Implies expression that is true for all possible values of its
"leaves" is an axiom.

So `Not(Not(forall x. P(x))) => forall x. P(x)` is an axiom since it is true
irrespective of whether `forall x. P(x)` is true or not.

It may seem like this axiom says "true things are true" but that's not correct.
We can easily (well, in exponential time :) ) decide if an expression is an
axiom by this rule or not so it's well founded.

### Reflexivity

This says things are equal to themselves: `forall x. x = x`.

### Substitution

This says you can substitute expressions with another expression equal to it.

Formally it says `x = y => F => G` where you get `G` by replacing some (not
necessarily all) instance of `x` in `F` with `y`.

### Natural number axioms

These are the standard Peano axioms stating the various properties of natural
numbers.

 * `forallx(Not(Eq(Zero(), Succ(x))))`
 * `forallxy(Implies(Eq(Succ(x), Succ(y)), Eq(x, y)))`
 * `forallx(Eq(Add(x, Zero()), x))`
 * `forallxy(Eq(Add(x, Succ(y)), Succ(Add(x, y))))`
 * `forallx(Eq(Mul(x, Zero()), Zero()))`
 * `forallxy(Eq(Mul(x, Succ(y)), Add(Mul(x, y), x)))`

### Induction Axiom

This says that for any predicate `P(x)` the following is an axiom: `P(0) &
(forall k. P(k) => P(S(k))) => forall x. P(x)`.

It may seem tempting to have a more direct representation for the induction
axiom, like `forall P. (P(0) & (forall k. P(k) => P(S(k))) => forall x. P(x))`.
However, quantifiers in first-order logic only range over natural numbers so
this won't work.
