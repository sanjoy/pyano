from axioms import *
from formula import *

import itertools


def _is_comment(proof_step):
    return isinstance(proof_step, str)


def _get_previous_comment(proof, idx):
    for p in proof[idx::-1]:
        if _is_comment(p):
            return p
    return None


class InvalidProofError(ValueError):
    def __init__(self, invalid_formula, invalid_formula_idx, last_comment):
        self._invalid_formula = invalid_formula
        self._invalid_formula_idx = invalid_formula_idx
        self._last_comment = last_comment

    @property
    def invalid_formula(self):
        return self._invalid_formula

    @property
    def invalid_formula_idx(self):
        return self._invalid_formula_idx

    @property
    def last_comment(self):
        return self._last_comment

    def __str__(self):
        return (
            f"Proof not valid: error at step number {self.invalid_formula_idx}, "
            + f"last comment: {self.last_comment}\n\n"
            + f"Invalid formula: {self.invalid_formula}"
        )


def assert_proof_is_valid(proof):
    """Raises an `InvalidProofError` if `proof` is invalid, otherwise returns normally.

    A proof is a list of `Formula`s where each formula is either an axiom
    itself, or follows from a previous formula.  See the "What is a correct
    proof" section in README.md for a longer explanation.
    """

    implications = {}
    valid_formulae = set()

    for formula_idx, formula in enumerate(proof):
        # Strings are comments and are skipped over.  We return the last comment before
        # an incorrect formula which can help narrow down the bug.
        if _is_comment(formula):
            continue

        ok = is_axiom(formula) or (
            formula in implications
            and any([ant in valid_formulae for ant in implications[formula]])
        )

        if not ok:
            prev_comment = _get_previous_comment(proof, formula_idx)
            raise InvalidProofError(formula, formula_idx, prev_comment)

        valid_formulae.add(formula)

        if isinstance(formula, Implies):
            if formula.q not in implications:
                implications[formula.q] = set([formula.p])
            else:
                implications[formula.q].add(formula.p)
