from clausesets import ClauseSet
from unification import mgu

# TODO: Sonderbehandlung für equality ??



def get_mgu(clause1, lit1, clause2, lit2):
    l1 = clause1.getLiteral(lit1)
    l2 = clause2.getLiteral(lit2)
    if l1.isNegative() == l2.isNegative():
        return None
    sigma = mgu(l1.atom, l2.atom)
    return sigma


class AlternatingPath(object):
    def __init__(self, clauses, limit=float('inf')):
        self.limit = limit
        self.unprocessed = ClauseSet()
        self.selected = [ClauseSet()]
        for c in clauses.clauses:
            if c.type in ["negated_conjecture", "plain"]:
                self.selected[0].addClause(c)
            else:
                self.unprocessed.addClause(c)

    @property
    def depth(self):
        return len(self.selected) - 1

    @property
    def selected_flat(self):
        return ClauseSet([clause for cs in self.selected for clause in cs.clauses])

    def computeAllReachable(self, clause):
        reachable = []
        for lit in range(len(clause)):
            if clause.getLiteral(lit).isInferenceLit():
                partners = \
                    self.unprocessed.getResolutionLiterals(clause.getLiteral(lit))
                for (cl2, lit2) in partners:
                    sigma = get_mgu(clause, lit, cl2, lit2)
                    if sigma is not None and cl2 not in reachable:
                        reachable.append(cl2)
        return reachable

    def saturate(self):
        while self.depth < self.limit:
            currentLevel = self.selected[-1]
            nextLevel = ClauseSet()
            self.selected.append(nextLevel)
            for clause in currentLevel.clauses:
                newReachable = self.computeAllReachable(clause)
                for c in newReachable:
                    self.unprocessed.clauses.remove(c)
                    nextLevel.addClause(c)
            # if we didn't find any new paths, we stop.
            if not nextLevel.clauses:
                break
        return self.selected_flat
