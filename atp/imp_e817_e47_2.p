fof(e1518, axiom, ![X,Y]: X = m(m(Y,Y), m(X, m(Y,X)))).
fof(e817, axiom, ![X]: X = m(X, m(m(X,X), m(X,X)))).
fof(left_inj, axiom, ![X,Y,Z]: (m(X,Y) = m(X,Z) => Y = Z)).
fof(left_surj, axiom, ![X,Y]: ?[Z]: m(X,Z) = Y).
fof(goal, conjecture, ![X]: X = m(X, m(X, m(X,X)))).
