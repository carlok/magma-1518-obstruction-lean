% T = 1518 + the four one-variable targets + finite-model consequences used as axioms
fof(e1518, axiom, ![X,Y]: X = m(m(Y,Y), m(X, m(Y,X)))).
% finite 1518-magmas are left quasigroups (Tao 2024-11-24): left multiplication is injective and surjective
fof(left_inj, axiom, ![X,Y,Z]: (m(X,Y) = m(X,Z) => Y = Z)).
fof(left_surj, axiom, ![X,Y]: ?[Z]: m(X,Z) = Y).
fof(closure_x_x_notargets, conjecture, ![X]: (m(X,m(X,X)) = X | m(X,m(X,X)) = m(X,X) | m(X,m(X,X)) = m(m(X,X),m(X,X)))).
