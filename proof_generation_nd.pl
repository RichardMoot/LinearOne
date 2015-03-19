
% Direct ND generation

create_pos_proof(N-A, L0, L, Proof) :-
	create_pos_proof(A, N, L0, L, Proof).

% = create_pos_proof(+PositiveFormula, +NodeNumber, +/-AtomsDL, -Proof)

create_pos_proof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax,[M-at(A,C,N,Vars)], M-at(A,_C,_N,Vars), [])) :-
	!.
create_pos_proof(exists(X,N-A), N, L0, L, rule(er, Gamma, N-exists(Y,N-A3), [ProofA])) :-
        !,
	/* rename to make sure bound variable isn't unified */
	rename_bound_variables(A, A2),
	rename_bound_variable(exists(X,N-A2), X, Y, exists(Y,N-A3)),
        create_pos_proof(A, N, L0, L, ProofA),
        ProofA = rule(_, Gamma, N-A2, _).
create_pos_proof(p(N-A,N-B), N, L0, L, rule(pr, GD, N-p(N-A2,N-B2), [P1,P2])) :-
        !,
        create_pos_proof(A, N, L0, L1, P1),
        create_pos_proof(B, N, L1, L, P2),
        P1 = rule(_, Gamma, N-A2, _),
        P2 = rule(_, Delta, N-B2, _),
        append(Gamma, Delta, GD).
% complex (negative) subformula
create_pos_proof(F, N, L, L, rule(ax, [N-F], N-F, [])).

% = create_neg_proof(+NumberedNegativeFormula, +/-AtomsDL, +Goal, -Proof)

create_neg_proof(N-A, L0, L, Neg, Proof) :-
	create_neg_proof(A, N, L0, L, Neg, Proof).

% = create_neg_proof(+NegativeFormula, +NodeNumber, +/-AtomsDL, +Goal, -Proof)

create_neg_proof(at(A,C,N,Vars), M, [neg(A,C,N,_,Vars)|L], L, at(A,C,N,Vars), rule(ax, [M-at(A,_C,_N,Vars)], M-at(A,C,N,Vars), [])) :-
        !.
create_neg_proof(impl(N-A,N-B), N, L0, L, Neg, rule(il, GD, N-Neg, [ProofA,ProofB])) :-
        !,
        create_pos_proof(A, N, L0, L1, ProofA),
	create_neg_proof(B, N, L1, L, Neg, ProofB),
	rename_bound_variables(B, B2),
	ProofA = rule(_, Gamma, N-A3, _),
	ProofB = rule(_, Delta, _, _),
	select_formula(B2, N, Delta, Delta_B),
	append(Gamma, [N-impl(N-A3,N-B2)|Delta_B], GD).
create_neg_proof(forall(X,N-A), N, L0, L, Neg, rule(fl, GammaP, C, [ProofA])) :-
        !,
	rename_bound_variables(A, A2),
        create_neg_proof(A, N, L0, L, Neg, ProofA),
        ProofA = rule(_, Gamma, C, _),
	/* rename to make sure bound variables aren't unified */
	replace_formula(A2, N, N-forall(Y,N-A3), Gamma, GammaP),
	rename_bound_variable(forall(X,N-A2), X, Y, forall(Y,N-A3)).
% complex (positive) subformula
create_neg_proof(F, N, L, L, _, rule(ax, [N-F], N-F, [])).


% = combine_univ(+Proof1, +Proof2, +Node1, +Node2, +VariableNumber, -Proof)
%
% combine Proof1 and Proof2 into Proof using a unary par contraction (with eigenvariable
% VariableNumber) which links Node1 to Node2

% = left rule for existential quantifier
combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P1 = rule(_, Gamma, N0-exists(var(V),N1-A), _),
	P2 = rule(_, Delta0, C, _),
	!,
	append(Delta1, [_-A|Delta2], Delta0),
	append(Delta1, [N1-exists(var(V),N1-A)|Delta2], Delta),
	append(Delta1, Gamma, GD1),
	append(GD1, Delta2, GD),
	/* try to create a cut-free proof */
	try_cut_elimination_left(P1, rule(el, Delta, C, [P2]), GD, Delta1, Delta2, C, N0-exists(var(V),N1-A), N0-exists(var(V),N1-A), Rule).

% = right rule for universal quantifier
combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P2 = rule(_, Gamma, N1-A, _),
	P1 = rule(_, Delta, C, _),
	append(Delta0, [_-forall(var(V),N1-A)|Delta1], Delta),
	append(Delta0, Gamma, GD0),
	append(GD0, Delta1, GD),
	/* try to create a cut-free proof */
	try_cut_elimination_right(rule(fr,Gamma,N1-forall(var(V),N1-A), [P2]), P1, GD, C, Gamma, N0-forall(var(V),N1-A), N0-forall(var(V),N1-A), Rule).

% = combine(+Proof1, +Proof2, +Node1, +Node2, -Proof)
%
% combine Proof1 and Proof2 into Proof using a binary par contraction which links Node1
% to Node2 (since this is a valid contraction, the two edges leaving Node1 must arrive
% in the same node Node2)

% = left rule for product
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(_, Gamma, N0-p(N1-A, N1-B), _),
        P2 = rule(_, Delta0, C, _),
	!,
	select_formula(B, N1, Delta0, Delta1),
	select_formula(A, N1, Delta1, Delta),
	replace_formula(A, N1, N1-p(N1-A,N1-B), Delta1, Delta2),
	append(Delta3, [N1-p(N1-A,N1-B)|Delta4], Delta2),
	append(Gamma, Delta, GD),		  
	/* try to create a cut-free proof */
	try_cut_elimination_left(P1, rule(pl, Delta2, C, [P2]), GD, Delta3, Delta4, C, N0-p(N1-A, N1-B), N0-p(N1-A, N1-B), Rule).

% = right rule for implication
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(_, Gamma, A, _),
	P2 = rule(_, Delta0, N1-D, _),
	append(Gamma0, [N0-impl(N1-C,N1-D)|Gamma1], Gamma),
	select_formula(C, N1, Delta0, Delta),
	append(Gamma0, Delta, GD0),
	append(GD0, Gamma1, GD),
	/* try to create a cut-free proof */
	try_cut_elimination_right(rule(ir, Delta, N0-impl(N1-C,N1-D), [P2]), P1, GD, A, Delta, N0-impl(N1-C,N1-D), N0-impl(N1-C,N1-D), Rule).
