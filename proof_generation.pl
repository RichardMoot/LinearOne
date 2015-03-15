:- module(proof_generation, [generate_proof/2]).

:- use_module(latex, [latex_proof/1]).
:- use_module(replace, [rename_bound_variable/4, rename_bound_variables/2, replace_proofs_labels/4]).
:- use_module(auxiliaries, [select_formula/4, subproofs/2, rulename/2, is_axiom/1, antecedent/2]).

generate_diagnostics(false).

% =======================================
% =           Proof generation          =
% =======================================

% = generate_proof(+InitialGraph, +ProofTrace)
%
% generate a sequent proof from the initial graph and proof trace
% given as arguments, and set the output to LaTeX.

generate_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	latex_proof(Proof).

combine_proofs([], [Proof], Proof).
combine_proofs([N0-par(N1)|Rest], Ps0, Proof) :-
	select(N0-P0, Ps0, Ps1),
	select(N1-P1, Ps1, Ps2),
	combine(P0, P1, N0, N1, P2),
	replace_proofs_labels([P2|Ps2], N0, N1, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([N0-univ(V,N1)|Rest], Ps0, Proof) :-
        select(N0-P0, Ps0, Ps1),
	select(N1-P1, Ps1, Ps2),
	combine_univ(P0, P1, N0, N1, V, P2),
	replace_proofs_labels([P2|Ps2], N0, N1, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([ax(N1,AtV1,AtO1,N0,AtV0,AtO0)|Rest], Ps0, Proof) :-
	select_pos_proof(Ps0, Ps1, AtV1, AtO1, Gamma, CL, LeftProof),
	proof_diagnostics('~NPos:~2n', LeftProof),
	select_neg_proof(Ps1, Ps2, AtV0, AtO0, Delta1, CR, Delta2, A, RightProof),
	proof_diagnostics('~NNeg:~2n', RightProof),
        append(Delta1, Gamma, GDP1),
	append(GDP1, Delta2, GDP),
	unify_atoms(CL, CR),
	try_cut_elimination_right(LeftProof, RightProof, GDP, A, Gamma, CL, CR, Rule),
	trivial_cut_elimination(RightProof, LeftProof, GDP, A, Rule0),
	antecedent(Rule, Ant1),
	antecedent(Rule0, Ant2),
	nl(user_error),
	print_two_lists(Ant1, Ant2),
	replace_proofs_labels([N0-Rule|Ps2], N1, N0, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([Next|_], CurrentProofs, Proof) :-
	/* dump all partial proofs in case of failure (useful for inspection) */
	format(user_error, '~N{Error: proof generation failed!}~nNext:~p~2n', [Next]),
	member(Proof, CurrentProofs).

% = trivial_cut_elimination(+LeftSubProof, +RightSubProof, +ConclusionAntecedent, +ConclusionSuccedent, -NewProof)

trivial_cut_elimination(P1, P2, GDP, C, rule(Nm, GDP, C, R)) :-
        is_axiom(P1),
        !,
	rulename(P2, Nm),
        subproofs(P2, R).
trivial_cut_elimination(P1, P2, GDP, C, rule(Nm, GDP, C, R)) :-
        is_axiom(P2),
        !,
	rulename(P1, Nm),		    
        subproofs(P1, R).
trivial_cut_elimination(P1, P2, GDP, C, rule(cut, GDP, C, [P2,P1])).


try_cut_elimination_right(LeftProof, RightProof, _GammaDelta, _A, Gamma, _-CL, _-CR, Proof) :-
	turbo_cut_elimination_right(RightProof, LeftProof, Gamma, CL, CR, Proof),
	!.
%	antecedent(Proof, Ant),
%	nl(user_error),
%        print_two_lists(GammaDelta, Ant).
try_cut_elimination_right(LeftProof, RightProof, GammaDelta, A, _Gamma, _CL, _CR, rule(cut, GammaDelta, A, [LeftProof,RightProof])).


print_two_lists([], []).
print_two_lists([A|As], [B|Bs]) :-
	( A == B -> C = ' '	; C = '*' ),
	format(user_error, '~w~t~w~34|~t~w~72|~w~n', [C,A,B,C]),
	print_two_lists(As, Bs).

%                      CL |- CL             Gamma |- CR
%                         .                       .
%                         .                       .
%  Gamma |- CR  Delta  CL |- A        Gamma, Delta |- A
%
% the proof on the left keeps CL constant in its right branch; in the proof of the right, we replace
% CL by Gamma throughout (and CL in the succedent by CR).

turbo_cut_elimination_left(rule(Nm, Gamma, _-CL, Rs0), RightProof, Delta1, Delta2, A, CL, CR, Proof) :-
    (
        Gamma = [_-CL], Rs0 = []
    ->
	/* reached axiom */     
	Proof = RightProof    
    ;				      		
        /* add Delta to Gamma and replace CL by A */
        append(Delta1, Gamma, GammaDelta1),
	append(GammaDelta1, Delta2, GammaDelta),
	Proof = rule(Nm, GammaDelta, A, Rs),
	turbo_cut_elimination_left1(Rs0, RightProof, Delta1, Delta2, A, CL, CR, Rs)
    ).

turbo_cut_elimination_left1([R0|Rs0], RightProof, Delta1, Delta2, A, CL, CR, [R|Rs]) :-
    (
	R0 = rule(_, _,_-CL, Rs0)
    ->
	Rs = Rs0,
	turbo_cut_elimination_left(R0, RightProof, Delta1, Delta2, A, CL, CR, R)
    ;		     
        R = R0,
        turbo_cut_elimination_left1(Rs0, RightProof, Delta1, Delta2, A, CL, CR, Rs)
    ).

%     CR |- CR                               Delta, CL |- A
%        .                                             .
%        .                                             .
%  Gamma |- CR  Delta, CL |- A            Delta, Gamma |- A
%
% the proof on the left transforms CR to Gamma without changing the succedent; we can
% use this same sequence of rules on the right to transform (replace) CL by the
% successive antecedents of the left proof

turbo_cut_elimination_right(rule(Nm, Delta, A, Rs0), LeftProof, Gamma, CL, CR, Proof) :-
    (
        Delta = [_-CR], Rs0 = []
    ->
	/* reached axiom */     
	Proof = LeftProof    
    ;				      		
        /* replace CR in the antecedent by Gamma */
	append(Delta1, [_-CR|Delta2], Delta),
	append(Delta1, Gamma, GammaDelta1),
	append(GammaDelta1, Delta2, GammaDelta),
	Proof = rule(Nm, GammaDelta, A, Rs),
	turbo_cut_elimination_right1(Rs0, LeftProof, Gamma, CL, CR, Rs)
    ).

% = proceed to the subproof containing CR
turbo_cut_elimination_right1([R0|Rs0], LeftProof, Delta, CL, CR, [R|Rs]) :-
    (
	antecedent_member(CR, R0)
    ->
	Rs = Rs0,
	turbo_cut_elimination_right(R0, LeftProof, Delta, CL, CR, R)
    ;		     
        R = R0,
        turbo_cut_elimination_right1(Rs0, LeftProof, Delta, CL, CR, Rs)
    ).


antecedent_member(F, rule(_, Gamma, _, _)) :-
	member(_-F, Gamma).

% = combine_univ(+Proof1, +Proof2, +Node1, +Node2, +VariableNumber, -Proof)
%
% combine Proof1 and Proof2 into Proof using a unary par contraction (with eigenvariable
% VariableNumber) which links Node1 to Node2

% = left rule for existential quantifier
combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P1 = rule(Nm, Gamma, N0-exists(var(V),N1-A), _),
	P2 = rule(_, Delta0, C, _),
	!,
	select_formula(A, N1, Delta0, Delta),
	replace_formula(A, N1, N1-exists(var(V),N1-A), Delta0, Delta1),
	append(Gamma, Delta, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(el, GD, C, [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(el, Delta1, C, [P2])])
   ).
% = right rule for universal quantifier
combine_univ(P1, P2, _N0, N1, V, N1-Rule) :-
        P2 = rule(_, Gamma, N1-A, _),
	P1 = rule(Nm, Delta, C, _),
	append(Delta0, [_-forall(var(V),N1-A)|Delta1], Delta),
	append(Delta0, Gamma, GD0),
	append(GD0, Delta1, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(fr,GD,N1-forall(var(V),N1-A), [P2])
   ;		  
        Rule = rule(cut, GD, C, [rule(fr,Gamma,N1-forall(var(V),N1-A), [P2]),P1])
   ).


% = combine(+Proof1, +Proof2, +Node1, +Node2, -Proof)
%
% combine Proof1 and Proof2 into Proof using a binary par contraction which links Node1
% to Node2 (since this is a valid contraction, the two edges leaving Node1 must arrive
% in the same node Node2)

% = left rule for product
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(Nm, Gamma, N0-p(N1-A, N1-B), _),
        P2 = rule(_, Delta0, C, _),
	!,
	select_formula(B, N1, Delta0, Delta1),
	select_formula(A, N1, Delta1, Delta),
	replace_formula(A, N1, N1-p(N1-A,N1-B), Delta1, Delta2),
	append(Gamma, Delta, GD),		  
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(pl, GD, C, [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(pl, Delta2, C, [P2])])
   ).
% = right rule for implication
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(Nm, Gamma, A, _),
	P2 = rule(_, Delta0, N1-D, _),
	append(Gamma0, [N0-impl(N1-C,N1-D)|Gamma1], Gamma),
	select_formula(C, N1, Delta0, Delta),
	append(Gamma0, Delta, GD0),
	append(GD0, Gamma1, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->	    
        Rule = rule(ir, GD, A, [P2])
   ;		  
        Rule = rule(cut, GD, A, [rule(ir, Delta, N0-impl(N1-C,N1-D), [P2]),P1])
   ).

% = unify_atoms(+Atom1, +Atom2)
%
% true if Atom1 and Atom2 unify when disregarding the unique two-integer
% identifiers

unify_atoms(_-at(A, _, _, Vs), _-at(A, _, _, Vs)).

% = same_formula(+Formula1, +Formula2)
%
% true if Formula1 and Formula2 are the same when disregarding the subformula
% numbering

same_formula(_-F0, _-F) :-
	same_formula1(F0, F).

same_formula1(at(A,Id1,Id2,_), at(A,Id1,Id2,_)).
same_formula1(forall(X,F0), forall(Y,F)) :-
	X == Y,
	same_formula(F0, F).
same_formula1(exists(X,F0), exists(Y,F)) :-
	X == Y,
	same_formula(F0, F).
same_formula1(impl(A0,B0), impl(A,B)) :-
	same_formula(A0, A),
	same_formula(B0, B).
same_formula1(p(A0,B0), p(A,B)) :-
	same_formula(A0, A),
	same_formula(B0, B).

% = select_neg_proof(+InProofs, -OutProofs, +Vertex, +Order, -Gamma, -A, -Delta, -C, -Proof)
%
% select the negative atomic formula indicated by the unique identifier Vertex-Order from InProofs, that is
% we are seeking a Proof with conclusion
%
%   Gamma, A, Delta |- C
%
% such that A is the formula indicated by Vertex-Order and OutProofs are the other proofs.


select_neg_proof([P|Ps], Ps, V, O, Gamma, A, Delta, C, Proof) :-
	select_neg_proof1(P, V, O, Gamma, A, Delta, C, Proof),
	!.
select_neg_proof([P|Ps], [P|Rs], V, O, Gamma, A, Delta, C, Proof) :-
	select_neg_proof(Ps, Rs, V, O, Gamma, A, Delta, C, Proof).

select_neg_proof1(_-P, V, O, Gamma, A, Delta, C, R) :-
	select_neg_proof1(P, V, O, Gamma, A, Delta, C, R).
select_neg_proof1(rule(Nm, GammaADelta, C, Ps), V, O, Gamma, A, Delta, C, rule(Nm, GammaADelta, C, Ps)) :-
	select_ant_formula(GammaADelta, V, O, Gamma, A, Delta).

% = select_pos_proof(+InProofs, -Outproof, +Vertex, +Order, -Delta, -A, -Proof)
%
% select the positive atomic indicated by the unique identifier Vertex-Order from InProofs, that is
% we are seeking a Proof with conclusion
%
%   Delta |- A
%
% such that A is the formula indicated by Vertex-Order and OutProofs are the other proofs.

select_pos_proof([P|Ps], Ps, V, O, Delta, A, Proof) :-
	select_pos_proof1(P, V, O, Delta, A, Proof),
	!.
select_pos_proof([P|Ps], [P|Rs], V, O, Delta, A, Proof) :-
	select_pos_proof(Ps, Rs, V, O, Delta, A, Proof).

select_pos_proof1(_-P, V, O, Delta, A, R) :-
	select_pos_proof1(P, V, O, Delta, A, R).
select_pos_proof1(rule(Nm, Delta, N-at(At,V,O,Vars), Rs), V, O, Delta, N-at(At,V,O,Vars), rule(Nm, Delta, N-at(At,V,O,Vars), Rs)).


% = select_ant_formula(+Antecedent, +Vertex, +Order, -Gamma, -A, -Delta)
%
% select the (negative) atomic formula indicated by Vertex-Order from the given Antecedent,
% dividing the antecedent into Gamma, A, Delta (Gamma is represented as a difference list)

select_ant_formula([N-at(At,V,O,Vars)|Delta], V, O, [], N-at(At,V,O,Vars), Delta) :-
	!.
select_ant_formula([G|Gs], V, O, [G|Gamma], A, Delta) :-
	select_ant_formula(Gs, V, O, Gamma, A, Delta).

% = node_proofs(+Graph, -Proofs)
%
% for each of the nodes in Graph, retrieve the stored formula and polarity of the node and
% compute the corresponding sequent proof

node_proofs([V|Vs], [P|Ps]) :-
        node_proof1(V, P),
        node_proofs(Vs, Ps).
node_proofs([], []).

node_proof1(vertex(N0, As, _, _), N0-Proof) :-
        node_formula(N0, Pol, F),
        node_proof2(As, F, N0, Pol, Proof),
	proof_diagnostics('~w. ', [N0], Proof),	
	!.

% = node_proof2(+Atoms, +Formula, +NodeNumber, +Polarity, -Proof)
%
% create a Proof using matching Formula to its Atoms

node_proof2([], F, N, _, rule(ax, [N-F], N-F, [])).
node_proof2([A|As], F, N, Pol, Proof) :-
        node_proof3(Pol, [A|As], F, N, Proof).

node_proof3(pos, L, F, N, Proof) :-
        create_pos_proof(F, N, L, [], Proof).
node_proof3(neg, L, F, N, Proof) :-
        max_neg(F, MN0),
	rename_bound_variables(MN0, MN),
        create_neg_proof(F, N, L, [], MN, Proof).

% = max_neg(+Formula, -Conclusion)
%
% given a negative (antecedent) formula, compute the Conclusion of the proof we are computing for it;
% this is (maximal) subformula we reach following a path of negative subformulas.

max_neg(impl(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(forall(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(F, F).

% = create_pos_proof(+NumberedPositiveFormula, +/-AtomsDL, -Proof)

create_pos_proof(N-A, L0, L, Proof) :-
	create_pos_proof(A, N, L0, L, Proof).

% = create_pos_proof(+PositiveFormula, +NodeNumber, +/-AtomsDL, -Proof)

create_pos_proof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax,[M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
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

create_neg_proof(at(A,C,N,Vars), M, [neg(A,C,N,_,Vars)|L], L, at(A,C,N,Vars), rule(ax, [M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
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

% =======================================
% =             Input/output            =
% =======================================

proof_diagnostics(Msg, P) :-
	proof_diagnostics(Msg, [], P).
proof_diagnostics(Msg, Vs, P) :-
   (
	generate_diagnostics(true)
    ->
	format(latex, Msg, Vs),
	latex_proof(P)
    ;
        true
    ).
