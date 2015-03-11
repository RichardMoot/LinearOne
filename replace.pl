:- module(replace, [replace_proofs_labels/4, replace_proof_labels/4, replace_formula/5, replace_graph/6]).

/* I don't believe it's necessary to do replacements inside the subproofs Rs here */

replace_proofs_labels([], _, _, []).
replace_proofs_labels([R0|Rs0], X, Y, [R|Rs]) :-
	replace_proof_labels(R0, X, Y, R),
	replace_proofs_labels(Rs0, X, Y, Rs).

replace_proof_labels(N0-R0, X, Y, N-R) :-
	replace_item(N0, X, Y, N),
	replace_proof_labels(R0, X, Y, R).
replace_proof_labels(rule(N, As0, F0, Rs), X, Y, rule(N, As, F, Rs)) :-
	replace_antecedent_labels(As0, X, Y, As),
	replace_formula_labels(F0, X, Y, F).

replace_antecedent_labels([], _, _, []).
replace_antecedent_labels([A|As], X, Y, [B|Bs]) :-
	replace_formula_labels(A, X, Y, B),
	replace_antecedent_labels(As, X, Y, Bs).

replace_formula_labels(N0-F0, X, Y, N-F) :-
	replace_item(N0, X, Y, N),
	replace_formula_labels(F0, X, Y, F).
replace_formula_labels(at(A,B,C,D), _, _, at(A,B,C,D)).
replace_formula_labels(impl(A0,B0), X, Y, impl(A,B)) :-
	replace_formula_labels(A0, X, Y, A),
	replace_formula_labels(B0, X, Y, B).
replace_formula_labels(p(A0,B0), X, Y, p(A,B)) :-
	replace_formula_labels(A0, X, Y, A),
	replace_formula_labels(B0, X, Y, B).
replace_formula_labels(forall(V,A0), X, Y, forall(V,A)) :-
	replace_formula_labels(A0, X, Y, A).
replace_formula_labels(exists(V,A0), X, Y, exists(V,A)) :-
	replace_formula_labels(A0, X, Y, A).

% = replace(+InFormula, +Index, ?IndexedFormula, +InList, ?OutList)
%
% replaces Index-Formula in InList by IndexedFormula in OutList,
% using forced-choice determinism

replace_formula(F0, N, F, L0, L) :-
%   (
%        F0 = at(_,_,_,_)
%   ->
%	select(F0, L0, F, L)
%   ;
        select(N-F0, L0, F, L),
%   ),
        !.


%% replace_list(F, N, List0, R, List) :-
%% 	replace_list(List0, N-F, R, List). 
%% replace_list([], _, _, []).
%% replace_list([A|As], C, D, [B|Bs]) :-
%%     (
%%        A = C
%%     ->
%%        B = D
%%     ;
%%        B = A
%%     ),
%%        replace_list(As, C, D, Bs).


%= replace_graph(+InGraph, +InPars, +InNodeNum, ?OutNodeNum, -OutGraph, OutPars)

replace_graph(Graph0, Par0, N0, N, Graph, Par) :-
	replace(Graph0, N0, N, Graph),
	replace_pars(Par0, N0, N, Par).

% = replace(+InGraph,+InNodeNum,?OutNodeNum,-OutGraph)
%
% renumbers InNode for OutNode throughout Graph.

replace([], _, _, []).
replace([vertex(N,As,FVs,Ps0)|Rest0], N0, N1, [vertex(N,As,FVs,Ps)|Rest]) :-
        replace_pars(Ps0, N0, N1, Ps),
        replace(Rest0, N0, N1, Rest).

replace_pars([], _, _, []).
replace_pars([P0|Ps0], N0, N1, [P|Ps]) :-
        replace_par(P0, N0, N1, P),
        replace_pars(Ps0, N0, N1, Ps).

replace_par(par(X,Y), N0, N1, par(V,W)) :-
        replace_item(X, N0, N1, V),
        replace_item(Y, N0, N1, W).
replace_par(univ(M,X), N0, N1, univ(M,Y)) :-
        replace_item(X, N0, N1, Y).

replace_item(X, N0, N1, Y) :-
    (
	X = N0
    ->
	Y = N1
    ;
        Y = X
    ).

