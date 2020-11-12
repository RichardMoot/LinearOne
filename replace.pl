% -*- Mode: Prolog -*-

:- module(replace, [replace_proofs_labels/4,
		    replace_proof_labels/4,
		    replace_formula/5,
		    replace_graph/6,
		    rename_bound_variable/4,
		    rename_bound_variables/2]).

:- use_module(ordset, [ord_key_insert/4, ord_key_member/3]).

% =======================================
% =   Auxiliary replacement predicates  =
% =======================================

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
        select(N-F0, L0, F, L),
        !.

%= replace_graph(+InGraph, +InPars, +InNodeNum, ?OutNodeNum, -OutGraph, OutPars)

replace_graph(Graph0, Par0, N0, N, Graph, Par) :-
	replace(Graph0, N0, N, Graph),
	replace_pars(Par0, N0, N, Par).

% = replace(+InGraph,+InNodeNum,?OutNodeNum,-OutGraph)
%
% renumbers InNodeNum for OutNodeNum throughout Graph.

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


% = rename_bound_variable(+LabeledFormulaIn, +InVariable, ?OutVariable, ?LabeldFormulaOut)
%
% true if LabeledFormulaOut is identical to LabeledFormulaIn except that all bound
% occurrences of InVariable have been renamed to OutVariable.

rename_bound_variable(N-F0, X, Y, N-F) :-
	rename_bound_variable(F0, X, Y, F).
rename_bound_variable(at(A,C,N,Vars0), X, Y, at(A,C,N,Vars)) :-
	rename_bound_var_list(Vars0, X, Y, Vars).
rename_bound_variable(forall(Z,A0), X, Y, forall(V,A)) :-
	rename_bound_var(Z, X, Y, V),
	rename_bound_variable(A0, X, Y, A).
rename_bound_variable(exists(Z,A0), X, Y, exists(V,A)) :-
	rename_bound_var(Z, X, Y, V),
	rename_bound_variable(A0, X, Y, A).
rename_bound_variable(impl(A0,B0), X, Y, impl(A,B)) :-
	rename_bound_variable(A0, X, Y, A),
	rename_bound_variable(B0, X, Y, B).
rename_bound_variable(p(A0,B0), X, Y, p(A,B)) :-
	rename_bound_variable(A0, X, Y, A),
	rename_bound_variable(B0, X, Y, B).


rename_bound_var_list([], _, _, []).
rename_bound_var_list([V|Vs], X, Y, [W|Ws]) :-
	rename_bound_var(V, X, Y, W),
	rename_bound_var_list(Vs, X, Y, Ws).

rename_bound_var(V, X, Y, W) :-
   (
	V == X 
   ->
	W = Y
   ;
        compound(V), 
        V =.. [F|As0],
	F \= '$VAR'	      
   ->
        rename_bound_var_list(As0, X, Y, As),
	W =.. [F|As]
   ;		      
	W = V
   ).

    
rename_bound_variables(F0, F) :-
	rename_bound_variables(F0, [], F).
rename_bound_variables(N-F0, Map, N-F) :-
	rename_bound_variables(F0, Map, F).
rename_bound_variables(at(A,C,N,Vars0), Map, at(A,C,N,Vars)) :-
	rename_bound_var_list(Vars0, Map, Vars).
rename_bound_variables(forall(Z,A0), Map0, forall(V,A)) :-
	ord_key_insert(Map0, Z, V, Map),
	rename_bound_variables(A0, Map, A).
rename_bound_variables(exists(Z,A0), Map0, exists(V,A)) :-
	ord_key_insert(Map0, Z, V, Map),
	rename_bound_variables(A0, Map, A).
rename_bound_variables(impl(A0,B0), Map, impl(A,B)) :-
	rename_bound_variables(A0, Map, A),
	rename_bound_variables(B0, Map, B).
rename_bound_variables(p(A0,B0), Map, p(A,B)) :-
	rename_bound_variables(A0, Map, A),
	rename_bound_variables(B0, Map, B).

rename_bound_var_list([], _, []).
rename_bound_var_list([V|Vs], Map, [W|Ws]) :-
	rename_bound_var(V, Map, W),
	rename_bound_var_list(Vs, Map, Ws).

rename_bound_var(V, Map, W) :-
   (
	ord_key_member(V, Map, W) 
   ->
	true
   ;
	W = V
   ).
