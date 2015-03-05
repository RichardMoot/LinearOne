:- use_module(ordset, [ord_union/3,ord_delete/3,ord_key_member/3,ord_key_insert/4]).
:- use_module(portray_graph_tikz, [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).
:- use_module(translations, [translate_lambek/3,translate_displacement/3,translate_hybrid/6]).
:- use_module(latex, [latex_proof/1,proof_header/0,proof_footer/0,latex_semantics/1]).
:- use_module(sem_utils, [substitute_sem/3,reduce_sem/2]).
:- use_module(lexicon, [parse/2]).

:- dynamic '$PROOFS'/1, '$AXIOMS'/1.
:- dynamic node_formula/3.

generate_diagnostics(false).

portray(neg(F, X, L)) :-
	atom(F),
	Term =.. [F|L],
	format('-~p ~p',[Term,X]).
portray(pos(F, X, L)) :-
	atom(F),
	Term =.. [F|L],
	format('+~p ~p',[Term,X]).
portray(at(X, Vs)) :-
	atom(X),
	Term =.. [X|Vs],
	print(Term).
portray(at(X, I1, I2, Vs)) :-
	atom(X),
	Term =.. [X|Vs],
	format('~w{~w,~w}', [Term,I1,I2]).
portray(impl(A,B)) :-
	format('(~p -o ~p)', [A,B]).
portray(rule(N,A,B,Ps)) :-
	Ps \== [],
	format('rule(~p,~p,~p,...)', [N,A,B]).
portray(appl(appl(F,Y),X)) :-
	atom(F),
	!,
	Term =.. [F,X,Y],
	print(Term).
portray(appl(F,X)) :-
	atom(F),
	!,
	Term =.. [F,X],
	print(Term).
portray(appl(M,N)) :-
	format('(~p ~p)', [M,N]).
portray(lambda(X,M)) :-
        format('(~p^~p)', [X,M]).
portray(bool(P,B,Q)) :-
	format('(~p ~p ~p)', [P,B,Q]).



prove(Antecedent, Goal) :-
	prove(Antecedent, Goal, []).

prove(Antecedent, Goal, LexSem) :-
	/* LaTeX output */
	graph_header,
	proof_header,
	/* reset counters */
	retractall('$PROOFS'(_)),
	assert('$PROOFS'(0)),
	retractall('$AXIOMS'(_)),
	assert('$AXIOMS'(0)),
	/* end initialisation */
        unfold_sequent(Antecedent, Goal, Vs0, _W, Sem0),
	/* keep a copy of the initial graph (before any unificiations) for later proof generation */
	copy_term(Vs0, Vs),
        prove1(Vs0, Trace),
	/* proof found */
	/* update proof statistics */
	'$PROOFS'(N0),
	N is N0 + 1,
	retractall('$PROOFS'(_)),
	assert('$PROOFS'(N)),
	substitute_sem(LexSem, Sem0, Sem1),
	reduce_sem(Sem1, Sem),
	format(user_error, '~NSemantics ~w: ~p~n', [N,Sem]),
	latex_semantics(Sem),
	/* generate a LaTeX proof */
	generate_proof(Vs, Trace),
	/* find alternatives using failure driven loop */
	fail.
prove(_, _, _) :-
	/* print final statistics and generate pdf files */
	'$AXIOMS'(A),
	'$PROOFS'(N),
	write_axioms(A),
	write_proofs(N),
	/* LaTeX graphs */
	graph_footer(N),
	/* LaTeX proofs */
	proof_footer.


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

generate_proof(Vs, Trace) :-
	node_proofs(Vs, Ps),
	combine_proofs(Trace, Ps, Proof),
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
	select_pos_proof(Ps0, Ps1, AtV1, AtO1, DeltaP, A2, P2),
	proof_diagnostics('~NPos:~2n', P2),
	select_neg_proof(Ps1, Ps2, AtV0, AtO0, Gamma, A1, Delta, C, P1),
	proof_diagnostics('~NNeg:~2n', P1),
        append(Gamma, DeltaP, GDP1),
	append(GDP1, Delta, GDP),
	unify_atoms(A1, A2),
	trivial_cut_elimination(P1, P2, GDP, C, Rule),
	replace_proofs_labels([N0-Rule|Ps2], N1, N0, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([Next|_], CurrentProofs, Proof) :-
	/* dump all partial proofs in case of failure (useful for inspection) */
	format(user_error, '~N{Error: proof generation failed!}~nNext:~p~2n', [Next]),
	member(Proof, CurrentProofs).

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


subproofs(_-R, S) :-
        subproofs(R, S).
subproofs(rule(_,_,_,S), S).

rulename(_-R, N) :-
        rulename(R, N).
rulename(rule(N,_,_,_), N).


is_axiom(_-R) :-
        is_axiom(R).
is_axiom(rule(ax,_,_,_)).


combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P1 = rule(Nm, Gamma, N0-exists(var(V),N1-A), _),
	P2 = rule(_, Delta0, C, _),
	!,
	%	rename_bound_variables(A, AA),
	A = AA,
	select_formula(AA, N1, Delta0, Delta),
	replace_formula(AA, N1, N1-exists(var(V),N1-AA), Delta0, Delta1),
	append(Gamma, Delta, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(el, GD, C, [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(el, Delta1, C, [P2])])
   ).
combine_univ(P1, P2, _N0, N1, V, N1-Rule) :-
        P2 = rule(_, Gamma, A, _),
	P1 = rule(Nm, Delta, C, _),
%	rename_bound_variables(A, AA),
	A = AA,
	append(Delta0, [_-forall(var(V),AA)|Delta1], Delta),
	append(Delta0, Gamma, GD0),
	append(GD0, Delta1, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(fr,GD,N1-forall(var(V),N1-AA), [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(fr,Gamma,N1-forall(var(V),N1-A), [P2])])
   ).
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(Nm, Gamma, N0-p(N1-A, N1-B), _),
        P2 = rule(_, Delta0, C, _),
	!,
%        rename_bound_variables(A, AA),
%	rename_bound_variables(B, BB),
	A = AA,
	B = BB,
	select_formula(BB, N1, Delta0, Delta1),
	select_formula(AA, N1, Delta1, Delta),
	replace_formula(AA, N1, N1-p(N1-AA,N1-BB), Delta1, Delta2),
	append(Gamma, Delta, GD),		  
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(pl, GD, C, [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(pl, Delta2, C, [P2])])
   ).
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(Nm, Gamma, A, _),
	P2 = rule(_, Delta0, _B, _),
	append(Gamma0, [N0-impl(N1-C,N1-D)|Gamma1], Gamma),
	rename_bound_variables(C, CC),
	select_formula(CC, N1, Delta0, Delta),
	append(Gamma0, Delta, GD0),
	append(GD0, Gamma1, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(ir, GD, A, [P2])
   ;		  
        Rule = rule(cut, GD, A, [P1,rule(ir, Delta, impl(N1-C,N1-D), [P2])])
   ).

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

unify_atoms(_-at(A, _, _, Vs), _-at(A, _, _, Vs)).

select_neg_proof([P|Ps], Ps, V, O, Gamma, A, Delta, C, Proof) :-
	select_neg_proof1(P, V, O, Gamma, A, Delta, C, Proof),
	!.
select_neg_proof([P|Ps], [P|Rs], V, O, Gamma, A, Delta, C, Proof) :-
	select_neg_proof(Ps, Rs, V, O, Gamma, A, Delta, C, Proof).

select_neg_proof1(_-P, V, O, Gamma, A, Delta, C, R) :-
	select_neg_proof1(P, V, O, Gamma, A, Delta, C, R).
select_neg_proof1(rule(Nm, GammaADelta, C, Ps), V, O, Gamma, A, Delta, C, rule(Nm, GammaADelta, C, Ps)) :-
	select_ant_formula(GammaADelta, V, O, Gamma, [], A, Delta).

select_pos_proof([P|Ps], Ps, V, O, Delta, A, Proof) :-
	select_pos_proof1(P, V, O, Delta, A, Proof),
	!.
select_pos_proof([P|Ps], [P|Rs], V, O, Delta, A, Proof) :-
	select_pos_proof(Ps, Rs, V, O, Delta, A, Proof).

select_pos_proof1(_-P, V, O, Delta, A, R) :-
	select_pos_proof1(P, V, O, Delta, A, R).
select_pos_proof1(rule(Nm, Delta, N-at(At,V,O,Vars), Rs), V, O, Delta, N-at(At,V,O,Vars), rule(Nm, Delta, N-at(At,V,O,Vars), Rs)).

select_ant_formula([N-at(At,V,O,Vars)|Delta], V, O, Gamma, Gamma, N-at(At,V,O,Vars), Delta) :-
	!.
select_ant_formula([G|Gs], V, O, [G|Gamma0], Gamma, A, Delta) :-
	select_ant_formula(Gs, V, O, Gamma0, Gamma, A, Delta).

	

node_proofs([V|Vs], [P|Ps]) :-
        node_proof1(V, P),
        node_proofs(Vs, Ps).
node_proofs([], []).

node_proof1(vertex(N0, As, _, _), N0-Proof) :-
        node_formula(N0, Pol, F),
        node_proof2(As, F, N0, Pol, Proof),
	proof_diagnostics('~w. ', [N0], Proof),	
	!.

node_proof2([], F, N, _, rule(ax, [N-F], N-F, [])).
node_proof2([A|As], F, N, Pol, Proof) :-
        node_proof3(Pol, [A|As], F, N, Proof).

node_proof3(pos, L, F, N, Proof) :-
        create_pos_proof(F, N, L, [], Proof).
node_proof3(neg, L, F, N, Proof) :-
        max_neg(F, MN0),
	rename_bound_variables(MN0, MN),
        create_neg_proof(F, N, L, [], MN, Proof).

max_neg(impl(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(forall(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(F, F).

create_pos_proof(N-A, L0, L, Proof) :-
	create_pos_proof(A, N, L0, L, Proof).

create_pos_proof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax,[M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
	!.
create_pos_proof(exists(X,N-A), N, L0, L, rule(er, Gamma, N-exists(Y,N-A3), [ProofA])) :-
        !,
	/* rename to make sure bound variable isn't unified */
	rename_bound_variables(A, A2),
	rename_bound_variable(exists(X,N-A2), X, Y, exists(Y,N-A3)),
        create_pos_proof(A, N, L0, L, ProofA),
        ProofA = rule(_, Gamma, N-A2, _).
create_pos_proof(p(N-A,N-B), N, L0, L, rule(pr, GD, N-p(N-A,N-B), [P1,P2])) :-
        !,
        create_pos_proof(A, N, L0, L1, P1),
        create_pos_proof(B, N, L1, L, P2),
        P1 = rule(_, Gamma, _, _),
        P2 = rule(_, Delta, _, _),
        append(Gamma, Delta, GD).
% complex subformula
create_pos_proof(F, N, L, L, rule(ax, [N-F], N-F, [])).

create_neg_proof(N-A, L0, L, Neg, Proof) :-
	create_neg_proof(A, N, L0, L, Neg, Proof).
create_neg_proof(at(A,C,N,Vars), M, [neg(A,C,N,_,Vars)|L], L, at(A,C,N,Vars), rule(ax, [M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
        !.
create_neg_proof(impl(N-A,N-B), N, L0, L, Neg, rule(il, GD, N-Neg, [ProofA,ProofB])) :-
        !,
        create_neg_subproof(A, N, L0, L1, ProofA),
	create_neg_proof(B, N, L1, L, Neg, ProofB),
%	rename_bound_variables(A, A2),
	rename_bound_variables(B, B2),
	copy_term(B2, B3),
%	format(user_error, '~NB :~w~nB2: ~w~n', [B,B2]),
	ProofA = rule(_, Gamma, N-A3, _),
	ProofB = rule(_, Delta, _, _),
%	replace_list(B3, N, Delta0, _, Delta),
	select_formula(B, N, Delta, Delta_B),
	%	format(user_error, '~NB :~w~nB2: ~w~n', [B,B2]),
	% B2 can have instantiated forall, so use B3
	append(Gamma, [N-impl(N-A3,N-B3)|Delta_B], GD).
create_neg_proof(forall(X,N-A), N, L0, L, Neg, rule(fl, GammaP, C, [ProofA])) :-
        !,
	rename_bound_variables(A, A2),
        create_neg_proof(A, N, L0, L, Neg, ProofA),
        ProofA = rule(_, Gamma, C, _),
	/* rename to make sure bound variables aren't unified */
	replace_list(A2, N, Gamma, N-forall(Y,N-A3), GammaP),
	rename_bound_variable(forall(X,N-A2), X, Y, forall(Y,N-A3)).
create_neg_proof(F, N, L, L, _, rule(ax, [N-F], N-F, [])).

create_neg_subproof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax, [M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
        !.
create_neg_subproof(p(N-A0,N-B0), N, L0, L, rule(pr, ProofA, ProofB)) :-
	!,
	rename_bound_variables(A0, A),
	rename_bound_variables(B0, B),
	create_neg_subproof(A, N, L0, L1, ProofA),
	create_neg_subproof(B, N, L1, L, ProofB).
create_neg_subproof(A0, N, L, L, rule(ax, [N-A], N-A, [])) :-
	rename_bound_variables(A0, A).


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

print_list([]).
print_list([A|As]) :-
	format(user_error, '~p~n', [A]),
	print_list(As).

select_formula(F, N, L0, L) :-
%   (
%        F = at(_,_,_,_)
%   ->
%	select(F, L0, L)
%   ;
        select(N-F, L0, L),
%   ),
        !.

replace_formula(F0, N, F, L0, L) :-
   (
        F0 = at(_,_,_,_)
   ->
	select(F0, L0, F, L)
   ;
        select(N-F0, L0, F, L)
   ),
        !.


%replace_list(at(A,C,N,Vars), _, List0, R, List) :-
%	!,
%	replace_list(List0, at(A,C,N,Vars), R, List).
replace_list(F, N, List0, R, List) :-
	replace_list(List0, N-F, R, List). 
replace_list([], _, _, []).
replace_list([A|As], C, D, [B|Bs]) :-
    (
       A = C
    ->
       B = D
    ;
       B = A
    ),
       replace_list(As, C, D, Bs).


write_proofs(P) :-
   (
       P =:= 0
   ->
       format(user_output, 'No proofs found!~n', [])
   ;
       P =:= 1
   ->
       format(user_output, '1 proof found.~n', [])
   ;
       format(user_output, '~p proofs found.~n', [P])
   ).
write_axioms(A) :-
   (
       A =:= 0
   ->
       format(user_output, 'No axioms performed!~n', [])
   ;
       A =:= 1
   ->
       format(user_output, '1 axiom performed.~n', [])
   ;
       format(user_output, '~p axioms performed.~n', [A])
   ).


prove1([vertex(_, [], _, [])], []) :-
        !.
prove1(G0, [ax(N0,AtV0,AtO0,N1,AtV1,AtO1)|Rest0]) :-
        portray_graph(G0),
        select(vertex(N0, [A|As0], FVs0, []), G0, G1),
        select(neg(At,AtV0,AtO0,X,Vars), [A|As0], As),
	/* forced choice for negative atom */
	/* TODO: replace with choice of atom with the */
        /* least possible links */
	!,
	select(vertex(N1, [B|Bs0], FVs1, Ps), G1, G2),
	select(pos(At,AtV1,AtO1,X,Vars), [B|Bs0], Bs),
        \+ cyclic(Ps, G2, N0),
	'$AXIOMS'(Ax0),
	Ax is Ax0 + 1,
	retractall('$AXIOMS'(_)),
	assert('$AXIOMS'(Ax)),
	append(As, Bs, Cs),
	merge_fvs(FVs0, FVs1, FVs),
	replace(G2, N0, N1, G3),
	replace_pars(Ps, N0, N1, Rs),
	G4 = [vertex(N1,Cs,FVs,Rs)|G3],
        portray_graph(G4),
	contract(G4, G, Rest0, Rest),
	connected(G),
	prove1(G, Rest).
prove1(G1, _) :-
        format(user_error, '~nFailed!~n', []),
        portray_graph(G1),
        fail.

% test for cyclicity
% G2 contains unvisited nodes
% P contains paths from current node
% N is the node to reach for a cycle.

cyclic([P|_], G2, N) :-
    cyclic1(P, G2, N).
cyclic([_|Ps], G2, N) :-
    cyclic(Ps, G2, N).

cyclic1(par(M,P), G2, N) :-
    (
       N =:= M
    ;
       N =:= P
    ;
       select(vertex(M,_,_,Ps), G2, G3),
       cyclic(Ps, G3, N)
    ;
       P \== M,
       select(vertex(P,_,_,Ps), G2, G3),
       cyclic(Ps, G3, N)
    ).
cyclic1(univ(_,M), G2, N) :-
    (
       N =:= M
     ;
       select(vertex(M,_,_,Ps), G2, G3),
       cyclic(Ps, G3, N)
    ).        

% = connected(+Graph)
%
% true if Graph is connected or at least can be made connected
% by vertex identifications (corresponding to axioms)

connected([V|Vs]) :-
   (
       Vs = []
   ->
       /* a single-node graph is connected */
       true
   ;
       connected1([V|Vs])
   ).

connected1([]).
connected1([vertex(_,As,_,Ps)|Vs]) :-
    (
        As = []
    ->  /* in a multiple-node graph, if a node has no */
        /* atoms, it must have a link */
        Ps = [_|_]
    ;
        true
    ),
    connected1(Vs).

% merge two sets of free variables
% remove variables already instantiated (these have an integer value)
% we need to sort again (since variable instantiations/unifications may
% have changed term order)

merge_fvs(Vs0, Ws0, Zs) :-
    reduce_fvs(Vs0, Vs1),
    sort(Vs1, Vs),
    reduce_fvs(Ws0, Ws1),
    sort(Ws1, Ws),
    ord_union(Vs, Ws, Zs).

reduce_fvs([], []).
reduce_fvs([V|Vs], Ws) :-
    (
        integer(V)
    ->
        reduce_fvs(Vs, Ws)
    ;
        Ws = [V|Ws0],
        reduce_fvs(Vs, Ws0)
    ).

% = contract(+InGraph,-OutGraph)
%
% perform all valid contractions on InGraph producing OutGraph;
% these are Danos-style contractions, performed in a first-found
% search.

contract(G0, G, L0, L) :-
        contract1(G0, G1, L0, L1),
        portray_graph(G1),
        !,
        contract(G1, G, L1, L).
contract(G, G, L, L).

% par contraction
contract1(G0, [vertex(N1,Cs,FVs,Rs)|G], [N0-par(N1)|Rest], Rest) :-
        select(vertex(N0, As, FVsA, Ps0), G0, G1),
        select(par(N1, N1), Ps0, Ps),
	select(vertex(N1, Bs, FVsB, Qs), G1, G2),
	\+ cyclic(Qs, G2, N0),
	!,
	append(As, Bs, Cs),
	append(Ps, Qs, Rs0),
	merge_fvs(FVsA, FVsB, FVs),
	replace_pars(Rs0, N0, N1, Rs),
	replace(G2, N0, N1, G).
% forall contraction
contract1(G0, [vertex(N1,Cs,FVs,Rs)|G], [N0-univ(U,N1)|Rest], Rest) :-
        select(vertex(N0, As, FVsA, Ps0), G0, G1),
        select(univ(U, N1), Ps0, Ps),
	select(vertex(N1, Bs, FVsB, Qs), G1, G2),
	no_occurrences1(FVsA, U),
	no_occurrences(G2, U),
	!,
	append(As, Bs, Cs),
	append(Ps, Qs, Rs0),
	merge_fvs(FVsA, FVsB, FVs),
	replace_pars(Rs0, N0, N1, Rs),
	replace(G2, N0, N1, G).


% = no_occurrences(+Graph, +VarNum)
%
% walks through +Graph and checks that none of its vertices
% has the variable +VarNum in their list of free variables.

no_occurrences([], _).
no_occurrences([vertex(_, _, FVs, _)|Rest], U) :-
        no_occurrences1(FVs, U),
        no_occurrences(Rest, U).

no_occurrences1([], _).
no_occurrences1([V|Vs], U) :-
        var(U) \== V,
        no_occurrences1(Vs, U).


% = replace(+InGraph,+InNodeNum,+OutNodeNum,+Outgraph)
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

% = unfolding
%
% transforms sequents, antecedents and (polarized) formulas into graphs

unfold_sequent(List, Goal, Vs0, W, Sem) :-
        retractall(node_formula(_,_,_)),
	unfold_antecedent(List, 0, W, 0, N0, 0, M, Vs0, [vertex(N0,As,FVsG,Es)|Vs1]),
	N is N0 + 1,
	number_subformulas_pos(Goal, N0, N, _, _-NGoal),
        assert(node_formula(N0, pos, NGoal)),
	free_vars_p(Goal, FVsG),
	unfold_pos(NGoal, Sem, M, _, As, [], Es, [], Vs1, []).

unfold_antecedent([], W, W, N, N, M, M, Vs, Vs).
unfold_antecedent([F|Fs], W0, W, N0, N, M0, M, [vertex(N0,As,FVsF,Es)|Vs0], Vs) :-
        N1 is N0 + 1,
        W1 is W0 + 1,
	free_vars_n(F, FVsF),
	number_subformulas_neg(F, N0, N1, N2, _-NF),
        assert(node_formula(N0, neg, NF)),
	unfold_neg(NF, '$VAR'(W0), M0, M1, As, [], Es, [], Vs0, Vs1),
	unfold_antecedent(Fs, W1, W, N2, N, M1, M, Vs1, Vs).

% = number_subformulas_neg(+Formula, +CurrentNodeNumber, +NextNodeNumberIn, -NextNodeNumberOut, -NumberFormula)
%
% assigns node numbers to all subformulas of Formula, allowing us to designate
% all (sub-)formula occurrences in a sequent by a unique node number, and in the
% case of atomic formulas a combination of node-index (where index is a
% left-to-right numbering of the atomic subformulas at a node).

number_subformulas_neg(F, C, N0, N, NF) :-
        number_subformulas_neg(F, C, N0, N, 1, _, NF).

number_subformulas_neg(at(A,Vars), C, N, N, M0, M, C-at(A,C,M0,Vars)) :-
        M is M0 + 1.
number_subformulas_neg(forall(X,A), C, N0, N, M0, M, C-forall(X,NA)) :-
	number_subformulas_neg(A, C, N0, N, M0, M, NA).
number_subformulas_neg(exists(X,A), C, N0, N, M, M, C-exists(X,NA)) :-
	N1 is N0 + 1,
	number_subformulas_neg(A, N0, N1, N, 1, _, NA).
number_subformulas_neg(p(A,B), C, N0, N, M, M, C-p(NA,NB)) :-
	N1 is N0 + 1,
	N2 is N1 + 1,
	number_subformulas_neg(A, N0, N2, N3, 1, _, NA),
	number_subformulas_neg(B, N1, N3, N, 1, _, NB).
number_subformulas_neg(impl(A,B), C, N0, N, M0, M, C-impl(NA,NB)) :-
	number_subformulas_pos(A, C, N0, N1, M0, M1, NA),
	number_subformulas_neg(B, C, N1, N, M1, M, NB).

number_subformulas_pos(F, C, N0, N, NF) :-
        number_subformulas_pos(F, C, N0, N, 1, _, NF).

number_subformulas_pos(at(A,Vars), C, N, N, M0, M, C-at(A,C,M0,Vars)) :-
	M is M0 + 1.
number_subformulas_pos(forall(X,A), C, N0, N, M, M, C-forall(X,NA)) :-
	N1 is N0 + 1,
	number_subformulas_pos(A, N0, N1, N, 1, _, NA).
number_subformulas_pos(exists(X,A), C, N0, N, M0, M, C-exists(X,NA)) :-
	number_subformulas_pos(A, C, N0, N, M0, M, NA).
number_subformulas_pos(p(A,B), C, N0, N, M0, M, C-p(NA,NB)) :-
	number_subformulas_pos(A, C, N0, N1, M0, M1, NA),
	number_subformulas_pos(B, C, N1, N, M1, M, NB).
number_subformulas_pos(impl(A,B), C, N0, N, M, M, C-impl(NA,NB)) :-
	N1 is N0 + 1,
	N2 is N1 + 1,	
	number_subformulas_neg(A, N0, N2, N3, 1, _, NA),
	number_subformulas_pos(B, N1, N3, N, 1, _, NB).

%= unfold(+Formula, Sem, VertexNo, VarNo, AtomsDL, EdgesDL, VerticesDL)

%unfold_neg(N-F, X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
%        unfold_neg(F, N, X, M0, M, As0, As, Es0, Es, Vs0, Vs).

unfold_neg(at(A,C,N,Vars), X, M, M, [neg(A,C,N,X,Vars)|As], As, Es, Es, Vs, Vs).
unfold_neg(forall(_,_-A), X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_neg(A, X, M0, M, As0, As, Es0, Es, Vs0, Vs).
unfold_neg(exists(var(M0),N-A), X, M0, M, As, As, [univ(M0,N)|Es], Es, [vertex(N,Bs,FVsA,Fs)|Vs0], Vs) :-
        assert(node_formula(N, neg, A)),
        free_vars_n(A, FVsA),
	M1 is M0 + 1,
	unfold_neg(A, X, M1, M, Bs, [], Fs, [], Vs0, Vs).
unfold_neg(p(N0-A,N1-B), X, M0, M, As, As, [par(N0,N1)|Es], Es, [vertex(N0,Bs,FVsA,Fs),vertex(N1,Cs,FVsB,Gs)|Vs0], Vs) :-
        assert(node_formula(N0, neg, A)),
        assert(node_formula(N1, neg, B)),
        free_vars_n(A, FVsA),
        free_vars_n(B, FVsB),
	unfold_neg(A, pi1(X), M0, M1, Bs, [], Fs, [], Vs0, Vs1),
	unfold_neg(B, pi2(X), M1, M, Cs, [], Gs, [], Vs1, Vs).
unfold_neg(impl(_-A,_-B), X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_pos(A, Y, M0, M1, As0, As1, Es0, Es1, Vs0, Vs1),
	unfold_neg(B, appl(X,Y), M1, M, As1, As, Es1, Es, Vs1, Vs).

unfold_pos(at(A,C,N,Vars), X, M, M, [pos(A,C,N,X,Vars)|As], As, Es, Es, Vs, Vs).
unfold_pos(forall(var(M0),N0-A), X, M0, M, As, As, [univ(M0,N0)|Es], Es, [vertex(N0,Bs,FVsA,Fs)|Vs0], Vs) :-
        assert(node_formula(N0, pos, A)),
        free_vars_p(A, FVsA),
	M1 is M0 + 1,
	unfold_pos(A, X, M1, M, Bs, [], Fs, [], Vs0, Vs).
unfold_pos(exists(_,_-A), X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_pos(A, X, M0, M, As0, As, Es0, Es, Vs0, Vs).
unfold_pos(p(_-A,_-B), pair(X,Y), M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_pos(A, X, M0, M1, As0, As1, Es0, Es1, Vs0, Vs1),
	unfold_pos(B, Y, M1, M, As1, As, Es1, Es, Vs1, Vs).
unfold_pos(impl(N0-A,N1-B), lambda(X,Y), M0, M, As, As, [par(N0,N1)|Es], Es, [vertex(N0,Bs,FVsA,Fs),vertex(N1,Cs,FVsB,Gs)|Vs0], Vs) :-
        assert(node_formula(N0, neg, A)),
        assert(node_formula(N1, pos, B)),
        free_vars_n(A, FVsA),
        free_vars_p(B, FVsB),
	unfold_neg(A, X, M0, M1, Bs, [], Fs, [], Vs0, Vs1),
	unfold_pos(B, Y, M1, M, Cs, [], Gs, [], Vs1, Vs).

% = free_vars_n(+Formula, -SetOfFreeVars)
%
% true if Formula (of negative polariy) has
% SetOfFreeVars, but with a slight twist: all
% variables bound by a tensor prefix are
% considered free. For example, a prefix of
% universal quantifiers is removed (and, in
% general, any negative forall/impl and
% postive exists/prod); this is the implicit
% tensor contraction rule).

free_vars_n(_-A, Vars) :-
        free_vars_n(A, Vars).
free_vars_n(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars_n(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars_n(p(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_n(impl(A,B), Vars) :-
        free_vars_p(A, Vars1),
        free_vars_n(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_n(forall(_,A), Vars) :-
        free_vars_n(A, Vars).
free_vars_n(exists(X,A), Vars) :-
       free_vars(A, Vars0),
       ord_delete(Vars0, X, Vars).

% = free_vars_p(+Formula, -SetOfFreeVars)
%
% true if Formula (of positive polariy) has
% SetOfFreeVars, but with a slight twist: all
% variables bound by a tensor prefix are
% considered free (this is the implicit tensor
% contraction rule).

free_vars_p(_-A, Vars) :-
        free_vars_p(A, Vars).
free_vars_p(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars_p(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars_p(p(A,B), Vars) :-
        free_vars_p(A, Vars1),
        free_vars_p(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_p(impl(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_p(exists(_,A), Vars) :-
        free_vars_p(A, Vars).
free_vars_p(forall(X,A), Vars) :-
        free_vars(A, Vars0),
        ord_delete(Vars0, X, Vars).

% = free_vars(+Formula, -SetOfFreeVars)
%
% true if Formula has SetOfFreeVars under the
% standard interpretation of free/bound.

free_vars(_-A, Vars) :-
        free_vars(A, Vars).
free_vars(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars(p(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars(impl(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars(exists(X,A), Vars) :-
        free_vars(A, Vars0),
	ord_delete(Vars0, X, Vars).
free_vars(forall(X,A), Vars) :-
        free_vars(A, Vars0),
        ord_delete(Vars0, X, Vars).

% = print_trace(+Stream, +List).

print_trace(Stream, [A|As]) :-
        format(Stream, '~n= Proof trace =~n', []),
        print_trace(As, A, Stream).

print_trace([], A, Stream) :-
        format(Stream, '~p~n= End of trace =~2n', [A]).
print_trace([B|Bs], A, Stream) :-
        format(Stream, '~p~n', [A]),
        print_trace(Bs, B, Stream).


% = some test predicates

test :-
        /* this should fail ! */
	prove([forall(X,exists(Y,at(f,[X,Y])))], exists(V,forall(W,at(f,[W,V])))).
test0 :-
	prove([exists(X,forall(Y,at(f,[X,Y])))], forall(V,exists(W,at(f,[W,V])))).

test1 :-
        translate_lambek(p(dr(at(np),at(n)),at(n)), [0,1], F),
        prove([F], at(np, [0,1])).

test2 :-
	prove([at(np,[0,1]),forall(X,impl(at(np,[X,1]),at(s,[X,2])))], at(s,[0,2])).

test3 :-
	prove([forall(Y,forall(Z,impl(impl(at(np,[0,1]),at(s,[Y,Z])),at(s,[Y,Z])))),forall(X,impl(at(np,[X,1]),at(s,[X,2])))], at(s,[0,2])).

test4 :-
        translate_hybrid(at(np), lambda(X,appl(john,X)), john, 0, 1, John),
	translate_hybrid(h(h(at(s),at(np)),at(np)), lambda(P,lambda(Q,lambda(Z,appl(Q,appl(loves,appl(P,Z)))))), loves, 1, 2, Loves),
        translate_hybrid(at(np), lambda(V,appl(mary,V)), mary, 2, 3, Mary),
	prove([John, Loves, Mary], at(s, [0,3])).

test5 :-
        translate_hybrid(at(np), lambda(X,appl(john,X)), john, 0, 1, John),
	translate_hybrid(h(h(at(s),at(np)),at(s)), lambda(P,lambda(Q,lambda(Z,appl(Q,appl(believes,appl(P,Z)))))), believes, 1, 2, Believes),
	translate_hybrid(h(at(s),h(at(s),at(np))), lambda(VP,lambda(Z,appl(appl(VP,someone),Z))), someone, 2, 3, Someone),
	translate_hybrid(h(at(s),at(np)), lambda(S,lambda(Z1,appl(S,appl(left,Z1)))), left, 3, 4, Left),
	prove([John, Believes, Someone, Left], at(s, [0,4])).

% = I need a better axiom selection strategy

% succeeds, but proof generation fails
test6 :-
	translate_displacement(at(np), [0,1], John),
	translate_displacement(dl(at(np),at(s)), [1,2], Left),
	translate_displacement(dr(dl(dl(at(np),at(s)),dl(at(np),at(s))),at(s)), [2,3], Before),
	translate_displacement(at(np), [3,4], Mary),
	translate_displacement(dl(dr(dr(>,dl(at(np),at(s)),dl(at(np),at(s))),dl(at(np),at(s))),dr(>,dl(at(np),at(s)),dl(at(np),at(s)))), [4,5], Did),
	prove([John,Left,Before,Mary,Did], at(s,[0,5])).

% fails (verify!)
test7 :-
        translate_hybrid(at(np), lambda(X,appl(john,X)), john, 0, 1, John),
	translate_hybrid(dr(dl(at(np),at(s)),at(np)), lambda(Y,appl(studies,Y)), studies, 1, 2, Studies),
        translate_hybrid(at(np), lambda(Z,appl(logic,Z)), logic, 2, 3, Logic),
	translate_hybrid(h(h(h(at(s),dr(dl(at(np),at(s)),at(np))),h(at(s),dr(dl(at(np),at(s)),at(np)))),h(at(s),dr(dl(at(np),at(s)),at(np)))),
			 lambda(STV2,lambda(STV1,lambda(TV,lambda(V,appl(appl(STV1,TV),appl(and,appl(appl(STV2,lambda(W,W)),V))))))), and, 3, 4, And),
        translate_hybrid(at(np), lambda(X1,appl(charles,X1)), charles, 4, 5, Charles),
        translate_hybrid(at(np), lambda(Z1,appl(phonetics,Z1)), phonetics, 5, 6, Phonetics),
	prove([John, Studies, Logic, And, Charles, Phonetics], at(s,[0,6])).

% = test translations

test_d1(F) :-
	/* generalized quantifier */
	translate_displacement(dl(>,dr(>,at(s),at(np)),at(s)), [1,2], F).
test_d2(F) :-
	/* did */
	translate_displacement(dl(dr(dr(>,at(vp),at(vp)),at(vp)),dr(>,at(vp),at(vp))), [4,5], F).
test_d3(F) :-
	/* himself */
	translate_displacement(dl(<,dr(<,dr(>,at(vp),at(np)),at(np)),dr(>,at(vp),at(np))), [3,4], F).

test_h1(F) :-
	translate_hybrid(h(at(s),at(np)), lambda(P,lambda(Z,appl(P,appl(walks,Z)))), walks, 1, 2, F).
test_h2(F) :-
	translate_hybrid(h(at(s),h(at(s),at(np))), lambda(P,lambda(Z,appl(appl(P,everyone),Z))), everyone, 0, 1, F).

	
