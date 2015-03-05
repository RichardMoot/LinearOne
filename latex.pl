:- module(latex, [latex_proof/1,proof_header/0,proof_footer/0,latex_semantics/1]).

proof_header :-
	open('latex_proofs.tex', write, _Stream, [alias(latex)]),
	format(latex, '\\documentclass{article}~2n', []),
	format(latex, '\\usepackage[a2paper]{geometry}~n', []),
	format(latex, '\\usepackage{proof}~n', []),
	format(latex, '\\usepackage{amssymb}~2n', []),
	format(latex, '\\begin{document}~2n', []).

proof_footer :-
	format(latex, '~n\\end{document}~n', []),
	close(latex),
    (
	access_file('latex_proofs.tex', read)
    ->
	shell('pdflatex latex_proofs.tex > /dev/null'),
	format('LaTeX proofs ready~n', [])
     ;
        format('LaTeX proof output failed~n', [])
     ).


latex_proof(Proof0) :-
	copy_term(Proof0, Proof),
	numbervars(Proof, 0, _),
	latex_proof(Proof, 0),
        format(latex, '~n\\bigskip~n', []).

latex_proof(_-Proof, Tab) :-
        latex_proof(Proof, Tab).
latex_proof(rule(Name, Ant, Suc, SubProofs), Tab0) :-
	format(latex, '\\infer[~@]{~@}{', [latex_rule_name(Name),latex_sequent(Ant,Suc)]),
	Tab is Tab0 + 6,
	latex_proofs(SubProofs, Tab),
	(SubProofs = [] -> true ; tab(latex,Tab0)),
        format(latex, '}~n', []).


latex_proofs([], _Tab).
latex_proofs([P|Ps], Tab) :-
	/* newline and tab only when there is at least one premiss */
	nl(latex),
	tab(latex, Tab),
	latex_proofs1(Ps, P, Tab).

latex_proofs1([], P, Tab) :-
	latex_proof(P, Tab).
latex_proofs1([P|Ps], Q, Tab) :-
	latex_proof(Q, Tab),
	tab(latex, Tab),
	format(latex, '&~n', []),
	tab(latex, Tab),
	latex_proofs1(Ps, P, Tab).


%latex_rule_name(ax) :-
%	write('Axiom').
latex_rule_name(ax).
latex_rule_name(cut) :-
	write(latex, 'Cut').
latex_rule_name(fl) :-
	write(latex, 'L\\forall').
latex_rule_name(fr) :-
	write(latex, 'R\\forall').
latex_rule_name(el) :-
	write(latex, 'L\\exists').
latex_rule_name(er) :-
	write(latex, 'R\\exists').
latex_rule_name(il) :-
	write(latex, 'L\\multimap').
latex_rule_name(ir) :-
	write(latex, 'R\\multimap').
latex_rule_name(pl) :-
	write(latex, 'L\\otimes').
latex_rule_name(pr) :-
	write(latex, 'R\\otimes').

latex_sequent(Ant, Suc) :-
	format(latex, '~@ \\vdash ~@', [latex_antecedent(Ant),latex_formula(Suc)]).

latex_antecedent([]).
latex_antecedent([A|As]) :-
	latex_antecedent(As, A).

latex_antecedent([], A) :-
	latex_formula(A).
latex_antecedent([A|As], B) :-
	latex_formula(B),
	write(latex, ','),
	latex_antecedent(As, A).

latex_formula(F) :-
	latex_formula(F, 0).

latex_formula(_-F, N) :-
	latex_formula(F, N).
latex_formula(at(F,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(latex, Term).
latex_formula(at(F,_,_,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(latex, Term).
latex_formula(forall(X,F), _) :-
	!,
	update_var(X, Y),
   (
	is_quantified(F)
   ->
	format(latex, '\\forall ~w. ~@', [Y,latex_formula(F, 1)])
   ;
	format(latex, '\\forall ~w. [~@]', [Y,latex_formula(F, 0)])
   ).
latex_formula(exists(X,F), _) :-
	!,
	update_var(X, Y),
   (
	is_quantified(F)
   ->
	format(latex, '\\exists ~w. ~@', [Y,latex_formula(F, 1)])
   ;
	format(latex, '\\exists ~w. [~@]', [Y,latex_formula(F, 0)])
   ).
latex_formula(p(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\otimes ~@', [latex_formula(A, 1),latex_formula(B, 1)])
   ;
	format(latex, '(~@ \\otimes ~@)', [latex_formula(A, 1),latex_formula(B, 1)])
   ).
latex_formula(impl(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\multimap ~@', [latex_formula(A, 1),latex_formula(B, 0)])
   ;
	format(latex, '(~@ \\multimap ~@)', [latex_formula(A, 1),latex_formula(B, 1)])
   ).

is_quantified(_-F) :-
	is_quantified(F).
is_quantified(exists(_,_)).
is_quantified(forall(_,_)).
is_quantified(at(_,_)).
is_quantified(at(_,_,_,_)).

update_vars([], []).
update_vars([V|Vs], [W|Ws]) :-
	update_var(V, W),
	update_vars(Vs, Ws).

update_var(V, W) :-
    (
         V = var(M)
    ->
         variable_atom(M, W)
    ;
         V = W
    ).	


variable_atom(N, At) :-
	VN is N mod 5,
	VI is N//5,
	print_var1(VI, V),
	atomic_list_concat([V, '_{', VN, '}'], At).
    
print_var1(0, x).
print_var1(1, y).
print_var1(2, z).
print_var1(3, v).
print_var1(4, w).

latex_semantics(Sem) :-
	format(latex, '~2n$$~n', []),	
	latex_semantics(Sem, 0),
	format(latex, '~n$$~2n', []).

latex_semantics(A, _) :-
	atomic(A),
	!,
	format(latex, '\\textrm{~w}', [A]).
latex_semantics('$VAR'(N), _) :-
	!,
	variable_atom(N, At),
	write(latex, At).
latex_semantics(lambda(X,M), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '\\lambda ~@. ~@', [latex_semantics(X, 1), latex_semantics(M, 1)])
   ;
	format(latex, '(\\lambda ~@. ~@)', [latex_semantics(X, 1), latex_semantics(M, 1)])
   ).
latex_semantics(appl(N,M), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@\\, ~@', [latex_semantics(N, 1), latex_semantics(M, 1)])
   ;
	format(latex, '(~@\\, ~@)', [latex_semantics(N, 1), latex_semantics(M, 1)])
   ).
latex_semantics(pair(N,M), _NB) :-
	!,
	format(latex, '\\langle~@,~@\\rangle', [latex_semantics(N, 0), latex_semantics(M, 0)]).
latex_semantics(pi1(N), _NB) :-
	!,
	format(latex, '\\pi_1(~@)', [latex_semantics(N, 0)]).
latex_semantics(pi2(N), _NB) :-
	!,
	format(latex, '\\pi_2(~@)', [latex_semantics(N, 0)]).
latex_semantics(quant(Q,X,F), _NB) :-
	format(latex, '~@~@.[~@]', [latex_quantifier(Q), latex_semantics(X, 0), latex_semantics(F, 0)]).
latex_semantics(bool(P,B,Q), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ ~@ ~@', [latex_semantics(P, 1), latex_bool(B), latex_semantics(Q, 1)])
   ;
	format(latex, '(~@ ~@ ~@)', [latex_semantics(P, 1), latex_bool(B), latex_semantics(Q, 1)])
   ).

latex_bool(&) :-
	write(latex, '\\wedge').
latex_bool(\/) :-
	write(latex, '\\vee').

latex_quantifier(forall) :-
	write(latex, '\\forall').
latex_quantifier(exists) :-
	write(latex, '\\exists').

