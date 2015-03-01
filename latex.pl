:- module(latex, [latex_proof/1,proof_header/0,proof_footer/0]).

proof_header :-
	format('\\documentclass{article}~2n', []),
	format('\\usepackage[a3paper]{geometry}~n', []),
	format('\\usepackage{proof}~n', []),
	format('\\usepackage{amssymb}~2n', []),
	format('\\begin{document}~n', []).

proof_footer :-
	format('\\end{document}~n', []),
	told,
    (
	access_file('latex_proofs.tex', read)
    ->
	shell('pdflatex latex_proofs.tex > /dev/null'),
	format('LaTeX ready~n', [])
     ;
        format('LaTeX output failed~n', [])
     ).


latex_proof(Proof) :-
	latex_proof(Proof, 0).

latex_proof(rule(Name, Ant, Suc, SubProofs), Tab0) :-
	format('\\infer[~@]{~@}{', [latex_rule_name(Name),latex_sequent(Ant,Suc)]),
	Tab is Tab0 + 6,
	latex_proofs(SubProofs, Tab),
%	nl,
%	tab(Tab0),
        format('}~n', []).


latex_proofs([], _Tab).
latex_proofs([P|Ps], Tab) :-
	nl,
	tab(Tab),
	latex_proofs1(Ps, P, Tab).

latex_proofs1([], P, Tab) :-
	tab(Tab),
	latex_proof(P).
latex_proofs1([P|Ps], Q, Tab) :-
	latex_proof(Q),
	tab(Tab),
	format('&~n', []),
	latex_proofs1(Ps, P, Tab).


latex_rule_name(ax) :-
	write('Axiom').
latex_rule_name(fl) :-
	write('L\\forall').
latex_rule_name(fr) :-
	write('R\\forall').
latex_rule_name(el) :-
	write('L\\exists').
latex_rule_name(er) :-
	write('R\\exists').
latex_rule_name(il) :-
	write('L\\multimap').
latex_rule_name(ir) :-
	write('R\\multimap').
latex_rule_name(pl) :-
	write('L\\otimes').
latex_rule_name(pr) :-
	write('R\\otimes').

latex_sequent(Ant, Suc) :-
	format('~@ \\vdash ~@', [latex_antecedent(Ant),latex_formula(Suc)]).

latex_antecedent([]).
latex_antecedent([A|As]) :-
	latex_antecedent(As, A).

latex_antecedent([], A) :-
	latex_formula(A).
latex_antecedent([A|As], B) :-
	latex_formula(B),
	write(','),
	latex_antecedent(As, A).

latex_formula(F) :-
	latex_formula(F, 0).

latex_formula(_-F, N) :-
	latex_formula(F, N).
latex_formula(at(F,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(Term).
latex_formula(at(F,_,_,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(Term).
latex_formula(forall(X,F), _) :-
	!,
	update_var(X, Y),
   (
	is_quantified(F)
   ->
	format('\\forall ~w. ~@', [Y,latex_formula(F, 1)])
   ;
	format('\\forall ~w. [~@]', [Y,latex_formula(F, 0)])
   ).
latex_formula(exists(X,F), _) :-
	!,
	update_var(X, Y),
   (
	is_quantified(F)
   ->
	format('\\exists ~w. ~@', [Y,latex_formula(F, 1)])
   ;
	format('\\exists ~w. [~@]', [Y,latex_formula(F, 0)])
   ).
latex_formula(p(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format('~@ \\otimes ~@', [latex_formula(A, 1),latex_formula(B, 1)])
   ;
	format('(~@ \\otimes ~@)', [latex_formula(A, 1),latex_formula(B, 1)])
   ).
latex_formula(impl(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format('~@ \\multimap ~@', [latex_formula(A, 1),latex_formula(B, 0)])
   ;
	format('(~@ \\multimap ~@)', [latex_formula(A, 1),latex_formula(B, 1)])
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
