% = portray_graph(+Graph)
%
% GraphViz output

:- module(portray_graph_tikz, [portray_graph/1,graph_header/0,graph_footer/1]).

:- dynamic '$GRAPH_NO'/1.

graph_header :-
        shell('rm graph.tex', _),
        tell('graph.tex'),
	format('\\documentclass{article}~2n', []),
	format('\\usepackage[a3paper]{geometry}~n', []),
	format('\\usepackage{amsmath}~n', []),
	format('\\usepackage{tikz}~n', []),
	format('\\usetikzlibrary{graphs, graphdrawing}~n', []),
	format('\\usetikzlibrary{quotes}~n', []),
	format('\\usegdlibrary{layered}~2n', []),
	format('\\begin{document}~n', []),
	format('\\begin{center}~n', []),
	retractall('$GRAPH_NO'(_)),
	assert('$GRAPH_NO'(0)).

graph_footer(P) :-
	'$GRAPH_NO'(N),
	write_graphs(N),
	write_proofs(P),
	format('\\end{center}~n', []),
	format('\\end{document}~n', []),
	told,
    (
	access_file('graph.tex', read)
    ->
	shell('lualatex graph.tex > /dev/null'),
	format('LaTeX graphs ready~n', [])
     ;
        format('LaTeX graph output failed~n', [])
     ).


write_proofs(P) :-
   (
       P =:= 0
   ->
       format('No proofs found!~n', [])
   ;
       P =:= 1
   ->
       format('1 proof found.~n', [])
   ;
       format('~p proofs found.~n', [P])
   ).

write_graphs(N) :-
   (
       N =:= 0
   ->
       format('No graphs output!~n', [])
   ;
       N =:= 1
   ->
       format('1 graph output.~n', [])
   ;
       format('~p graphs output.~n', [N])
   ).


portray_graph(G) :-
       '$GRAPH_NO'(N0),
       retractall('$GRAPH_NO'(_)),
       N is N0 + 1,
       assert('$GRAPH_NO'(N)),
      /* do temporary numbervars */
\+ \+ (graph_numbervars(G, 0, _),
       format('{\\flushleft ~p\\hfill}~2n\\tikz \\graph [multi, layered layout, level distance=1.3cm] {~n', [N]),
       portray_vertices(G),
       portray_edges(G),
       format('};~2n', [])).

graph_numbervars([], N, N).
graph_numbervars([vertex(_,As,_,_)|Rest], N0, N) :-
    atoms_numbervars(As, N0, N1),
    graph_numbervars(Rest, N1, N).

atoms_numbervars([], N, N).
atoms_numbervars([A|As], N0, N) :-
    atom_numbervars(A, N0, N1),
    atoms_numbervars(As, N1, N).

atom_numbervars(neg(_, _, Vars), N0, N) :-
    numbervars(Vars, N0, N).
atom_numbervars(pos(_, _, Vars), N0, N) :-
    numbervars(Vars, N0, N).
atom_numbervars(neg(_, _, _, _, Vars), N0, N) :-
    numbervars(Vars, N0, N).
atom_numbervars(pos(_, _, _, _, Vars), N0, N) :-
    numbervars(Vars, N0, N).

portray_vertices([]).
portray_vertices([vertex(N,As,FVs,_Ps)|Rest]) :-
    format('~w/{$', [N]),
    portray_fvs(FVs),
    write('\\ '),
    portray_atoms(As),
    format('$};~n', []),
    portray_vertices(Rest).

portray_edges([]).
portray_edges([vertex(N,_As,_FVs,Ps)|Rest]) :-
    portray_links(Ps, N),
    portray_edges(Rest).


portray_links([], _).
portray_links([P|Ps], N) :-
    portray_link(P, N),
    portray_links(Ps, N).

portray_link(univ(A,P), N) :-
    format('~w <-["$~@$"] ~w;~n', [N,portray_var(A),P]).
portray_link(par(P,Q), N) :-
  (
    P =:= Q
  ->
    format('~w <-[bend left] ~w;~n~w <-[bend right] ~w;~n', [N,P,N,Q])
  ;
    format('~w <- ~w;~n~w <- ~w;~n', [N,P,N,Q])
  ).

portray_atoms([]) :-
    write('\\emptyset').
portray_atoms([A|As]) :-
    write('\\{'),
    portray_atoms1(As, A).

portray_atoms1([], A) :-
    portray_atom(A),
    write('\\}').
portray_atoms1([B|Bs], A) :-
    portray_atom(A),
    write(','),
    portray_atoms1(Bs, B).

portray_atom(neg(A,_,Vars)) :-
    format('\\overset{-}{~@}',[portray_atom1(Vars, A)]).
portray_atom(pos(A,_,Vars)) :-
    format('\\overset{+}{~@}',[portray_atom1(Vars, A)]).
portray_atom(neg(A,_,_,_,Vars)) :-
    format('\\overset{-}{~@}',[portray_atom1(Vars, A)]).
portray_atom(pos(A,_,_,_,Vars)) :-
    format('\\overset{+}{~@}',[portray_atom1(Vars, A)]).

portray_fvs([]).
portray_fvs([V|Vs]) :-
  (
      var(V)
   ->
      true
   ;
      V = var(N)
   ->
      portray_var(N)
   ;
      true
  ),
  portray_fvs(Vs).

portray_atom1([], Atom) :-
    write(Atom).
portray_atom1([V|Vs], Pred) :-
    format('~w(~@)', [Pred,portray_vars(Vs,V)]).
    
portray_vars([], V) :-
    portray_var1(V).
portray_vars([V|Vs], W) :-
    portray_var1(W),
    write(','),
    portray_vars(Vs, V).

portray_var1(Int) :-
    integer(Int),
    !,
    print(Int).
portray_var1(var(N)) :-
    portray_var(N).
portray_var1('$VAR'(N)) :-
    print('$VAR'(N)).

portray_var(N) :-
    VN is N mod 5,
    VI is N//5,
    print_var1(VI),
    format('_{~w}', [VN]).

print_var1(0) :-
    write(x).
print_var1(1) :-
    write(y).
print_var1(2) :-
    write(z).
print_var1(3) :-
    write(v).
print_var1(4) :-
    write(w).

