% = portray_graph(+Graph)
%
% GraphViz output

:- module(portray_graph_tikz, [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).

:- dynamic '$GRAPH_NO'/1.

graph_header :-
      ( exists_file('graph.tex') -> delete_file('graph.tex') ; true),
	open('graph.tex', write, _, [alias(graph)]),
	format(graph, '\\documentclass{article}~2n', []),
	format(graph, '\\usepackage[a3paper]{geometry}~n', []),
	format(graph, '\\usepackage{amsmath}~n', []),
	format(graph, '\\usepackage{tikz}~n', []),
	format(graph, '\\usetikzlibrary{graphs, graphdrawing}~n', []),
	format(graph, '\\usetikzlibrary{quotes}~n', []),
	format(graph, '\\usegdlibrary{layered}~2n', []),
	format(graph, '\\begin{document}~n', []),
	format(graph, '\\begin{center}~n', []),
	retractall('$GRAPH_NO'(_)),
	assert('$GRAPH_NO'(0)).

graph_footer(P) :-
	'$GRAPH_NO'(N),
	write_graphs(N),
	write_proofs(P),
	format(graph, '\\end{center}~n', []),
	format(graph, '\\end{document}~n', []),
	close(graph),
    (
	access_file('graph.tex', read)
    ->
	/* it is recommended to comment out the following line */
	/* for larger proofs, since lualatex slows down */
	/* considerably for a trace consisting of several */
        /* larger graphs */    
%	shell('lualatex graph.tex > /dev/null'),
	format('LaTeX graphs ready~n', [])
     ;
        format('LaTeX graph output failed~n', [])
     ).


write_proofs(P) :-
   (
       P =:= 0
   ->
       format(graph, 'No proofs found!~n', [])
   ;
       P =:= 1
   ->
       format(graph, '1 proof found.~n', [])
   ;
       format(graph, '~p proofs found.~n', [P])
   ).

write_graphs(N) :-
   (
       N =:= 0
   ->
       format(graph, 'No graphs output!~n', [])
   ;
       N =:= 1
   ->
       format(graph, '1 graph output.~n', [])
   ;
       format(graph, '~p graphs output.~n', [N])
   ).

latex_graph(G0) :-
	copy_term(G0, G),
 	graph_header,
 	graph_numbervars(G, 0, _),
        format(graph, '{\\tikz \\graph [multi, layered layout, level distance=1.3cm] {~n', []),
        portray_vertices(G),
        portray_edges(G),
        format(graph, '};~2n', []),
	format(graph, '\\end{center}~n', []),
	format(graph, '\\end{document}~n', []),
	told,
    (
	access_file('graph.tex', read)
    ->
	shell('lualatex graph.tex > /dev/null'),
	format('LaTeX graphs ready~n', [])
     ;
        format('LaTeX graph output failed~n', [])
     ).

portray_graph(G) :-
        '$GRAPH_NO'(N0),
	retractall('$GRAPH_NO'(_)),
	N is N0 + 1,
	assert('$GRAPH_NO'(N)),
        /* do temporary numbervars */
\+ \+ ( graph_numbervars(G, 0, _),
        format(graph, '{\\flushleft ~p\\hfill}~2n\\tikz \\graph [multi, layered layout, level distance=1.3cm] {~n', [N]),
        portray_vertices(G),
        portray_edges(G),
        format(graph, '};~2n', [])).

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
    format(graph, '~w/{$', [N]),
    portray_fvs(FVs),
    write(graph, '\\ '),
    portray_atoms(As),
    format(graph, '$};~n', []),
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
    format(graph, '~w <-["$~@$"] ~w;~n', [N,portray_var(A),P]).
portray_link(par(P,Q), N) :-
  (
    P =:= Q
  ->
    format(graph, '~w <-[bend left] ~w;~n~w <-[bend right] ~w;~n', [N,P,N,Q])
  ;
    format(graph, '~w <- ~w;~n~w <- ~w;~n', [N,P,N,Q])
  ).

portray_atoms([]) :-
    write(graph, '\\emptyset').
portray_atoms([A|As]) :-
    write(graph, '\\{'),
    portray_atoms1(As, A).

portray_atoms1([], A) :-
    portray_atom(A),
    write(graph, '\\}').
portray_atoms1([B|Bs], A) :-
    portray_atom(A),
    write(graph, ','),
    portray_atoms1(Bs, B).

portray_atom(neg(A,_,Vars)) :-
    format(graph, '\\overset{-}{~@}',[portray_atom1(Vars, A)]).
portray_atom(pos(A,_,Vars)) :-
    format(graph, '\\overset{+}{~@}',[portray_atom1(Vars, A)]).
portray_atom(neg(A,_,_,_,Vars)) :-
    format(graph, '\\overset{-}{~@}',[portray_atom1(Vars, A)]).
portray_atom(pos(A,_,_,_,Vars)) :-
    format(graph, '\\overset{+}{~@}',[portray_atom1(Vars, A)]).

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
    write(graph, Atom).
portray_atom1([V|Vs], Pred) :-
    format(graph, '~w(~@)', [Pred,portray_vars(Vs,V)]).
    
portray_vars([], V) :-
    portray_var1(V).
portray_vars([V|Vs], W) :-
    portray_var1(W),
    write(graph, ','),
    portray_vars(Vs, V).

portray_var1(Int) :-
    integer(Int),
    !,
    print(graph, Int).
portray_var1(var(N)) :-
    portray_var(N).
portray_var1('$VAR'(N)) :-
    print(graph, '$VAR'(N)).

portray_var(N) :-
    VN is N mod 5,
    VI is N//5,
    print_var1(VI),
    format(graph, '_{~w}', [VN]).

print_var1(0) :-
    write(graph, x).
print_var1(1) :-
    write(graph, y).
print_var1(2) :-
    write(graph, z).
print_var1(3) :-
    write(graph, v).
print_var1(4) :-
    write(graph, w).

