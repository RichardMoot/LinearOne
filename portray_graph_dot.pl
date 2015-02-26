% = portray_graph(+Graph)
%
% GraphViz output

:- module(portray_graph_tikz, [portray_graph/1,header/1,footer/1]).

header.
footer.

portray_graph([]).
portray_graph([vertex(N,As,FVs,Ps)|Rest]) :-
    format('~w [shape="record" label="{ ', [N]),
    portray_fvs(FVs),
    format('| ', []),
    portray_atoms(As),
    format('}"];~n', []),
    portray_links(Ps, N),
    portray_graph(Rest).

portray_links([], _).
portray_links([P|Ps], N) :-
    portray_link(P, N),
    portray_links(Ps, N).

portray_link(univ(A,P), N) :-
    format('~w -> ~w [label="~p"];~n', [N,P,'$VAR'(A)]).
portray_link(par(P,Q), N) :-
    format('~w -> ~w;~n~w -> ~w;~n', [N,P,N,Q]).

portray_atoms([]).
portray_atoms([A|As]) :-
    portray_atom(A),
    portray_atoms(As).

portray_atom(neg(A,_,_)) :-
    format('-~w ', [A]).
portray_atom(pos(A,_,_)) :-
    format('+~w ', [A]).


portray_fvs([]).
portray_fvs([V|Vs]) :-
  (
      var(V)
   ->
      true
   ;
      V = var(N)
   ->
      format('~p ', ['$VAR'(N)])
   ;
      true
  ),
  portray_fvs(Vs).
