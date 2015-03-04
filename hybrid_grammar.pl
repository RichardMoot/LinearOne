

test(1) :-
	lookup([john,studies,logic,and,charles,phonetics], Formulas, LexSem, s, Goal),
	prove(Formulas, Goal, LexSem).

lex(john, np, lambda(X,appl(john,X)), j).
lex(studies, tv, lambda(Y,appl(studies,Y)), s).
lex(logic, np, lambda(Z,appl(logic,Z)), l).
lex(and, (((s|tv)|(s|tv))|(s|tv)), lambda(STV2,lambda(STV1,lambda(TV,lambda(V,appl(appl(STV1,TV),appl(and,appl(appl(STV2,lambda(W,W)),V))))))), lambda(S2,lambda(S1,lambda(T,bool(appl(S1,T),&,appl(S2,T)))))).
lex(charles, np, lambda(X1,appl(charles,X1)), c).
lex(phonetics, np, lambda(Z1,appl(phonetics,Z1)), p).

